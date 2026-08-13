import LeanDag.ViewPace

/-!
# The reactive schedule

The timed schedules of `Timing` and `ViewSync` direct a validator to wait
a **full timeout** in every round (`waits`), which makes latency a
multiple of the timeout however fast the network happens to be. A
*reactive* validator waits only as long as it must: at the round above a
leader it builds as soon as it holds the leader's block and enough
references, falling back to the timeout only if the leader does not
arrive; and a validator that voted builds its next block as soon as it
can certify, again with the timeout only as a fallback.

`ReactiveCore` is the schedule and network layer both reactive protocols
share, together with the first reactive stage — the leader wait. Two
clauses replace `waits`:

* `deadline` — a validator never waits *past* the timeout. The uniform
  floor is gone; only `built_lt` (time advances) bounds builds from
  below.
* `vote_or_wait` — at the round above a reliable leader, a block either
  references the leader (the reactive exit), or its builder waited the
  full timeout and would have referenced the leader had it held it (the
  fallback). Building early *without* the leader is thereby excluded,
  which is the whole discipline: the schedule accelerates only where
  acceleration cannot cost the vote.

The clause is stated only for slots whose leader lies in `T`. For a
Byzantine leader nothing useful can be said — it may equivocate, and
`ValidWrt.distinct_creators` forbids referencing two of its blocks — and
no liveness statement concerns such slots.

For the fast path, `prompt_vote` bounds the reactive exit from above: once
a validator past its round entry holds the leader *and* every reliable
round-`r` block, it builds within the processing bound `proc`. The
latency and no-timeout theorems (`built_succ_le_of_fast`,
`no_timeout_of_fast`) quantify the resulting speed: rounds advance at the
pace of actual propagation, and if delivery is faster than the timeout
the timeout never fires.

Everything here consumes the DAG layer read-only; the commit rules are
untouched, and each protocol's file derives its own `DirectCommit` from
the votes this stage guarantees.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {D N R : ℕ} {k : ℕ} {L : BlockId}

/-- The reactive schedule and network layer, shared by both protocols.

Relative to `ViewSync`: `waits` and `prompt` are replaced by `deadline`,
`built_lt`, `vote_or_wait` and `prompt_vote`, and the referencing clause
is carried inside `vote_or_wait`'s fallback rather than stated globally —
a reactive builder deliberately does *not* reference everything it holds. -/
structure ReactiveCore (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) where
  /-- `v`'s round-`n` block. -/
  blk : Validator → ℕ → BlockId
  /-- The time at which `v` built it. -/
  built : Validator → ℕ → ℕ
  /-- The fallback timeout in force at round `n`. -/
  timeout : ℕ → ℕ
  /-- The processing bound: how long a reactive exit may lag its trigger. -/
  proc : ℕ
  gst : ℕ
  delay : ℕ
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  blk_mem : ∀ v ∈ T, ∀ n ≤ N, blk v n ∈ U.ids
  blk_creator : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).creator = v
  blk_round : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).round = n
  /-- Time advances with rounds — the only lower bound a reactive
  schedule keeps. -/
  built_lt : ∀ v ∈ T, ∀ n, built v n < built v (n + 1)
  /-- **The reactive ceiling.** A validator never waits past the
  timeout; it may build any time before it. -/
  deadline : ∀ v ∈ T, ∀ n < N, built v (n + 1) ≤ built v n + timeout n
  /-- What `v` holds at time `t`. -/
  holds : Validator → ℕ → Finset BlockId
  holds_own : ∀ v ∈ T, ∀ n ≤ N, blk v n ∈ holds v (built v n)
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  /-- **N2, as view convergence** (network) — as in `ViewPace`. -/
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  /-- **The leader wait.** At the round above a reliable leader, either
  the block votes (the reactive exit), or its builder waited the full
  timeout and votes for any leader block it holds (the fallback). -/
  vote_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 1 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    L ∈ (U.block (blk v (S.slotRound k + 1))).refs ∨
      (built v (S.slotRound k) + timeout (S.slotRound k)
          ≤ built v (S.slotRound k + 1) ∧
        (L ∈ holds v (built v (S.slotRound k + 1)) →
          L ∈ (U.block (blk v (S.slotRound k + 1))).refs))
  /-- **The reactive exit is prompt.** Once a validator past its round
  entry holds the leader and every reliable round-`r` block, it builds
  within `proc`. Consumed only by the fast-path results. -/
  prompt_vote : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 1 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L → ∀ t, built v (S.slotRound k) ≤ t →
    L ∈ holds v t → (∀ u ∈ T, blk u (S.slotRound k) ∈ holds v t) →
    built v (S.slotRound k + 1) ≤ t + proc

namespace ReactiveCore

variable (rc : ReactiveCore U T N)

omit [DecidableEq BlockId] in
/-- Rounds advance real time. -/
theorem le_built {v : Validator} (hv : v ∈ T) (n : ℕ) : n ≤ rc.built v n := by
  induction n with
  | zero => omega
  | succ n ih => have := rc.built_lt v hv n; omega

omit [DecidableEq BlockId] in
/-- The reliable leader's block of slot `k` is the one the schedule
names: non-equivocation identifies any leader block with `blk`. -/
theorem leader_blk_eq (hT : T ⊆ (Correct : Finset Validator))
    (hN : S.slotRound k ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) : L = rc.blk (S.leader k) (S.slotRound k) :=
  U.eq_of_creator_eq hL.1 (rc.blk_mem _ hlead _ hN) (hT hlead) hL.2.2
    (rc.blk_creator _ hlead _ hN) (by rw [hL.2.1, rc.blk_round _ hlead _ hN])

/-- **Every reliable validator votes.** Past GST, with the timeout
clearing drift plus the delivery bound, every `T`-block at the round
above a reliable leader references the leader's block — whether by the
reactive exit or by the fallback.

The fallback case is the only argument: the leader holds its own block
when it builds, convergence carries it across within `delay`, drift and
the full timeout place that arrival before the waiter's build, and the
fallback clause then obliges the vote. The reactive exit needs nothing:
it *is* the vote. -/
theorem votes (hT : T ⊆ (Correct : Finset Validator))
    (hD : DriftOn rc.built T R D N) (hgst : rc.gst ≤ R)
    (hto : ∀ n, R ≤ n → D + rc.delay ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    ∀ v ∈ T, L ∈ (U.block (rc.blk v (S.slotRound k + 1))).refs := by
  intro v hv
  rcases rc.vote_or_wait v hv k hN hlead L hL with hvote | ⟨hwait, hheld⟩
  · exact hvote
  · refine hheld ?_
    -- the leader's own copy, carried across by convergence
    have hLeq := rc.leader_blk_eq hT (by omega) hlead hL
    have hown := rc.holds_own _ hlead (S.slotRound k) (by omega)
    have hgstL : rc.gst ≤ rc.built (S.leader k) (S.slotRound k) :=
      le_trans (le_trans hgst hR) (rc.le_built hlead _)
    have hconv := rc.converges v hv _ hlead _ hgstL hown
    rw [← hLeq] at hconv
    refine rc.holds_mono v _ _ ?_ hconv
    have hdrift := hD v hv _ hlead (S.slotRound k) hR (by omega)
    have := hto (S.slotRound k) hR
    omega

end ReactiveCore

/-! ## The fast path

The theorems above use only the fallback. These two use only the exit:
when delivery outpaces the timeout, latency tracks delivery, and the
timeout never fires. `δ` is the *actual* per-block propagation bound of
the execution — a premise about this run, not an assumption about the
network in general — and the conclusions degrade continuously as it
approaches the timeout. -/

namespace ReactiveCore

variable (rc : ReactiveCore U T N)

omit [DecidableEq BlockId] in
/-- **Latency tracks delivery.** If every reliable round-`r` block —
the leader's among them — reaches every reliable validator within `δ`
of its build, then the round above is built within `D + δ + proc` of
round entry: drift to the last builder, `δ` to arrive, `proc` to build.
The timeout does not appear. -/
theorem built_succ_le_of_fast {δ : ℕ}
    (hδ : ∀ u ∈ T, ∀ v ∈ T,
      rc.blk u (S.slotRound k) ∈ rc.holds v (rc.built u (S.slotRound k) + δ))
    (hD : ∀ u ∈ T, ∀ v ∈ T,
      rc.built u (S.slotRound k) ≤ rc.built v (S.slotRound k) + D)
    (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) (hT : T ⊆ (Correct : Finset Validator)) :
    ∀ v ∈ T, rc.built v (S.slotRound k + 1)
      ≤ rc.built v (S.slotRound k) + D + δ + rc.proc := by
  intro v hv
  have hLeq := rc.leader_blk_eq hT (by omega) hlead hL
  refine rc.prompt_vote v hv k hN hlead L hL
    (rc.built v (S.slotRound k) + D + δ) (by omega) ?_ ?_
  · rw [hLeq]
    refine rc.holds_mono v _ _ ?_ (hδ _ hlead v hv)
    have := hD _ hlead v hv
    omega
  · intro u hu
    refine rc.holds_mono v _ _ ?_ (hδ u hu v hv)
    have := hD u hu v hv
    omega

omit [DecidableEq BlockId] in
/-- **The timeout never fires.** When delivery, drift and processing
together undercut the timeout, every reliable validator builds strictly
before its deadline — the fallback branch of `vote_or_wait` is never
taken, and consensus proceeds at network speed. -/
theorem no_timeout_of_fast {δ : ℕ}
    (hδ : ∀ u ∈ T, ∀ v ∈ T,
      rc.blk u (S.slotRound k) ∈ rc.holds v (rc.built u (S.slotRound k) + δ))
    (hD : ∀ u ∈ T, ∀ v ∈ T,
      rc.built u (S.slotRound k) ≤ rc.built v (S.slotRound k) + D)
    (hN : S.slotRound k + 1 ≤ N) (hlead : S.leader k ∈ T)
    (hL : IsLeaderBlock U k L) (hT : T ⊆ (Correct : Finset Validator))
    (hfast : D + δ + rc.proc < rc.timeout (S.slotRound k)) :
    ∀ v ∈ T, rc.built v (S.slotRound k + 1)
      < rc.built v (S.slotRound k) + rc.timeout (S.slotRound k) := by
  intro v hv
  have := rc.built_succ_le_of_fast hδ hD hN hlead hL hT v hv
  omega

end ReactiveCore

end LeanDag
