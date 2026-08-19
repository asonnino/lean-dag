import LeanDag.Reactive.Basic

/-!
# Reactive Mysticeti

The three-round rule, run reactively. The vote stage is `ReactivePace`'s;
this file adds the certificate stage — a validator that voted waits at
round `r + 2` only until it can certify, with the timeout as the fallback
(`cert_or_wait`) — and derives the direct commit.

The commit rule itself is untouched: `DirectCommit`, `Certifies`,
`Decided` and the whole safety development are consumed as found. What
changes is only where the liveness hypotheses come from. The reference
coverage of the main line (`SynchronisedOn`) is deliberately *not*
available here — a reactive builder omits whatever had not arrived when
its exit condition was met — and it is not needed: the exit conditions
are chosen so that exactly the references the commit rule counts are
present, early exit and fallback alike.

`reactive_decided` is the liveness statement, mirroring the shape of
`decided_of_leader_mem`: a reliable-led slot past GST is committed, with
the population hypotheses supplied by the trunk's derived production
(`PaceCore.populatedOn`) and the coverage hypothesis replaced by the two
reactive wait clauses.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {N R : ℕ} {k : ℕ} {L : BlockId}

/-- The reactive three-round schedule: `ReactivePace`'s vote stage,
plus the certificate wait, stated over any `T`-authored block. -/
structure ReactiveM (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends ReactivePace U T N where
  /-- **The certificate wait.** At two rounds above a reliable leader,
  any `T`-authored block either already certifies (the reactive exit —
  its references carry a quorum of votes), or its builder waited the
  full timeout and references every reliable vote it holds (the
  fallback). -/
  cert_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 2 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 2 →
    Certifies U c L ∨
      (built v (S.slotRound k + 1) + timeout (S.slotRound k + 1)
          ≤ built v (S.slotRound k + 2) ∧
        ∀ b ∈ U.ids, (U.block b).creator ∈ T →
          (U.block b).round = S.slotRound k + 1 →
          b ∈ holds v (built v (S.slotRound k + 2)) →
          L ∈ (U.block b).refs → b ∈ (U.block c).refs)

namespace ReactiveM

variable (rm : ReactiveM U T N)

/-- **Every reliable certificate block certifies.** In the reactive exit
the block certifies by construction. In the fallback, every reliable vote
has arrived — each voter holds its own vote when it builds, convergence
carries it across, and drift plus the full timeout place the arrival
before the fallback build — so the block references all of `T`'s votes,
and `T` is a quorum of distinct authors.

The vote blocks themselves come from the trunk's derived production
(`PaceCore.populatedOn`): nothing here assumes a block exists. -/
theorem certifies (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    CertifiesAt U T (S.slotRound k) L := by
  have hD := rm.driftOn_of_catchup hcard hgst
  intro v hv c hc hcc hcr
  rcases rm.cert_or_wait v hv k hN hlead L hL c hc hcc hcr with hcert | ⟨hwait, hincl⟩
  · exact hcert
  · -- the fallback block references every reliable vote; count them
    have hvotes := rm.toReactivePace.votes hT hcard hgst hto hR (by omega) hlead hL
    -- each `u ∈ T` has a vote block, by derived production
    have hpop := rm.toPaceCore.populatedOn hcard (S.slotRound k + 1) (by omega)
    refine le_trans hcard (Finset.card_le_card ?_)
    intro u hu
    obtain ⟨b, hb, hbc, hbr⟩ := hpop u hu
    have hvote : L ∈ (U.block b).refs := hvotes u hu b hb hbc hbr
    have harrive : b ∈ rm.holds v (rm.built v (S.slotRound k + 2)) := by
      have hown := rm.holds_own u hu (S.slotRound k + 1) (by omega) b hb hbc hbr
      have htopu : S.slotRound k + 1 ≤ rm.top u := by
        have := rm.le_top_of_built u hu b hb hbc
        omega
      have hgstu : rm.gst ≤ rm.built u (S.slotRound k + 1) :=
        le_trans (le_trans hgst (by omega)) (rm.le_built hu _ htopu)
      have hconv := rm.converges v hv u hu _ hgstu hown
      refine rm.holds_mono v _ _ ?_ hconv
      have hdrift := hD v hv u hu (S.slotRound k + 1) (by omega) (by omega)
      have := hto (S.slotRound k + 1) (by omega)
      omega
    refine mem_creatorsOf.mpr ⟨b, ?_, hbc⟩
    exact Finset.mem_filter.mpr ⟨hincl b hb (hbc ▸ hu) hbr harrive hvote, hvote⟩

/-- **The reactive direct commit** — the shared counting theorem
(`directCommit_of_certifiesAt`) fed by the reactive certificate
supplier, with the certificate blocks from derived production. One
application; the argument lives in `Liveness.lean`, once. -/
theorem directCommit (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    DirectCommit U L (S.slotRound k) :=
  directCommit_of_certifiesAt hcard
    (rm.toPaceCore.populatedOn hcard (S.slotRound k + 2) (by omega))
    (rm.certifies hT hcard hgst hto hR hN hlead hL)

/-- **Reactive liveness (Mysticeti).** A reliable-led slot past GST is
committed by every view — the conclusion of `decided_of_leader_mem`,
with reference coverage replaced by the two reactive wait clauses and
the leader block supplied by derived production. -/
theorem decided (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLmem, hLc, hLr⟩ :=
    rm.toPaceCore.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  exact ⟨L, hL, Decided.directCommit hL
    (directCommitIn_full (rm.directCommit hT hcard hgst hto hR hN hlead hL))⟩

/-- **Reactive liveness is local too** (V18, reactive). Every reliable
validator decides the slot on its own view, by the same explicit time as the
timed discipline. The trunk supplies the argument
(`decided_local_of_certifiesAt`); the reactive side supplies only its
certificate stage, exactly as for the global statement. Reference coverage
appears nowhere. -/
theorem decided_local (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ ∀ v ∈ T,
      Decided U (rm.viewAt v (rm.latest (S.slotRound k + 2) + rm.delay)) k (some L) := by
  obtain ⟨L, hLmem, hLc, hLr⟩ :=
    rm.toPaceCore.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  have hg : ∀ u ∈ T, rm.gst ≤ rm.built u (S.slotRound k + 2) := by
    intro u hu
    have htop := rm.toPaceCore.reached hcard (S.slotRound k + 2) hN u hu
    have := rm.le_built hu (S.slotRound k + 2) htop
    omega
  exact ⟨L, hL, rm.toPaceCore.decided_local_of_certifiesAt hcard hN hg hL
    (rm.certifies hT hcard hgst hto hR hN hlead hL)⟩

/-! ## Inclusion without coverage: the rotation backbone

The reference coverage of the main line is what chain quality's
inclusion results (report §7) run on, and the reactive discipline
deliberately does without it: an early exit omits whatever had not
arrived, so a straggler's block may be referenced by nobody at the round
above — `SynchronisedOn` is false, and the per-round backbone of CQ5
with it.

Inclusion survives anyway, by a different route. A correct author's
blocks form a single chain under the self-parent clause
(`reaches_self_ancestor`), so a straggler's block lies below every later
block of its *own author* — and when that author leads a slot, which
per-validator fairness guarantees (`FairToEach`), the reactive vote
discipline commits the leader block, and the whole chain enters the
common cone at once.

So the reactive system trades the inclusion latency, not the guarantee:
where full coverage puts a correct round-`m` block in *every* correct
cone one round later, the reactive discipline puts it in the *agreed
ledger* one leadership rotation later. Commit latency at network speed,
inclusion latency at rotation speed — and both halves of that sentence
are theorems. -/

/-- **RS5 — reactive inclusion.** For every round `m` and author
`u ∈ T`, the schedule fixes a `u`-led slot above `m` before any
execution is named, and every sufficiently grown reactive execution
commits that slot with a leader block whose cone contains `u`'s
round-`m` block — which is therefore in the agreed ledger of any verdict
assignment covering the slot.

No coverage appears: the hypotheses are the reactive wait clauses, GST
and the backoff, exactly as in `ReactiveM.decided`. What is added is
only `FairToEach` — the schedule must return to `u` itself — and the
self-parent chain does the rest. -/
theorem committed_of_correct_block
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairToEach (S := S) T) {u : Validator} (hu : u ∈ T) (R m : ℕ)
    (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧ S.leader k' = u ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ)
        (rm : ReactiveM U T N),
        rm.gst ≤ R →
        (∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∀ b ∈ U.ids, (U.block b).creator = u → (U.block b).round = m →
          ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) ∧
            Reaches U L b ∧
            ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
              b ∈ ledgerSet U g n := by
  -- the schedule fixes the slot: `u`-led, past round `m`
  obtain ⟨k', hk', hlead⟩ := fair u hu (slotAt Validator (m + 1))
  have hm : m < S.slotRound k' := by
    have h1 := le_slotRound_slotAt (Validator := Validator) (m + 1)
    have h2 := S.mono hk'
    omega
  refine ⟨k', hm, by omega, hlead, ?_⟩
  intro U N rm hgst hto hN b hb hbc hbr
  -- the reactive commit at `u`'s slot
  obtain ⟨L, hL, hdec⟩ :=
    rm.decided hT hcard hgst hto (by omega) hN (hlead ▸ hu)
  -- the leader block is `u`-authored above `m`: the self-parent chain
  -- carries it down to `b`
  have hreach : Reaches U L b :=
    reaches_self_ancestor (hT hu) hL.1 hb
      (by rw [hL.2.2, hlead]) hbc (by rw [hL.2.1, hbr]; omega)
  exact ⟨L, hL, hdec, hreach,
    fun g n hg hn => ⟨k', hn, L, hg, hreach⟩⟩

/-! ### The same result, execution first

`committed_of_correct_block` fixes the slot *before* any execution is named:
the schedule alone decides where `u`'s block will be picked up, and the
statement then quantifies over every reactive execution reaching that far.
That order is the strong reading, and it is why the theorem's conclusion
carries a universally quantified execution inside an existential.

The reader's order is the other one --- take an execution, ask what happens
to a block. That is the corollary below: it says of a *given* run what the
theorem says of all of them, and it is what the paper states. -/

/-- **No reliable validator's block is censored** (RS5, execution first). In
a reactive run past GST whose timeout clears `2Δ + proc`, every block a
reliable validator authors is reached by a later commit --- at a slot the
validator leads itself --- and so enters the agreed ledger.

The slot is still the schedule's choice, so the horizon condition remains: the
run must reach two rounds past it. Everything else is fixed before the
statement begins. -/
theorem committed_of_correct_block_of_run
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairToEach (S := S) T) (rm : ReactiveM U T N) {R m : ℕ}
    (hgst : rm.gst ≤ R) (hto : ∀ n, R ≤ n → 2 * rm.delay + rm.proc ≤ rm.timeout n)
    {u : Validator} (hu : u ∈ T) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ S.leader k' = u ∧
      (S.slotRound k' + 2 ≤ N →
        ∀ b ∈ U.ids, (U.block b).creator = u → (U.block b).round = m →
          ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) ∧
            Reaches U L b ∧
            ∀ (g : ℕ → Option BlockId) (n : ℕ), g k' = some L → k' < n →
              b ∈ ledgerSet U g n) := by
  obtain ⟨k', hm, hR, hlead, hrest⟩ :=
    committed_of_correct_block (BlockId := BlockId) (Payload := Payload)
      hT hcard fair hu R m hRm
  exact ⟨k', hm, hlead, fun hN => hrest U N rm hgst hto hN⟩

end ReactiveM

end LeanDag
