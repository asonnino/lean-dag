import LeanDag.Quantitative

/-!
# View convergence, and reference coverage derived from it

The layer beneath `Timing`. `Timing.covers` is the only field of that
structure which is not purely one thing: its own comment concedes that it
says *"a `T`-block built at time `t` is in every `T`-validator's hands by
`t + delay`; **and** a validator references everything it holds."* Two
clauses, one network and one protocol, fused into a single hypothesis
that concludes about `refs`. That fusion is convenient — it is what makes
`synchronisedOn_of_timing` short — but it puts a protocol clause inside
the row of the trust boundary reserved for the network.

This file separates them, and in the direction that the original design
notes asked for: state the network assumption as **view convergence** —
*after GST, whatever one correct validator holds reaches every correct
validator within `delay`* — keep referencing as the protocol clause P7 it
is, and derive `covers`, hence all of `Timing`, hence reference coverage.

```
view convergence + P7 (references) + P9 (waits, drift)
        ──▶  Timing.covers  ──▶  SynchronisedOn  ──L4/L6──▶  commits
```

**What this settles.** Reference coverage *is* derivable from view
convergence — the objection that a validator might build before a
straggler's block lands is answered not by strengthening the network but
by the waiting rule, which is already a clause of the protocol. What view
convergence cannot do *alone* is win that race: `holds_mono` and
`converges` place the block in the builder's hands at time
`built w n + delay`, and only `waits` (through the drift bound) puts that
moment before `built v (n+1)`. So the two premises are co-equal partners,
not a network assumption with an afterthought.

`ViewSync.toTiming` is the reduction, after which every result of
`Timing.lean` applies unchanged: drift is still derived from `prompt`,
the backoff still terminates, and the quantitative bounds of §6.10 are
unaffected.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {N : ℕ}

/-- `Timing` with its one impure field replaced by the two clauses it
conflates: a view-level network guarantee (`converges`) and the protocol's
referencing rule (`references`).

Everything else is `Timing`'s, unchanged, because the derivation of
reference coverage needs the same waiting and drift machinery either way —
the point of the separation is *where the premises come from*, not how
many there are. -/
structure ViewSync (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) where
  /-- `v`'s round-`n` block, when it was built, and the timing parameters —
  as in `Timing`. -/
  blk : Validator → ℕ → BlockId
  built : Validator → ℕ → ℕ
  timeout : ℕ → ℕ
  gst : ℕ
  delay : ℕ
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  blk_mem : ∀ v ∈ T, ∀ n ≤ N, blk v n ∈ U.ids
  blk_creator : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).creator = v
  blk_round : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).round = n
  /-- **P9, the waiting rule** (protocol). -/
  waits : ∀ v ∈ T, ∀ n < N, built v n + timeout n ≤ built v (n + 1)
  timeout_pos : ∀ n, 1 ≤ timeout n
  latest : ℕ → ℕ
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  latest_mem : ∀ n ≤ N, ∃ w ∈ T, latest n ≤ built w n
  /-- **P9, the promptness rule** (protocol). -/
  prompt : ∀ v ∈ T, ∀ n < N,
    built v (n + 1) ≤ max (built v n + timeout n) (latest n + delay)
  /-- What `v` holds at *time* `t` — the temporal index a `View` cannot
  supply (§13.1). This is the object the original design notes wanted the
  synchrony assumption stated over. -/
  holds : Validator → ℕ → Finset BlockId
  /-- A validator holds its own block from the moment it builds it. -/
  holds_own : ∀ v ∈ T, ∀ n ≤ N, blk v n ∈ holds v (built v n)
  /-- Holdings only grow: nothing is forgotten. -/
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  /-- **N2, as view convergence** (network). After GST, whatever a correct
  validator holds at time `t` is held by every correct validator by
  `t + delay`. No mention of blocks, rounds or references: this is a
  statement about views, and it is the whole of what is assumed of the
  network here. -/
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  /-- **P7, referencing** (protocol). A validator references every block of
  the round below that it holds when it builds. This is `Delivery.includes`
  in the timed setting, and it is a clause an implementation executes —
  not something the network provides. -/
  references : ∀ v ∈ T, ∀ n < N, ∀ a ∈ holds v (built v (n + 1)),
    (U.block a).round = n → a ∈ (U.block (blk v (n + 1))).refs

namespace ViewSync

variable (vs : ViewSync U T N)

/-- **The derivation.** `Timing.covers` — a `T`-block built after GST and
early enough is referenced — follows from view convergence and the
referencing clause, with no counting and no drift: the block is in its
author's hands when built (`holds_own`), reaches the builder within
`delay` (`converges`), is still there when the builder acts
(`holds_mono`, which is where the hypothesis
`built w n + delay ≤ built v (n+1)` is spent), and is therefore
referenced (`references`).

The hypothesis discharged here is exactly the race of §13.1: view
convergence delivers the block relative to when it was *sent*, and only
the waiting rule places that moment before the builder acts. -/
theorem covers_of_converges :
    ∀ v ∈ T, ∀ w ∈ T, ∀ n < N, vs.gst ≤ vs.built w n →
      vs.built w n + vs.delay ≤ vs.built v (n + 1) →
      vs.blk w n ∈ (U.block (vs.blk v (n + 1))).refs := by
  intro v hv w hw n hn hgst hearly
  refine vs.references v hv n hn _ ?_ (vs.blk_round w hw n (by omega))
  refine vs.holds_mono v _ _ hearly ?_
  exact vs.converges v hv w hw _ hgst (vs.holds_own w hw n (by omega))

/-- **The reduction.** A `ViewSync` *is* a `Timing`, so every result of
`Timing.lean` applies to it unchanged — `driftFrom_of_prompt`,
`synchronisedOn_of_timing`, `exists_synchronisedOn_of_backoff`, and the
quantitative results built on them. The two formulations of the network
assumption are therefore not siblings but a hierarchy: view convergence
is the weaker, more primitive statement, and `covers` is what it becomes
once the protocol's referencing clause is applied. -/
def toTiming : Timing U T N where
  blk := vs.blk
  built := vs.built
  timeout := vs.timeout
  gst := vs.gst
  delay := vs.delay
  rounds_le := vs.rounds_le
  blk_mem := vs.blk_mem
  blk_creator := vs.blk_creator
  blk_round := vs.blk_round
  waits := vs.waits
  timeout_pos := vs.timeout_pos
  covers := vs.covers_of_converges
  latest := vs.latest
  built_le_latest := vs.built_le_latest
  latest_mem := vs.latest_mem
  prompt := vs.prompt

@[simp] theorem toTiming_built : vs.toTiming.built = vs.built := rfl
@[simp] theorem toTiming_gst : vs.toTiming.gst = vs.gst := rfl
@[simp] theorem toTiming_delay : vs.toTiming.delay = vs.delay := rfl
@[simp] theorem toTiming_timeout : vs.toTiming.timeout = vs.timeout := rfl

/-- Drift, stated directly over a `ViewSync`. -/
abbrev DriftFrom (n₀ D : ℕ) : Prop := vs.toTiming.DriftFrom n₀ D

/-- **Reference coverage from view convergence.** The statement the design
notes originally asked for, now a theorem: after GST, with validators
waiting long enough that the timeout clears drift plus the delivery
bound, every correct block references every correct block of the round
below.

The premises divide exactly along the trust boundary — `converges` is the
network's, `references` and `waits` are the protocol's — and no clause of
the one stands in for the other. -/
theorem synchronisedOn_of_converges (hT : T ⊆ (Correct : Finset Validator))
    {R D : ℕ} (hD : vs.DriftFrom R D) (hgst : vs.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vs.delay ≤ vs.timeout n) :
    SynchronisedOn U T R :=
  Timing.synchronisedOn_of_timing (tm := vs.toTiming) hT hD hgst hbackoff

/-- **And with an unbounded backoff, from some round on** — the `ViewSync`
form of L7b's headline, with drift derived rather than assumed. -/
theorem exists_synchronisedOn_of_converges
    (hT : T ⊆ (Correct : Finset Validator))
    (hmono : Monotone vs.timeout) (hub : ∀ m, ∃ n, m ≤ vs.timeout n)
    {n₀ D : ℕ} (hdel : ∀ n, n₀ ≤ n → vs.delay ≤ vs.timeout n)
    (hbase : ∀ v ∈ T, ∀ w ∈ T, vs.built w n₀ ≤ vs.built v n₀ + D) :
    ∃ R, SynchronisedOn U T R :=
  exists_synchronisedOn_of_backoff vs.toTiming hT hmono hub hdel hbase

/-! ## Liveness on this foundation

What the whole liveness development needs, once it is grounded here.

The striking point is what is **absent**: no `Delivery`, no `Live`, and no
`DeliversQuorum` (N1). Block production is not derived from N1 and P8 in
this setting — it is carried by the structure itself, since `blk` asserts
a block per `T`-validator per round below the horizon, which is exactly
`PopulatedOn`. So on this foundation the entire liveness account rests on

* **view convergence** — the network's whole contribution;
* **`references`** (P7) and **`waits`/`prompt`** (P9) — protocol;
* **`blk`** — the production clause P8 plays, here as data;
* **a fair schedule** (P10) — for the recurrence results;

and nothing else. N1 remains necessary only for the *untimed* route, where
production must be derived rather than assumed (§4.3). -/

section Liveness

variable [S : Slots Validator] {k : ℕ}

/-- **Production.** The structure asserts a block per `T`-validator per
round, so rounds are populated with no appeal to N1 or L1. -/
theorem populatedOn (vs : ViewSync U T N) {n : ℕ} (hn : n ≤ N) :
    PopulatedOn U T n :=
  vs.toTiming.populatedOn hn

/-- **L4 on this foundation.** A `T`-led slot past GST is committed, given
only view convergence, the referencing rule, and a wait exceeding the
start spread plus the delivery bound. -/
theorem decided_of_leader_of_converges (vs : ViewSync U T N)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card) {D₀ : ℕ}
    (hstart : ∀ v ∈ T, ∀ w ∈ T, vs.built w 0 ≤ vs.built v 0 + D₀)
    (hwait : ∀ n, D₀ + vs.delay ≤ vs.timeout n)
    (hgst : vs.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_wait vs.toTiming hT hcard hstart hwait hgst hN hlead

/-- **L6 on this foundation.** Commits recur: for every slot there is a
later one, past any given bound on GST, which any sufficiently grown
view-convergent execution commits.

The quantifier order is L6's and carries the same content (§6.6): the
committing slot is fixed by the schedule and the GST bound alone, before
any execution is named. -/
theorem commits_recur_of_converges (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (fair : FairScheduleOn T) (G k : ℕ) :
    ∃ k', k ≤ k' ∧ G ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N D₀ : ℕ)
        (vs : ViewSync U T N), vs.gst ≤ G →
        (∀ v ∈ T, ∀ w ∈ T, vs.built w 0 ≤ vs.built v 0 + D₀) →
        (∀ n, D₀ + vs.delay ≤ vs.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded G
  obtain ⟨k', hk', hlead⟩ := fair (max k k₀)
  have hG : G ≤ S.slotRound k' :=
    le_trans hk₀ (S.mono (le_trans (le_max_right k k₀) hk'))
  refine ⟨k', le_trans (le_max_left _ _) hk', hG, ?_⟩
  intro U N D₀ vs hgst hstart hwait hN
  exact decided_of_leader_of_converges vs hT hcard hstart hwait
    (le_trans hgst hG) hN hlead

/-- **L10 on this foundation.** Every slot below a committed run is
decided, so the ledger does not stall — again with no `Delivery` and no
N1 anywhere in the hypotheses. -/
theorem all_decided_below_of_converges {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hspan : SpansEligible (Validator := Validator) c)
    (fair : FairRunOn T c) (G k : ℕ) :
    ∃ b, k ≤ b ∧ G ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N D₀ : ℕ)
        (vs : ViewSync U T N), vs.gst ≤ G →
        (∀ v ∈ T, ∀ w ∈ T, vs.built w 0 ≤ vs.built v 0 + D₀) →
        (∀ n, D₀ + vs.delay ≤ vs.timeout n) →
        S.slotRound (b + c - 1) + 2 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded G
  obtain ⟨b, hb, hrunT⟩ := fair (max k k₀)
  have hG : G ≤ S.slotRound b :=
    le_trans hk₀ (S.mono (le_trans (le_max_right k k₀) hb))
  refine ⟨b, le_trans (le_max_left _ _) hb, hG, ?_⟩
  intro U N D₀ vs hgst hstart hwait hN
  have hrun : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B, Decided U (View.full U) j (some B) := by
    intro j hj1 hj2
    have hlead : S.leader j ∈ T := by
      have := hrunT (j - b) (by omega)
      rwa [Nat.add_sub_cancel' hj1] at this
    have hjr : S.slotRound j ≤ S.slotRound (b + c - 1) := S.mono hj2
    obtain ⟨L, -, hdec⟩ := decided_of_leader_of_converges vs hT hcard hstart hwait
      (le_trans hgst (le_trans hG (S.mono hj1))) (by omega) hlead
    exact ⟨L, hdec⟩
  exact decided_below_of_committed_run (by omega) (fun i hi => hspan b i hi) hrun

end Liveness

end ViewSync

end LeanDag
