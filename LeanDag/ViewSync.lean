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
  supply (report §18.1). This is the object the original design notes wanted the
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
`built w n + delay ≤ built v (n+1)` is consumed), and is therefore
referenced (`references`).

The hypothesis discharged here is exactly the race of report §18.1: view
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

/-- **Build-time views agree, from `R` on.** Every `T`-authored round-`n`
block is in *every* `T`-validator's holdings at the moment it builds for
round `n+1` — the index-aligned statement, derived rather than assumed.

This is the timed model's version of `ViewsConverge`, and the proof shows
what that untimed condition is really carrying. Convergence alone places
the block in the builder's hands at `built w n + delay`; making that
moment precede `built v (n+1)` needs the *bound* (to compare with a
timeout at all), the *drift* (to compare `w`'s clock with `v`'s), and the
*wait* (to push `v`'s build past both). An unbounded lag `d` cannot enter
that chain: there is nothing to compare it with, and no timeout can be
chosen to clear it. -/
theorem blk_mem_holds (_hT : T ⊆ (Correct : Finset Validator))
    {R D : ℕ} (hD : vs.toTiming.DriftFrom R D) (hgst : vs.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vs.delay ≤ vs.timeout n)
    {v : Validator} (hv : v ∈ T) {w : Validator} (hw : w ∈ T)
    {n : ℕ} (hRn : R ≤ n) (hn : n < N) :
    vs.blk w n ∈ vs.holds v (vs.built v (n + 1)) := by
  have hown := vs.holds_own w hw n (by omega)
  have hgstw : vs.gst ≤ vs.built w n :=
    le_trans (le_trans hgst hRn) (vs.toTiming.le_built hw n (by omega))
  have hconv := vs.converges v hv w hw _ hgstw hown
  refine vs.holds_mono v _ _ ?_ hconv
  have hdrift := hD v hv w hw n hRn (by omega)
  have hwait := vs.waits v hv n hn
  have hto := hbackoff n hRn
  simp only [toTiming_built] at hdrift
  omega

/-- The untimed condition's shape, stated over the timed structure:
from `R` on, every `T`-validator's build-time view contains every
`T`-authored block of the round it is building over. This is what
`ViewsConverge` asserts outright in the untimed model. -/
def ViewsAgree (R : ℕ) : Prop :=
  ∀ v ∈ T, ∀ u ∈ T, ∀ n, R ≤ n → n < N →
    vs.blk u n ∈ vs.holds v (vs.built v (n + 1))

/-- **The bridge, with the protocol clause made explicit.**

In the untimed model the two halves cannot be separated, and the reason
is structural rather than a matter of taste: `Delivery.held v n` is
indexed by the *round*, and `held_spec` confines it to round-`n` blocks,
so a round-`n` block can only ever appear at index `n`. There is
therefore no way to say "it arrived, but after `v` had already built" —
the model has no room to place the arrival event on either side of the
build event. Delivery and waiting are literally indistinguishable there,
which is why `ViewsConverge` must assume their conjunction.

Separating them needs exactly one thing: an ordering of the two events,
which is to say a clock. With one, the split is clean and this theorem
is the bridge —

* `converges` is the **network's** half (bounded, from `gst`);
* `waits` with the drift and backoff conditions is the **protocol's**;

and together they yield what the untimed model has to postulate. -/
theorem viewsAgree_of_converges (hT : T ⊆ (Correct : Finset Validator))
    {R D : ℕ} (hD : vs.toTiming.DriftFrom R D) (hgst : vs.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vs.delay ≤ vs.timeout n) :
    vs.ViewsAgree R :=
  fun _ hv _ hu _ hRn hn => vs.blk_mem_holds hT hD hgst hbackoff hv hu hRn hn


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

The quantifier order is L6's and carries the same content (report §6.6): the
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

/-! ## Factoring the bound

`converges` is partial synchrony in its usual two-part shape, and the
parts can be separated. Qualitatively, holdings converge at all —
whatever one correct validator holds, every correct validator holds
*some time later*, with no claim about when. Quantitatively, from `gst`
on that lag is uniformly at most `delay`.

`convergesWithin_iff_bounded` is the factoring: under monotone holdings,
convergence-with-a-bound is exactly eventual convergence whose lag is
uniformly bounded after `gst`. So

> **view convergence under synchrony  =  view convergence  +  a bound on
> the lag.**

The bound is not decoration. Eventual convergence alone cannot yield
reference coverage, for the reason `covers_of_converges` makes visible:
the block must be in the builder's hands *before it builds*, and the only
way to arrange that is to choose a timeout exceeding the lag. A lag that
merely exists cannot be compared with a timeout; a lag bounded by `delay`
can, and `D + delay ≤ timeout n` is where the comparison happens. This is
also why the bound is asserted only from `gst`: before it there is
nothing for a timeout to clear, which is precisely the content of partial
synchrony. -/

section Factoring

variable {holds : Validator → ℕ → Finset BlockId} {gst bound : ℕ}

/-- **The qualitative half.** Holdings converge: whatever `w` holds at `t`,
`v` holds at some later time. No bound and no GST. -/
def ConvergesEventually (holds : Validator → ℕ → Finset BlockId)
    (T : Finset Validator) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ t, ∃ d, holds w t ⊆ holds v (t + d)

/-- **The quantitative half.** From `gst` on, that lag is at most `bound` —
and uniformly so, in the validators and in the time. This is exactly the
`converges` field of `ViewSync`. -/
def ConvergesWithin (holds : Validator → ℕ → Finset BlockId)
    (T : Finset Validator) (gst bound : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + bound)

/-- The `converges` field *is* the bounded form — the definition is the
field, unfolded. -/
theorem ViewSync.convergesWithin (vs : ViewSync U T N) :
    ConvergesWithin vs.holds T vs.gst vs.delay := vs.converges

/-- A bounded lag is a lag: the timed form implies the untimed one, even
before `gst`, since holdings only grow. -/
theorem convergesEventually_of_within
    (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t)
    (h : ConvergesWithin holds T gst bound) :
    ConvergesEventually holds T := by
  intro v hv w hw t
  refine ⟨(gst - t) + bound, ?_⟩
  refine le_trans (hmono w t (max t gst) (le_max_left _ _)) ?_
  refine le_trans (h v hv w hw (max t gst) (le_max_right _ _)) ?_
  exact hmono v _ _ (by omega)

/-- And conversely: eventual convergence whose lag is uniformly bounded
after `gst` *is* convergence within that bound. The two together are
`converges`, and neither half alone is. -/
theorem convergesWithin_of_bounded
    (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t)
    (h : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t →
      ∃ d ≤ bound, holds w t ⊆ holds v (t + d)) :
    ConvergesWithin holds T gst bound := by
  intro v hv w hw t ht
  obtain ⟨d, hd, hsub⟩ := h v hv w hw t ht
  exact le_trans hsub (hmono v _ _ (by omega))

/-- **The factoring.** Under monotone holdings, convergence within a bound
and bounded eventual convergence are the same condition. -/
theorem convergesWithin_iff_bounded
    (hmono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t) :
    ConvergesWithin holds T gst bound ↔
      (∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t →
        ∃ d ≤ bound, holds w t ⊆ holds v (t + d)) :=
  ⟨fun h v hv w hw t ht => ⟨bound, le_refl _, h v hv w hw t ht⟩,
   convergesWithin_of_bounded hmono⟩

/-- Every `ViewSync` converges in the qualitative sense too — the bound is
extra information, not a different phenomenon. -/
theorem ViewSync.convergesEventually (vs : ViewSync U T N) :
    ConvergesEventually vs.holds T :=
  convergesEventually_of_within vs.holds_mono vs.converges

end Factoring

/-! ## The untimed variant

`ViewSync.converges` still mentions a clock: `holds w t ⊆ holds v (t + delay)`
is a statement about wall-clock instants, and `delay` is Δ. The obvious
question is whether the same shape can be had *without* a bound —
"whatever a correct validator holds, every correct validator eventually
holds" — and whether that could stand in for N1.

It can, and the definition is below; but the form it must take is
forced, and worth understanding before use.

**Why "eventually, at some later index" cannot work.** Building a
round-`(n+1)` block requires round-`n` blocks *at that build*. In an
untimed model the only measure of progress is the round index itself —
and the round index advances only when blocks are produced, which is the
very thing production is trying to establish. So an assumption which
delivers round-`n` blocks at some index `m > n` cannot drive production:
every validator may sit waiting, nothing is produced, no index advances,
and the "eventually" never arrives. The circle is real, and N1 breaks it
by being *conditional on existence* rather than on progress.

**So the untimed form must be index-aligned**, and once it is, there is
no clock left in it: `held v n` means "what `v` had in hand when it built
for round `n+1`", *whenever that was*. That is where the "eventually"
lives — not in a bound, but in the fact that the index is logical rather
than temporal. A validator that waits arbitrarily long still builds at
index `n`.

**The price.** Index-aligned sharing of correct blocks is *stronger* than
N1: N1 promises a quorum and only when one exists, whereas this promises
every correct block, always. In exchange the two network assumptions
become the same shape — both are now "views converge", one with a bound
and one without — and N1 disappears from the liveness development
entirely (`populated_of_viewsConverge`). Whether that trade is worth
making is a modelling judgement, not a theorem; §4.3 keeps N1 because its
conditional quorum form is the weaker hypothesis and the implementable
one. -/

section Untimed

variable {D : Delivery U}

/-- **Untimed view convergence.** What a correct validator holds when it
builds for round `n` is held by every correct validator when *it* builds
for round `n` — no clock, no Δ, no GST.

Restricted to correct-authored blocks, deliberately: a Byzantine author
may send to some correct validators and not others, and no network
assumption should forbid that (report §4.3). -/
def ViewsConverge (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ w ∈ (Correct : Finset Validator),
    ∀ n, ∀ b ∈ D.held v n,
      (U.block b).creator ∈ (Correct : Finset Validator) → b ∈ D.held w n

/-- A correct validator has its own block in hand when it builds the next
one. The untimed counterpart of `ViewSync.holds_own`, and the clause that
turns *existence* of a block into somebody *holding* it. -/
def HoldsOwn (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n → b ∈ D.held v n

/-- Untimed view convergence is `EventuallyDelivers` from round `0`: the
author holds its own block, and convergence hands it to everyone else at
the same index. -/
theorem eventuallyDelivers_of_viewsConverge (hvc : ViewsConverge D)
    (hown : HoldsOwn D) : EventuallyDelivers D 0 := by
  intro n _ v hv a ha har hac
  exact hvc _ hac _ hv n a (hown _ hac n a ha rfl har) hac

/-- **L1 without N1.** Under untimed view convergence, every round below
the horizon is populated — the conclusion `no_stall` draws from
`DeliversQuorum`, drawn instead from a view-shaped assumption.

The induction is the same, with the quorum obtained differently: rather
than assuming a quorum is delivered whenever one exists, the previous
round's population supplies `|Correct| ≥ n − f` correct blocks, and
convergence puts every one of them in every correct validator's hands. -/
theorem populated_of_viewsConverge {N : ℕ} (H : Live U D N)
    (hvc : ViewsConverge D) (hown : HoldsOwn D) :
    ∀ r ≤ N, Populated U r := by
  have hED := eventuallyDelivers_of_viewsConverge hvc hown
  intro r
  induction r with
  | zero => intro _; exact H.genesis
  | succ r ih =>
      intro hr v hv
      refine H.builds r (by omega) v hv ?_
      refine le_trans card_correct (Finset.card_le_card ?_)
      intro w hw
      obtain ⟨a, ha, hac, har⟩ := ih (by omega) w hw
      refine mem_creatorsOf.mpr ⟨a, ?_, hac⟩
      exact D.accepts_correct v hv r a
        (hED r (Nat.zero_le r) v hv a ha har (by rw [hac]; exact hw))
        (by rw [hac]; exact hw)

end Untimed

/-! ## Production, derived rather than assumed

The two routes above appear to treat block production differently. The
untimed one *derives* it (`populated_of_viewsConverge`), from the build
rule P8 and convergence. The timed one appears to *assume* it: `blk` is a
total function giving every `T`-validator a block at every round below the
horizon, and `populatedOn` merely reads it off.

The difference is one of presentation. `blk_mem`, `blk_creator` and
`blk_round` say exactly that every `v ∈ T` has a round-`n` block, which is
`PopulatedOn U T n`; and conversely a choice function extracted from
`PopulatedOn` satisfies the three fields, the choice being canonical
because non-equivocation (T1) makes a correct validator's round-`n` block
unique. `exists_blk_of_populatedOn` is that direction. So `blk` is
`PopulatedOn`, Skolemised.

`ViewGrowth` is then `ViewSync` with `blk` removed and the build rule put
in its place, and `toViewSync` derives what was previously assumed. Two
fields have to be generalised for this to be possible, and they are
exactly the two stated over `blk`:

* `holds_own` becomes a statement about any block a validator authored,
  not about `blk v n`;
* `references` becomes a statement about any block a validator authors at
  round `n+1`, not about `blk v (n+1)`.

Both generalisations are what one would state anyway — non-equivocation
makes the block in question unique — and with them the circularity is
gone: neither clause mentions the function being constructed.

**What remains asymmetric, and should.** `converges` says nothing below
`gst`, so production is derivable only from a round `R` at or after the
GST crossing, whereas `ViewsConverge` is unconditional and drives
production from round 0. `ViewGrowth` therefore carries a `base` covering
rounds up to `R`. The residue is not a defect of the development but the
content of partial synchrony: before GST the network may deliver nothing
and no round need be populated. The two routes run the same induction and
differ only in where it starts — `R = 0` untimed, `R` past GST timed.
-/

section Production

variable {R D : ℕ}

/-- Drift over a build schedule alone. `Timing.DriftFrom` is this
predicate at `tm.built`, which is all that definition mentions; naming it
separately lets the production argument state the hypothesis before any
`Timing` exists — and none can exist until `blk` is available. -/
def DriftOn (built : Validator → ℕ → ℕ) (T : Finset Validator)
    (R D N : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, R ≤ n → n ≤ N → built w n ≤ built v n + D

theorem Timing.driftFrom_iff_driftOn (tm : Timing U T N) :
    tm.DriftFrom R D ↔ DriftOn tm.built T R D N := Iff.rfl

omit [DecidableEq BlockId] in
/-- Rounds advance real time — `Timing.le_built`'s argument over a
schedule alone, for the same reason. -/
theorem le_built_of_waits {built : Validator → ℕ → ℕ} {timeout : ℕ → ℕ}
    (waits : ∀ v ∈ T, ∀ n < N, built v n + timeout n ≤ built v (n + 1))
    (timeout_pos : ∀ n, 1 ≤ timeout n) {v : Validator} (hv : v ∈ T) :
    ∀ n ≤ N, n ≤ built v n := by
  intro n
  induction n with
  | zero => intro _; omega
  | succ n ih =>
      intro hn
      have hw := waits v hv n (by omega)
      have := timeout_pos n
      have := ih (by omega)
      omega

omit [DecidableEq BlockId] in
/-- **`blk` is `PopulatedOn`, Skolemised.** A population of every round
below the horizon yields a function naming one block per validator per
round, satisfying the three `blk` fields of `Timing` and `ViewSync`.

The converse is those fields read directly, so the timed structure's
production clause and the untimed route's conclusion are the same
proposition in two presentations. Non-equivocation is not needed for this
direction — any choice will do — but it is what makes the choice
canonical, and `synchronisedOn_of_timing` relies on that when it
identifies an arbitrary `T`-authored block with the one `blk` names. -/
theorem exists_blk_of_populatedOn [Nonempty BlockId]
    (hpop : ∀ n ≤ N, PopulatedOn U T n) :
    ∃ blk : Validator → ℕ → BlockId,
      (∀ v ∈ T, ∀ n ≤ N, blk v n ∈ U.ids) ∧
      (∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).creator = v) ∧
      (∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).round = n) := by
  classical
  have h : ∀ p : Validator × ℕ, ∃ b : BlockId, p.1 ∈ T → p.2 ≤ N →
      b ∈ U.ids ∧ (U.block b).creator = p.1 ∧ (U.block b).round = p.2 := by
    rintro ⟨v, n⟩
    by_cases hv : v ∈ T
    · by_cases hn : n ≤ N
      · obtain ⟨b, hb, hbc, hbr⟩ := hpop n hn v hv
        exact ⟨b, fun _ _ => ⟨hb, hbc, hbr⟩⟩
      · exact ⟨Classical.arbitrary BlockId, fun _ h => absurd h hn⟩
    · exact ⟨Classical.arbitrary BlockId, fun h => absurd h hv⟩
  obtain ⟨f, hf⟩ := Classical.skolem.mp h
  exact ⟨fun v n => f (v, n),
    fun v hv n hn => (hf (v, n) hv hn).1,
    fun v hv n hn => (hf (v, n) hv hn).2.1,
    fun v hv n hn => (hf (v, n) hv hn).2.2⟩

/-- `ViewSync` with production removed and the build rule put in its
place: the same network and protocol data, but the DAG's growth is a
consequence rather than a hypothesis.

Everything except `blk` is `ViewSync`'s, with `holds_own` and
`references` generalised off `blk` as described above, plus the two
clauses the induction needs: a `base` populating the rounds up to `R`,
and `builds`, the timed counterpart of `Live.builds`. -/
structure ViewGrowth (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (R N : ℕ) where
  built : Validator → ℕ → ℕ
  timeout : ℕ → ℕ
  gst : ℕ
  delay : ℕ
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  /-- **P9, the waiting rule** (protocol), at every round rather than only
  below the horizon. `N` bounds the DAG, not the clock: a schedule does
  not stop honouring its timeouts at round `N`, and the extra round is
  what lets the induced delivery below reach the topmost blocks. -/
  waits : ∀ v ∈ T, ∀ n, built v n + timeout n ≤ built v (n + 1)
  timeout_pos : ∀ n, 1 ≤ timeout n
  latest : ℕ → ℕ
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  latest_mem : ∀ n ≤ N, ∃ w ∈ T, latest n ≤ built w n
  /-- **P9, the promptness rule** (protocol). -/
  prompt : ∀ v ∈ T, ∀ n < N,
    built v (n + 1) ≤ max (built v n + timeout n) (latest n + delay)
  holds : Validator → ℕ → Finset BlockId
  /-- Holdings are real blocks. `ViewSync` can leave this implicit because
  `blk_mem` supplies it where it is needed; the induced delivery below
  states it over arbitrary held ids, so it must be assumed. -/
  holds_sub : ∀ v t, holds v t ⊆ U.ids
  /-- A validator holds every block it authored, from the time it builds
  at that round. `ViewSync.holds_own` is this at `blk v n`. -/
  holds_own : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n → b ∈ holds v (built v n)
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  /-- **N2, as view convergence** (network). -/
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  /-- **P7, referencing** (protocol), over any block the validator authors
  at that round. `ViewSync.references` is this at `blk v (n+1)`. -/
  references : ∀ v ∈ T, ∀ n < N, ∀ c ∈ U.ids,
    (U.block c).creator = v → (U.block c).round = n + 1 →
    ∀ a ∈ holds v (built v (n + 1)), (U.block a).round = n →
    a ∈ (U.block c).refs
  /-- The seed: **one** populated round at the GST crossing. The
  induction below steps from `n` to `n+1` using only the previous round,
  so nothing is assumed about the rounds beneath `R` — which is the most
  that can be claimed, since `converges` is silent below `gst` and the
  network may deliver nothing there. The untimed route's counterpart is
  `Live.genesis`, at `R = 0`. -/
  base : PopulatedOn U T R
  /-- **P8, the build rule** (protocol). A validator holding a quorum of
  distinct authors at round `n`, among what it has in hand when it builds
  for round `n+1`, produces a block there. This is `Live.builds` with
  `D.accepted v n` replaced by the round-`n` part of the build-time
  view. -/
  builds : ∀ v ∈ T, ∀ n, R ≤ n → n < N →
    (Fintype.card Validator - F.f) ≤
      (creatorsOf U.block
        ((holds v (built v (n + 1))).filter fun b => (U.block b).round = n)).card →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n + 1

namespace ViewGrowth

variable (vg : ViewGrowth U T R N)

/-- **Production, derived.** From the seed round on, every round below the
horizon is populated — the timed counterpart of
`populated_of_viewsConverge`, and the same induction.

The step is the argument of `blk_mem_holds` run in the other direction:
rather than moving a block that `blk` asserts exists, it moves the blocks
the induction hypothesis provides. Each `w ∈ T` authored a round-`n`
block, holds it at `built w n` (`holds_own`), which is past GST since
rounds advance time; convergence puts it in `v`'s hands by
`built w n + delay`, and drift, the wait and the backoff put that before
`built v (n+1)`. So `v`'s build-time view contains a round-`n` block from
every member of `T` — a quorum of distinct authors — and `builds`
applies.

The conclusion starts at `R` rather than at `0`, and the hypothesis is a
single round rather than every round beneath `R`, because the step
consumes only its predecessor. Below `R` nothing is derivable and nothing
is assumed: `converges` is silent before `gst`, and its unbounded
companion `ConvergesEventually`, though it does hold there, cannot
substitute — a lag that merely exists cannot be ordered against a build
time, which is the comparison `hbackoff` performs. What lets the untimed
route begin at round `0` is not the absence of a GST but the index
alignment of `ViewsConverge`, which supplies that ordering by fiat. -/
theorem populatedOn (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn vg.built T R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n) :
    ∀ n, R ≤ n → n ≤ N → PopulatedOn U T n := by
  have key : ∀ k, R + k ≤ N → PopulatedOn U T (R + k) := by
    intro k
    induction k with
    | zero => intro _; exact vg.base
    | succ k ih =>
        intro hn
        have hpop := ih (by omega)
        have hRn : R ≤ R + k := by omega
        intro v hv
        refine vg.builds v hv (R + k) hRn (by omega)
          (le_trans hcard (Finset.card_le_card ?_))
        intro w hw
        obtain ⟨b, hb, hbc, hbr⟩ := hpop w hw
        refine mem_creatorsOf.mpr ⟨b, Finset.mem_filter.mpr ⟨?_, hbr⟩, hbc⟩
        have hown := vg.holds_own w hw (R + k) (by omega) b hb hbc hbr
        have hle := le_built_of_waits (N := N) (fun v hv n _ => vg.waits v hv n) vg.timeout_pos hw (R + k) (by omega)
        have hconv := vg.converges v hv w hw _ (by omega) hown
        refine vg.holds_mono v _ _ ?_ hconv
        have hdrift := hD v hv w hw (R + k) hRn (by omega)
        have hwait := vg.waits v hv (R + k)
        have hto := hbackoff (R + k) hRn
        omega
  intro n hRn hn
  obtain ⟨k, rfl⟩ : ∃ k, n = R + k := ⟨n - R, by omega⟩
  exact key k hn

/-- **The unification.** A `ViewGrowth` *is* a `ViewSync`: production is
recovered by Skolemising the population it derives, and the two clauses
generalised off `blk` specialise back to it.

So the timed route no longer assumes what the untimed route proves. Every
result of this file and of `Timing.lean` applies to a `ViewGrowth` through
this reduction, with N1 absent from both routes. -/
noncomputable def toViewSync [Nonempty BlockId]
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn vg.built T R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n)
    (hbelow : ∀ n < R, PopulatedOn U T n) :
    ViewSync U T N :=
  let hb := exists_blk_of_populatedOn (U := U) (T := T) (N := N)
    (fun n hn => if h : R ≤ n then vg.populatedOn hcard hD hgst hbackoff n h hn
      else hbelow n (by omega))
  { blk := hb.choose
    built := vg.built
    timeout := vg.timeout
    gst := vg.gst
    delay := vg.delay
    rounds_le := vg.rounds_le
    blk_mem := hb.choose_spec.1
    blk_creator := hb.choose_spec.2.1
    blk_round := hb.choose_spec.2.2
    waits := fun v hv n _ => vg.waits v hv n
    timeout_pos := vg.timeout_pos
    latest := vg.latest
    built_le_latest := vg.built_le_latest
    latest_mem := vg.latest_mem
    prompt := vg.prompt
    holds := vg.holds
    holds_own := fun v hv n hn =>
      vg.holds_own v hv n hn _ (hb.choose_spec.1 v hv n hn)
        (hb.choose_spec.2.1 v hv n hn) (hb.choose_spec.2.2 v hv n hn)
    holds_mono := vg.holds_mono
    converges := vg.converges
    references := fun v hv n hn a ha har =>
      vg.references v hv n hn _ (hb.choose_spec.1 v hv (n + 1) (by omega))
        (hb.choose_spec.2.1 v hv (n + 1) (by omega))
        (hb.choose_spec.2.2 v hv (n + 1) (by omega)) a ha har }

@[simp] theorem toViewSync_built [Nonempty BlockId] (hcard) (hD) (hgst) (hbackoff) (hbelow) :
    (vg.toViewSync (D := D) hcard hD hgst hbackoff hbelow).built = vg.built := rfl

@[simp] theorem toViewSync_gst [Nonempty BlockId] (hcard) (hD) (hgst) (hbackoff) (hbelow) :
    (vg.toViewSync (D := D) hcard hD hgst hbackoff hbelow).gst = vg.gst := rfl

@[simp] theorem toViewSync_delay [Nonempty BlockId] (hcard) (hD) (hgst) (hbackoff) (hbelow) :
    (vg.toViewSync (D := D) hcard hD hgst hbackoff hbelow).delay = vg.delay := rfl

@[simp] theorem toViewSync_timeout [Nonempty BlockId] (hcard) (hD) (hgst) (hbackoff) (hbelow) :
    (vg.toViewSync (D := D) hcard hD hgst hbackoff hbelow).timeout = vg.timeout := rfl

/-- **L7c with production derived.** Reference coverage from view
convergence, on a structure that assumes no blocks exist. -/
theorem synchronisedOn_of_converges [Nonempty BlockId]
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn vg.built T R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n)
    (hbelow : ∀ n < R, PopulatedOn U T n) :
    SynchronisedOn U T R :=
  (vg.toViewSync hcard hD hgst hbackoff hbelow).synchronisedOn_of_converges hT
    (D := D) (by intro v hv w hw n hn hN; exact hD v hv w hw n hn hN)
    hgst hbackoff

end ViewGrowth

/-! ### The untimed condition, induced

`ViewsConverge` is stated over a `Delivery`, whose `held v n` is
documented as *what `v` held from round `n` when it built its round-`n+1`
block* — a build-time view. A `ViewGrowth` has exactly that, as
`holds v (built v (n+1))`, so it induces a delivery, and the untimed
condition becomes a theorem about it rather than a separate assumption.

Two relativisations survive the passage, and both are forced. The induced
delivery holds nothing outside `T` or above the horizon, because
`converges` and `holds_own` say nothing there; and the derived condition
runs from `R` on, because `converges` is silent below `gst`. So what is
obtained is `ViewsConvergeOn T R`, of which `ViewsConverge` is the case
`T = Correct`, `R = 0` — a hierarchy rather than an equivalence, in the
same shape as the one between `converges` and `Timing.covers`. -/

/-- `ViewsConverge` relative to a set and a starting round: what a
`T`-validator holds when it builds for round `n` is held by every
`T`-validator when it builds for round `n`, for `T`-authored blocks from
round `R` on. -/
def ViewsConvergeOn (D : Delivery U) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, R ≤ n → ∀ b ∈ D.held v n,
    (U.block b).creator ∈ T → b ∈ D.held w n

omit [DecidableEq BlockId] in
/-- At `T = Correct` and `R = 0` the relative condition is the original. -/
theorem viewsConverge_of_viewsConvergeOn {D : Delivery U}
    (h : ViewsConvergeOn D (Correct : Finset Validator) 0) : ViewsConverge D :=
  fun v hv w hw n b hb hbc => h v hv w hw n (Nat.zero_le _) b hb hbc

namespace ViewGrowth

variable (vg : ViewGrowth U T R N)

/-- **The delivery a timed structure induces.** `held` is the build-time
view, cut to the round it is indexed by; `accepted` keeps the
correct-authored part of it.

Accepting conservatively is what makes `accepted_inj` true rather than a
further assumption: two accepted blocks share an author only if that
author is correct, and non-equivocation then identifies them. Outside `T`
and above the horizon the delivery is empty, which is the most that can
be claimed — `converges` and `holds_own` quantify over `T`, and no block
exists above `N`. -/
def toDelivery : Delivery U where
  held v n := (vg.holds v (vg.built v (n + 1))).filter
    fun b => (U.block b).round = n ∧ v ∈ T
  held_spec v n i hi := by
    simp only [Finset.mem_filter] at hi
    exact ⟨vg.holds_sub _ _ hi.1, hi.2.1⟩
  accepted v n := (vg.holds v (vg.built v (n + 1))).filter
    fun b => ((U.block b).round = n ∧ v ∈ T) ∧
      (U.block b).creator ∈ (Correct : Finset Validator)
  accepted_sub v n i hi := by
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.1⟩
  accepted_inj v n i hi j hj hij := by
    simp only [Finset.mem_filter] at hi hj
    exact U.eq_of_creator_eq (vg.holds_sub _ _ hi.1) (vg.holds_sub _ _ hj.1)
      hi.2.2 rfl hij.symm (by rw [hi.2.1.1, hj.2.1.1])
  accepts_correct v _ n a ha hac := by
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2, hac⟩
  includes v _ n b hb hbc hbr a ha := by
    simp only [Finset.mem_filter] at ha
    obtain ⟨hamem, ⟨har, hvT⟩, _⟩ := ha
    -- above the horizon there is no such `b`, so the clause is vacuous
    have hnN : n < N := by have := vg.rounds_le b hb; omega
    exact vg.references v hvT n hnN b hb hbc hbr a hamem har

omit [DecidableEq BlockId] in
/-- Membership in the induced delivery, unfolded. -/
theorem mem_toDelivery {v : Validator} {n : ℕ} {b : BlockId} :
    b ∈ vg.toDelivery.held v n ↔
      b ∈ vg.holds v (vg.built v (n + 1)) ∧ (U.block b).round = n ∧ v ∈ T := by
  simp only [toDelivery, Finset.mem_filter, and_assoc]

/-- **The untimed condition, derived.** From `R` on, the induced delivery
satisfies view convergence relative to `T`.

The argument is `blk_mem_holds`'s, over a block the hypothesis supplies
rather than one `blk` names: its author holds it when it builds
(`holds_own`), that moment is past GST because rounds advance time,
convergence carries it to `w` within `delay`, and drift, the wait and the
backoff place that before `w` builds for the round above. -/
theorem viewsConvergeOn_toDelivery
    (hD : DriftOn vg.built T R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n) :
    ViewsConvergeOn vg.toDelivery T R := by
  intro v hv w hw n hRn b hb hbT
  rw [mem_toDelivery] at hb
  obtain ⟨hbmem, hbr, -⟩ := hb
  have hbids := vg.holds_sub _ _ hbmem
  have hnN : n ≤ N := by have := vg.rounds_le b hbids; omega
  rw [mem_toDelivery]
  refine ⟨?_, hbr, hw⟩
  have hown := vg.holds_own _ hbT n hnN b hbids rfl hbr
  have hle := le_built_of_waits (N := N) (fun v hv n _ => vg.waits v hv n) vg.timeout_pos hbT n (by omega)
  have hconv := vg.converges w hw _ hbT _ (by omega) hown
  refine vg.holds_mono w _ _ ?_ hconv
  have hdrift := hD w hw _ hbT n hRn (by omega)
  have hwait := vg.waits w hw n
  have hto := hbackoff n hRn
  omega

/-- A validator holds its own block when it builds the next, in the
induced delivery — `HoldsOwn` relative to `T`. -/
theorem holdsOwn_toDelivery {v : Validator} (hv : v ∈ T) {n : ℕ} (hn : n ≤ N)
    {b : BlockId} (hb : b ∈ U.ids) (hbc : (U.block b).creator = v)
    (hbr : (U.block b).round = n) : b ∈ vg.toDelivery.held v n := by
  rw [mem_toDelivery]
  refine ⟨vg.holds_mono v _ _ ?_ (vg.holds_own v hv n hn b hb hbc hbr), hbr, hv⟩
  exact le_trans (Nat.le_add_right _ _) (vg.waits v hv n)

/-- **`HoldsOwn`, in full.** With `T = Correct` the induced delivery
satisfies the clause outright, at every round: above the horizon no block
exists, and at the horizon itself `waits` still applies. -/
theorem holdsOwn_toDelivery' (vg : ViewGrowth U (Correct : Finset Validator) R N) :
    HoldsOwn vg.toDelivery := by
  intro v hv n b hb hbc hbr
  have hnN : n ≤ N := by have := vg.rounds_le b hb; omega
  exact vg.holdsOwn_toDelivery hv hnN hb hbc hbr

/-- **N2a, derived.** The induced delivery satisfies eventual DAG
synchrony from `R` on — the assumption of report §6.7, obtained from view
convergence and the schedule.

The horizon is no longer an obstruction. `EventuallyDelivers` quantifies
over every round, including `N`, where it asserts that a correct round-`N`
block is in hand when its holder builds for round `N+1`; `waits` reaching
past the horizon is exactly what supplies that step, and above `N` the
statement is vacuous because no block exists there. -/
theorem eventuallyDelivers_toDelivery
    (vg : ViewGrowth U (Correct : Finset Validator) R N)
    (hD : DriftOn vg.built (Correct : Finset Validator) R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n) :
    EventuallyDelivers vg.toDelivery R := by
  intro n hRn v hv a ha har hac
  have hnN : n ≤ N := by have := vg.rounds_le a ha; omega
  rw [mem_toDelivery]
  refine ⟨?_, har, hv⟩
  have hown := vg.holds_own _ hac n hnN a ha rfl har
  have hle := le_built_of_waits (N := N) (fun v hv n _ => vg.waits v hv n)
    vg.timeout_pos hac n hnN
  have hconv := vg.converges v hv _ hac _ (by omega) hown
  refine vg.holds_mono v _ _ ?_ hconv
  have hdrift := hD v hv _ hac n hRn hnN
  have hwait := vg.waits v hv n
  have hto := hbackoff n hRn
  omega

/-- **And hence coverage, the second way.** `synchronised_of_delivery`
(L7a) applies to the induced delivery, so the delivery route's conclusion
is available from view convergence too — the three routes of report §6.7–§6.9
meet. -/
theorem synchronised_toDelivery
    (vg : ViewGrowth U (Correct : Finset Validator) R N)
    (hD : DriftOn vg.built (Correct : Finset Validator) R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n) :
    Synchronised U R :=
  synchronised_of_delivery _ (vg.eventuallyDelivers_toDelivery hD hgst hbackoff)

/-- **The bridge, at the untimed condition's own parameters.** When the
reliable set is all of `Correct` and stabilisation has already happened,
the induced delivery satisfies `ViewsConverge` outright — the assumption
of the untimed route, obtained as a theorem of the timed one.

The two hypotheses `T = Correct` and `R = 0` are carried in the type
rather than assumed, since both are parameters of the structure. They are
the exact price of the passage: outside `T` the timed structure says
nothing, and below `gst` neither does the network. -/
theorem viewsConverge_toDelivery (vg : ViewGrowth U (Correct : Finset Validator) 0 N)
    (hD : DriftOn vg.built (Correct : Finset Validator) 0 D N) (hgst : vg.gst = 0)
    (hbackoff : ∀ n, D + vg.delay ≤ vg.timeout n) :
    ViewsConverge vg.toDelivery :=
  viewsConverge_of_viewsConvergeOn
    (vg.viewsConvergeOn_toDelivery hD (le_of_eq hgst) (fun n _ => hbackoff n))

end ViewGrowth

end Production

end LeanDag
