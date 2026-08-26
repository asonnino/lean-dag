# lean-dag — Hammerhead 2.0: design record

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for the **Hammerhead 2.0** arc,
written before the development: the definitions and theorems below are
a plan, the Lean signatures are proposals, and §12 lists the decisions
the plan asks the author to settle before Phase 1 begins. The question
is whether the adaptive *leader-count* mechanism of the Hammerhead 2.0
paper (working title; `\sysname` in the manuscript) — every few seconds,
measure on the agreed DAG the fraction of leader slots the base protocol
decided directly, and drive the number of leaders per round with an
additive-increase, multiplicative-decrease rule — is safe and live over
each of the three base protocols this development already formalises:
Mysticeti (report §3), Odontoceti, which the paper calls Blue Bottle
(report §10), and Nemo-Nemo (report §15). Results carry **HH**-labels;
everything lives in `LeanDag/HammerheadTwo/` under the statement/proof
partition (§10), with `decide` witnesses in `LeanDagTest/HammerheadTwo/`,
consuming the core read-only.

## 0. Overview

The paper abstracts its base protocol as four assumptions, A1–A4: rounds
and slots, causal completeness, a direct decision predicate local to a
wave, and safety and liveness for every fixed configuration. Its
mechanism is a control loop on one integer. Upon committing the first
leader whose round exceeds `lastRound + Interval` — the *anchor* — a
validator takes the anchor's causal history over the last `Interval`
rounds as the *window*, counts the slots the direct rule decides within
the window, compares the count with the number expected under the
current leader count, and moves the count up by one or down by
`2^backoff`; the new count applies to rounds after the anchor.

The arc's one structural observation is that **the paper's algorithm
decides under the count in force and only then switches**. Algorithm 2's
`TryDecide` evaluates every round above the last commit at the current
count; `TryCommit` walks the verdicts in slot order, commits the anchor,
updates, and returns; only rounds above the anchor are re-decided under
the new count. So the verdicts of configuration `k`'s range — the rounds
strictly above the `k`-th anchor and up to the `(k+1)`-st — are
derivations of the base relation against a **fixed** uniform schedule,
`m_k` leaders in every round, including whatever decision-anchors above
the `(k+1)`-st anchor an indirect decision reads. Nothing in the range
depends on configuration `k+1`. The dependency is therefore well-founded
by induction on `k`, and the arc needs neither the bounded relation nor
the two-epoch lag of the identity-adapting arc (`adaptive-leaders.md`
§2), whose circularity arose because there the leader of a slot's anchor
was itself a function of verdicts.

Three consequences shape the plan.

- **Safety holds for any update rule.** The `(k+1)`-st count is a
  function of the universe, the anchor block and the previous state; the
  anchor is the least committed slot past the threshold in a schedule
  both validators share; the verdicts of the range are agreed by the base
  rule's own agreement theorem. So two validators agree on every
  configuration and every verdict for **any** deterministic update, with
  no synchrony or fairness hypothesis — the AIMD rule is one instance
  (HH3, HH4).
- **Liveness is the existence of the configuration sequence.** Each
  range closes because the base rule decides every slot of a fixed
  schedule on the full view; the next anchor exists because committed
  slots recur; the sequence is built by recursion on `k` (HH8). What the
  arc consumes from the base is exactly the paper's A4, stated as a
  clause on a schedule (§7).
- **A4 is not automatic under multiple leaders.** With the paper's
  own rotation, `GetLeader(r + l)`, and `m ≥ 2` leaders, the run
  fairness the development's liveness route consumes (`FairRunOn`,
  report §5) fails at `n = 4`, `f = 1`: no three consecutive rounds are
  ever fully correct-led. Liveness holds anyway, by a different descent
  in which only the *first* slot of each round matters (§8). Discharging
  A4 for the paper's schedule is Phase 4, and is the arc's one piece of
  new base-protocol theory.

The arc is generic over the base protocol through an explicit interface
(§2), instantiated three times (Phase 5); the paper's Lean appendix can
then say, accurately, that everything is proved from A1–A4 and not from
Mysticeti.

### 0.1 Correspondence with the paper

| paper | this arc |
| :-- | :-- |
| A1 rounds and slots; `GetLeader(r + l)` | `Sched m`, `elect` (§3) |
| A2 causal completeness | `View.complete`, P4; the window as a view (§4) |
| A3 direct decision predicate | `BaseRule.DirectCommitIn` (§2) |
| A4 base safety | `BaseRule.agree` (§2) |
| A4 base liveness | `BaseRule.LiveOn S` (§7), discharged in Phases 4–5 |
| Algorithm 2 (`TryCommit`, `TryDecide`) | `PartialRun`, `ConfigRun` (§5) |
| Algorithm 3 (`UpdateLeaders`, `GetSubDag`, `CountDirectCommits`, `ExpectedCommits`) | `window`, `observed`, `expected`, `Aimd.update` (§4) |
| Window Agreement | HH2 |
| Leader-Count Agreement | HH3 |
| Safety (Agreement, Integrity, Total Order) | HH4, HH5 |
| Configuration Progress; Liveness | HH8 |
| Lean appendix: assumed vs. proved, witnesses | §9, §11 |

## 1. The mechanism, in this development's vocabulary

A *configuration* is a pair `(start, m)`: the round after which it is in
force and its leader count. Configurations are indexed `k = 0, 1, …`;
`C_0 = (0, 1)` (Algorithm 2 initialises `lastRound ← 0` and, per the
paper's Algorithm 1, one leader). The `(k+1)`-st anchor `A_{k+1}` is the
least slot of `Sched m_k`, in slot order, that is committed and whose
round exceeds `start_k + Interval`; then `start_{k+1}` is `A_{k+1}`'s
round and `m_{k+1} = update(m_k, backoff_k, U, A_{k+1})`.

The *range* of configuration `k` is the set of slots of `Sched m_k` at
rounds in `(start_k, start_{k+1}]`. Every slot of the range is decided by
the base relation against `Sched m_k`. The slots of round `start_{k+1}`
*after* the anchor belong to range `k`: the paper's text says the new
count applies to rounds after the anchor, and this arc follows the text
(§12, D4; the pseudocode is ambiguous there and a comment in the
manuscript records it).

The *ledger* is the concatenation over `k` of the committed blocks of
range `k`, in slot order of `Sched m_k`.

## 2. The base-protocol interface

The arc never counts anything. What it needs of a base protocol is a
decision relation parametric in the schedule, agreement across views for
a fixed schedule, and — for the measurement — the direct-commit
predicate. The three protocols differ in their universe and view types
(Nemo has `Nemo.Universe` and `Nemo.View`; the Byzantine rules share
`BlockUniverse` and `View`) and in their fault classes, so the interface
bundles the types:

```lean
structure BaseRule (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (BlockId : Type) [DecidableEq BlockId] (Payload : Type) where
  /-- The universe type of the base development. -/
  Universe : Type
  /-- The view type, indexed by universe. -/
  View : Universe → Type
  /-- The block an id denotes: rounds, creators and references. -/
  block : Universe → BlockId → Block Validator BlockId Payload
  ids : Universe → Finset BlockId
  viewIds : ∀ {U}, View U → Finset BlockId
  /-- The full view. -/
  full : ∀ U, View U
  /-- A3: the direct commit predicate, view-relative. -/
  DirectCommitIn : ∀ {U}, View U → BlockId → ℕ → Prop
  /-- The decision relation, parametric in the schedule. -/
  Decided : [Slots Validator] → ∀ {U}, View U → ℕ → Option BlockId → Prop
  /-- A4, safety: verdicts agree across views for a fixed schedule. -/
  agree : ∀ [Slots Validator] {U} (V₁ V₂ : View U) k v₁ v₂,
    Decided V₁ k v₁ → Decided V₂ k v₂ → v₁ = v₂
  /-- A direct commit of a candidate is a commit verdict. -/
  decided_of_directCommitIn : ∀ [Slots Validator] {U} (V : View U) k L,
    IsLeaderBlock block U k L → DirectCommitIn V L (Slots.slotRound k) →
    Decided V k (some L)
  /-- Verdicts persist into larger views. -/
  mono : ∀ [Slots Validator] {U} (V V' : View U) k v,
    viewIds V ⊆ viewIds V' → Decided V k v → Decided V' k v
```

`IsLeaderBlock block U k L` is the generic candidate predicate — the
right round, the right author — stated over the `block` function rather
than a particular universe type; each instantiation shows it coincides
with its own `IsLeaderBlock`. The liveness fields are in §7. Types live
in `Type` rather than `Type*`: every concrete universe of the
development is in `Type`, and a universe-polymorphic structure field
would complicate every statement for no instance (§12, D1).

`decided_of_directCommitIn` is what makes the window count well defined:
two directly committed candidates of one slot on one view are one block
by `agree`, so the paper's count over leader *blocks* — several upon
equivocation — equals a count over *slots* (§4).

## 3. Schedules

The paper's slot `(r, l)`, for `l` below the count, is led by
`GetLeader(r + l)`; the leader function does not depend on the count, and
only *which slots exist* changes across configurations. In this
development a schedule with `m` leaders in every pipelined round is
`Slots.uniform 1 m elect`, slot `κ` at round `κ / m` with offset `κ % m`
(`pipelining-and-multi-leader.md` §3.2):

```lean
/-- `m` leaders in every round, slot `(r, l)` led by `getLeader (r + l)`. -/
def Sched (getLeader : ℕ → Validator) (hwin : WindowInjective getLeader maxLeaders)
    (m : ℕ) (hm : 0 < m) (hmax : m ≤ maxLeaders) : Slots Validator :=
  Slots.uniform 1 m Nat.one_pos hm (fun κ => getLeader (κ / m + κ % m)) (…)
```

`Slots.keyed` asks that the `m` leaders of a round be distinct
validators, which under `getLeader (r + l)` is injectivity of
`getLeader` on every window of `maxLeaders` consecutive naturals
(`WindowInjective`). Round-robin `getLeader r = r % n` satisfies it for
`maxLeaders ≤ n`, and is the arc's witness schedule (HH1). Whether the
model should carry `getLeader` abstract with this clause, or fix
round-robin, is D8.

`Sched` is a `def`, not an instance, and every use passes
`(S := Sched … m …)`: the arc's whole point is several `Slots` instances
on one validator type.

## 4. The window and the update

**The window.** `GetSubDag` is the anchor's causal history restricted to
rounds `[r − Interval, r]`. In this development `history U A` is the
finite causal history (`History.lean`), and its restriction by round is
a `View`: `View.complete` holds because references descend in round, so
a block of the restriction references only blocks of the restriction or
below the cut — and the cut is a lower bound on round, so below the cut
is outside the *universe* of the count only, not of the view. The
definition is the restriction of `history U A` to rounds `≥ r −
Interval`, closed by adding nothing: a block at round `r − Interval`
references round `r − Interval − 1`, which the view must hold. So the
window view is `history U A` itself, and the round bound is applied by
the count, not by the view (D9 records the alternative). Both readings
give the same count, since the direct predicate at round `r'` reads
rounds `[r', r' + w)` only (A3).

```lean
/-- The anchor's causal history, as the view a validator measures on. -/
def windowView (R : BaseRule …) (U : R.Universe) (A : BlockId) : R.View U
```

For `BlockUniverse` this is `⟨history U A, history_subset_ids, …⟩`; the
interface asks each instantiation for it (a field `historyView`).

**The measurement.** For each round `r'` of `[r − Interval, r]` and each
offset `l < m`, the slot `(r', l)` of `Sched m` counts if some candidate
of it is directly committed on the window view:

```lean
def observed (R : BaseRule …) (P : Params) (U) (A : BlockId) (m : ℕ) : ℕ :=
  ((Finset.range (P.interval + 1)) ×ˢ (Finset.range m)).filter (fun ⟨d, l⟩ =>
    let r' := (R.block U A).round - d
    ∃ L ∈ R.ids U, IsLeaderBlock R.block U (m * r' + l) L ∧
      R.DirectCommitIn (windowView R U A) L r').card

def expected (P : Params) (m : ℕ) : ℕ := (P.interval - P.waveLength + 1) * m
```

The paper counts leader blocks; by §2 the two counts agree, and the arc
counts slots because that is what `expected` counts.

**The rule.** `threshold` is a rational in the paper and an integer
comparison in the implementation; the arc takes an integer pair
`(num, den)` and the test `den * observed ≥ num * expected` (D3). The
paper's `0.96` is `(96, 100)`.

```lean
structure Params where
  interval waveLength maxLeaders num den : ℕ
  interval_pos : 0 < interval
  max_pos : 0 < maxLeaders

/-- Additive increase, multiplicative decrease. -/
def Aimd.update (P : Params) (m backoff : ℕ) (healthy : Bool) : ℕ × ℕ :=
  if healthy then (min (m + 1) P.maxLeaders, 0)
  else (max (m - 2 ^ backoff) 1, backoff + 1)

/-- The paper's `UpdateLeaders`, as a function of the universe and the anchor. -/
def Aimd.rule (R) (P) : UpdateRule R :=
  fun m backoff U A =>
    Aimd.update P m backoff (decide (P.den * observed R P U A m ≥ P.num * expected P m))

/-- Any deterministic function of the state, the universe and the anchor. -/
abbrev UpdateRule (R : BaseRule …) := ℕ → ℕ → R.Universe → BlockId → ℕ × ℕ
```

Safety (§6) is stated for `UpdateRule`; the AIMD facts (HH7) are stated
for `Aimd.rule`.

**A note on `expected`.** The window has `Interval + 1` rounds. A slot
at round `r'` is decidable within it when `r' + w − 1 ≤ r`, which is
`Interval − w + 2` rounds, one more than the paper's formula. On the
other hand the anchor's own round contributes one block to the window,
so at round `r − w + 1` a direct commit needs a quorum of certifiers
among a single block, and the count there is zero whenever the quorum
exceeds one; the decidable rounds are then `Interval − w + 1`, the
paper's number, for a reason the paper does not give. Which of the two
holds is settled on data in Phase 1 (§9), and the paper is told
(§11, F2). The bound `observed ≤ expected` is protocol-specific — it
needs A3's locality and a quorum above one — and is proved for
Mysticeti in Phase 5 rather than assumed of the interface.

## 5. The run

What a validator holds mid-execution is a *partial run* closed up to a
configuration height; the object safety and liveness are stated on.

```lean
structure PartialRun (R : BaseRule …) (P : Params) (upd : UpdateRule R)
    (U : R.Universe) (V : R.View U) (K : ℕ) where
  /-- `start k`, the round after which configuration `k` is in force. -/
  start : ℕ → ℕ
  /-- The leader count of configuration `k`. -/
  count : ℕ → ℕ
  backoff : ℕ → ℕ
  /-- `anchor k` is the slot index, in `Sched (count k)`, of `A_{k+1}`. -/
  anchor : ℕ → ℕ
  /-- `vdct k κ` is the verdict of slot `κ` of `Sched (count k)`. -/
  vdct : ℕ → ℕ → Option BlockId
  init : start 0 = 0 ∧ count 0 = 1 ∧ backoff 0 = 0
  count_pos : ∀ k, 0 < count k
  count_le : ∀ k, count k ≤ P.maxLeaders
  /-- Every slot of the range, through the anchor, is decided against the
  configuration's schedule. -/
  closed : ∀ k, k < K → ∀ κ, start k < (Sched (count k)).slotRound κ → κ ≤ anchor k →
    R.Decided (S := Sched (count k)) V κ (vdct k κ)
  /-- The anchor is committed and past the threshold … -/
  anchor_commits : ∀ k, k < K →
    (∃ A, vdct k (anchor k) = some A) ∧ start k + P.interval < (Sched (count k)).slotRound (anchor k)
  /-- … and is the least such slot. -/
  anchor_least : ∀ k, k < K → ∀ κ, κ < anchor k →
    start k + P.interval < (Sched (count k)).slotRound κ → vdct k κ = none
  start_succ : ∀ k, k < K → start (k + 1) = (Sched (count k)).slotRound (anchor k)
  /-- The next configuration is the rule's. -/
  update : ∀ k, k < K → ∀ A, vdct k (anchor k) = some A →
    (count (k + 1), backoff (k + 1)) = upd (count k) (backoff k) U A
```

A `ConfigRun` is the total form (`K` unbounded), with `closed`
strengthened to the whole range — through the end of the anchor's round
— so that the ledger of range `k` is defined. The distinction matters
for what a validator holds: at the instant it commits `A_{k+1}` the
trailing slots of that round may be undecided, and the configuration
sequence must not wait for them (§1).

`count_pos` and `count_le` are clauses of the run rather than
consequences of the rule because the run is stated for an arbitrary
`UpdateRule`; for `Aimd.rule` they are theorems (HH7) and the clauses
are discharged.

Slots are numbered per configuration (D2): `vdct k` is a verdict
function on `Sched (count k)`, which is the object every base theorem
speaks about, and the ledger of the range is `commitSeq` of that
function restricted to the range. A global `(round, offset)` indexing
was considered and rejected: it would need a fourth schedule structure
the base development does not have, and every derivation would be
translated into it and back.

## 6. Safety

**HH1 (schedules).** `Sched m` is a lawful `Slots` instance for every
`0 < m ≤ maxLeaders`; round-robin is window-injective at
`maxLeaders ≤ n`. From `Slots.uniform`; nothing new.

**HH2 (the window is agreed).** Any two views holding the anchor hold
its whole history (`View.mem_of_reaches`, T6a), so the window view, the
count and the update read the same data on every view. In this model
the universe is the shared ground truth and the statement is that the
measurement is a function of `(U, A)` alone — which is the paper's
Window Agreement lemma, with the paper's Claims 1–2 being P4 and view
convergence (report §5).

**HH3 (partial runs agree).** Two partial runs over one universe —
whatever views, whatever heights — agree on `start`, `count`,
`backoff`, `anchor` and on every verdict of their common ranges:

```lean
theorem partialRun_agree {V₁ V₂ : R.View U} {K₁ K₂ : ℕ}
    (R₁ : PartialRun R P upd U V₁ K₁) (R₂ : PartialRun R P upd U V₂ K₂) :
    ∀ k, k ≤ min K₁ K₂ →
      R₁.start k = R₂.start k ∧ R₁.count k = R₂.count k ∧ R₁.backoff k = R₂.backoff k ∧
      (k < min K₁ K₂ → R₁.anchor k = R₂.anchor k ∧
        ∀ κ, R₁.start k < (Sched (R₁.count k)).slotRound κ → κ ≤ R₁.anchor k →
          R₁.vdct k κ = R₂.vdct k κ)
```

By induction on `k`. The configurations agree below `k` by hypothesis,
so both runs' range-`k` verdicts are derivations against one schedule
and agree by `R.agree`; the anchor is the least committed slot past one
threshold in one verdict function, so the anchors agree; the update is
one function of one universe, one anchor and one state. No synchrony, no
fairness, no clause on `upd`.

**HH4 (safety).** Total runs agree everywhere; the corollary in the
shape of M6.

**HH5 (the ledger).** The concatenated committed sequences of two total
runs are equal, range by range and hence as one list; a block appears at
most once (`Slots.keyed` per range, distinct rounds across ranges). This
is the paper's Agreement, Integrity and Total Order in the form the
development states them (M7, `outputAt_unique`).

**HH6 (conservativity).** Under the constant rule
`fun m b _ _ => (m, b)` every configuration has the initial count and a
run's verdicts are `Decided` verdicts of `Sched 1`: the arc collapses
onto the base development.

**HH7 (the AIMD rule).** `Aimd.update` keeps the count in
`[1, maxLeaders]`; an unhealthy window strictly decreases a count above
one; a healthy one increases a count below the maximum by one; `backoff`
resets on a healthy window. For Mysticeti (Phase 5): `observed ≤
expected`, from A3's locality and `quorumCard ≥ 2`, in whichever of the
two forms §4 turns out to hold on data.

## 7. Liveness, interface half

The paper's A4 liveness is "after GST, honest validators commit new
leaders infinitely often". In this development liveness is structural:
`SynchronisedOn U T R` and `PopulatedOn U T r` say what the DAG must
contain, view convergence supplies them (report §5), and no theorem
mentions time. The interface therefore carries those two predicates as
fields and states A4 as a clause on a schedule:

```lean
  /-- The structural interface of the base liveness route. -/
  SynchronisedOn : Universe → Finset Validator → ℕ → Prop
  PopulatedOn : Universe → Finset Validator → ℕ → Prop
  Reliable : Finset Validator          -- `Correct`, or Nemo's `Live`
  quorum : ℕ                            -- the count `T` must reach
```

```lean
/-- **A4, liveness, on one schedule.** Above the synchrony round every slot
is decided on the full view, and committed slots recur. -/
def BaseRule.LiveOn (R : BaseRule …) (S : Slots Validator) : Prop :=
  ∀ (U : R.Universe) (T : Finset Validator) (Rnd : ℕ),
    T ⊆ R.Reliable → R.quorum ≤ T.card →
    R.SynchronisedOn U T Rnd → (∀ r, Rnd ≤ r → R.PopulatedOn U T r) →
    (∀ k, Rnd ≤ S.slotRound k → ∃ v, R.Decided (S := S) (R.full U) k v) ∧
    (∀ r, ∃ k, r ≤ S.slotRound k ∧ ∃ L, R.Decided (S := S) (R.full U) k (some L))
```

The population hypothesis is stated at every round above `Rnd` rather
than to a horizon `N`, which is the shape of `adaptiveRun_exists` and
of every total-run statement; the finite-horizon form belongs to the
witnesses.

**HH8 (the configuration sequence exists).** If `LiveOn (Sched m)` holds
for every `m` in `[1, maxLeaders]`, then on a universe synchronised over
a reliable quorum and populated above `Rnd` a total run exists on the
full view:

```lean
theorem configRun_exists (hlive : ∀ m (hm : 0 < m) (hmax : m ≤ P.maxLeaders), R.LiveOn (Sched m …))
    (hT : T ⊆ R.Reliable) (hcard : R.quorum ≤ T.card)
    (hs : R.SynchronisedOn U T Rnd) (hpop : ∀ r, Rnd ≤ r → R.PopulatedOn U T r) :
    Nonempty (ConfigRun R P upd U (R.full U))
```

By recursion on `k`: range `k` is decided by the first conjunct at
`Sched (count k)`; some committed slot lies past `start k + interval` by
the second; the least such slot is the anchor; the rule gives the next
state, and `count_pos`/`count_le` hold by HH7 for `Aimd.rule` (the
theorem is stated for rules that keep the count in range). The paper's
Configuration Progress is the inductive step; its Liveness is the
existence of the total run together with HH5.

Two things are deliberately not in HH8. Ranges below `Rnd` are not
decided by the clause — the run's `closed` for those ranges is taken as
a hypothesis, exactly as the base liveness statements start at the
synchrony round. And the statement is on the full view; the *local*
form — every reliable validator decides on its own view at an explicit
time — needs the pacing structures of report §5 and `R.mono`, and is
deferred to a later phase (D6) rather than promised here.

## 8. Liveness, the descent under multiple leaders

**The problem.** The base liveness route decides everything below a run
of `c` consecutive committed slots spanning the eligibility gap
(`decided_below_of_committed_run`, L10), and the run comes from
`FairRunOn T c`: `c` consecutive `T`-led slots, arbitrarily far out.
With `m` leaders per round the run must cover three full rounds,
`c = 3m`, all of whose `3m` leaders are in `T`. Under
`getLeader (r + l) = (r + l) % n` the leaders of three consecutive rounds
are `m + 2` consecutive residues, and at `n = 4`, `f = 1`, `m = 2` these
are all four validators: no run ever exists. The witness schedule of the
identity-adapting arc, `waveRobin`, sidesteps this by holding a leader
for a wave; the paper's schedule does not, and the paper's evaluation
runs `m` up to five.

**The descent.** Only the *head* of a round — its slot at offset `0` —
matters. For a slot `σ` at round `ρ'`, the eligible anchors begin at
round `ρ' + g` (`g = 3` for Mysticeti, `2` for the two-round rules), and
the head of that round precedes every other eligible slot. If the head
is directly committed then it is the least eligible committed slot, the
set of eligible intermediates is empty, and `σ` is decided by the
indirect rule outright, whatever its own direct evidence. So:

```lean
/-- A stretch of rounds all of whose heads are `T`-led. -/
def HeadsRun (S : Slots Validator) (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ r, ∃ ρ, r ≤ ρ ∧ ∀ i, i < c → S.leader (S.head (ρ + i)) ∈ T
```

**HH9a (decided stretch descent).** The base descent, weakened: a
stretch of consecutive slots all *decided*, whose top slot is committed,
spanning eligibility for everything below it, decides everything below
it. The base proof goes through unchanged — the intermediates the
minimality argument meets are decided and not committed, hence skipped —
and the weakening is what lets Byzantine-led slots sit inside the
stretch.

**HH9b (heads decide the stretch).** If the heads of rounds
`ρ + g, …, ρ + 2g − 1` are `T`-led then, above the synchrony round, every
slot at rounds `ρ, …, ρ + g − 1` is decided on the full view, and the
head of `ρ + g` is committed: the stretch from the first slot of `ρ` to
that head satisfies HH9a's hypotheses.

**HH9c (`LiveOn` from `HeadsRun`).** `HeadsRun (Sched m) T g` implies
`R.LiveOn (Sched m)` — HH9b at every `r`, then HH9a.

**HH9d (round-robin places heads).** Under `getLeader r = r % n`, the
head of round `r` is led by `r % n` *whatever the count*, so `HeadsRun`
is one arithmetic statement for every configuration: `g` consecutive
`T`-led residues exist in every cycle when `|Tᶜ| ≤ f` and `n` is at
least `(g − 1) f + f + 1`. For Mysticeti, `n ≥ 3f + 1` and `g = 3`; for
the two-round rules, `g = 2` at `n ≥ 5f + 1` and `n ≥ 2f + 1`. The
pigeonhole is the arc-counting argument the `FairRunOn` docstring
records and the wave-aligned schedule was introduced to avoid; it is
needed here because the paper's schedule is per-round rotation.

HH9c and HH9d together discharge HH8's `hlive` for the paper's own
schedule at every count, which is the paper's A4 for multi-leader
rounds — assumed there, proved here (§11, F3). HH9a–c are stated on the
interface with `g` a field (`gap`), and the per-protocol content is the
one lemma "a directly committed head anchors every slot `g` rounds
below with no intermediates", which is the eligibility arithmetic each
protocol already has (`eligible_iff`, `spansEligible_two`).

## 9. Witnesses (`LeanDagTest/HammerheadTwo/`)

Every definition is exercised by `decide` before anything is proved
from it, and a run whose count moves is exhibited before agreement is
stated.

- **The window and the count.** A four-validator universe at `f = 1`,
  `Interval` small (three or four rounds), with an anchor whose history
  the count reads: `observed` and `expected` computed by `decide`, which
  settles §4's question about the top rounds of the window on data;
  `Aimd.update` at both branches; the count reaching `maxLeaders` and
  the floor.
- **A run whose count moves.** The same universe extended: configuration
  `0` at count `1`, the first anchor healthy, configuration `1` at count
  `2`; a slot `(r, 1)` that exists in `Sched 2` and not in `Sched 1`,
  with a verdict; two views' partial runs constructed and shown
  identical by HH3. Then the unhealthy branch: a window with a stalled
  slot and the count returning to `1`.
- **The heads descent.** A DAG with a Byzantine head undecided directly
  and decided by the head three rounds above; `HeadsRun` for round-robin
  at `n = 4` by `decide` over one cycle.
- **The three instantiations.** `BaseRule` for Mysticeti, Odontoceti
  and Nemo, each on its existing test model (`U7`, the Odontoceti model,
  the three-validator Nemo model), with the window count computed under
  each rule.

## 10. Layout and discipline

The arc adopts the statement/proof partition of the Mahi-Mahi and Black
Marlin arcs (`mahi-mahi.md` §9), and is the third to do so;
`HammerheadTwo` is added to `ARCS` in `scripts/check-arc-holes.py` in
Phase 1.

```
LeanDag/HammerheadTwo/
  Model/         definitions only, theorem-free:
                 Rule (§2, §7), Schedule (§3), Window (§4), Run (§5), Heads (§8)
  Helpers/       lemma infrastructure; unaudited
  <Result>/Statement.lean   imports Model/ only; `def Statement : Prop`; never a proof
  <Result>/Proof.lean       `theorem holds : Statement`; unaudited
  Instances/     the three `BaseRule`s; audited (they are definitions)
LeanDagTest/HammerheadTwo/  witness models; audited
```

Results: `Window` (HH2), `Agreement` (HH3, HH4), `Ledger` (HH5),
`Conservativity` (HH6), `Aimd` (HH7), `Liveness` (HH8), `Heads`
(HH9a–d). HH1 is a definition and its `Slots` proof obligations.

**The freeze protocol**, as in the two arcs before: for each phase,
statements are written, reviewed, agreed, and then frozen — no edit to
`Model/` or a `Statement.lean` without notice to the author, however
small; a proof that needs a statement changed stops and raises the
need. Proofs are then written until they verify, the hole checker and
`#print axioms` are clean, and the phase is committed.

**Relation to the core.** Read-only: `Block`, `BlockDag`, `Causality`,
`History`, `Validators`, `Schedule`, `Mysticeti`, `Liveness`,
`Odontoceti/`, `Nemo/`. HH9a is a weakening of
`decided_below_of_committed_run`; it is proved in the arc's `Helpers/`,
not by editing the core, and reported as a candidate for the core if
the base development wants it. If a phase finds it needs a change to
the core, that is a finding, not a refactor.

**Relation to the identity-adapting arc.** `LeanDag/Adaptive/` is not
consumed. The paper says the two mechanisms are orthogonal and
composable; their composition — a policy that chooses both who leads and
how many — is a later question, and §13 records it.

## 11. Findings for the paper

Each is recorded here with its status and reaches the manuscript as an
author comment when confirmed.

- **F1 — the anchor's round.** Algorithm 2 returns at the anchor and
  restarts from `r_committed + 1`; whether the slots of the anchor's
  round after the anchor are committed at all, and under which count,
  is not determined by the pseudocode. The arc follows the text
  (previous count through the anchor's round). *In the manuscript*
  (`sections/protocol.tex`).
- **F2 — `expected`.** The window's decidable rounds are
  `Interval − w + 2` by the stated reason and `Interval − w + 1` by
  another (§4). *To be settled by the Phase 1 witness.*
- **F3 — A4 under multiple leaders.** Run fairness fails for the paper's
  schedule at `m ≥ 2` and small `n`; liveness holds by the heads
  descent, and the paper's A4 is a theorem for its own schedule
  (HH9). *Phase 4.*
- **F4 — A5 is unnecessary.** The proof outline's "any leader committed
  after `r_i` has the anchor in its causal history" is not consumed:
  agreement is the base agreement theorem under one fixed schedule plus
  determinism of the update, and the lagging validator is view
  convergence. *Phase 2.*
- **F5 — safety for any update rule.** The paper's Leader-Count
  Agreement is stated for the AIMD rule; it holds for any deterministic
  function of the universe and the anchor, which is a stronger and
  simpler statement for the Lean appendix. *Phase 2.*
- **F6 — blocks versus slots.** `CountDirectCommits` iterates over
  leader blocks and could in principle count a slot twice; it cannot,
  by the base agreement theorem (§2). *Phase 2.*

## 12. Decisions for the author

Settle before Phase 1; each is written with the recommendation first.

- **D1 — the interface's types.** Bundle `Universe`/`View` in `Type`
  inside `BaseRule` (recommended: three instantiations, one statement
  each), or make the arc a functor over a typeclass on universe types.
- **D2 — indexing.** Per-configuration slot numbering, verdicts as
  functions on `Sched (count k)` (recommended), or a global
  `(round, offset)` index.
- **D3 — the threshold.** An integer pair with the test
  `den * observed ≥ num * expected` (recommended; the implementation's
  form), or a `ℚ`.
- **D4 — the anchor's round.** The previous count through the whole of
  the anchor's round (recommended; the text's reading), or the new count
  from the slot after the anchor.
- **D5 — the count.** Over slots, with the block count shown equal
  (recommended), or over blocks as the pseudocode iterates.
- **D6 — local liveness.** HH8 on the full view, local form deferred
  (recommended for this arc), or the time-indexed local statement in
  scope from the start.
- **D7 — the initial configuration.** `(0, 1)` as Algorithm 1
  initialises (recommended), or an initial count as a parameter.
- **D8 — the leader function.** Abstract `getLeader` with the
  window-injectivity clause, round-robin as witness (recommended), or
  round-robin fixed in the model.
- **D9 — the window view.** The anchor's whole history as the view with
  the round bound in the count (recommended; it is a `View` with no
  closure proof — the history is closed), or the round-restricted
  set with the closure argument of §4.

## 13. Out of scope

- **Composition with the identity-adapting arc** — one policy choosing
  who leads and how many. The count-adapting mechanism decides under
  the count in force and the identity-adapting one needs the bounded
  relation; whether one stratification serves both is a separate arc's
  question.
- **Garbage collection.** A joiner reading the window from a truncated
  universe; the analogue of `HorizonStable` (report §16, I5).
- **Non-pipelined base protocols**, where `expected` is divided by the
  wave length; all three instantiated protocols are pipelined.
- **Certified DAGs.** The paper says the measurement applies; the model
  has no certified-DAG base.
- **Performance (R2).** The paper's evaluation claims are outside the
  formal model, as the paper says.
- **Byzantine bias of the measurement.** The paper notes a Byzantine
  leader can lower the direct rate within a window; that the damage is
  bounded to one interval is a quantitative claim not attempted here.
