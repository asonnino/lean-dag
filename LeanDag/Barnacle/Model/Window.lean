import LeanDag.Barnacle.Model.Schedule
import Mathlib.Data.Finset.Prod

/-!
# Barnacle: the window, the count, and the AIMD rule

The paper's Algorithm 3 (`barnacle.md` §4): upon committing the
anchor, take its causal history over the last `interval` rounds as the
window, count the slots the direct rule decides within it, compare the
count with the number expected under the current leader count, and move
the count up by one or down by `2^backoff`.

The window is the anchor's history *view* — `BaseRule.historyView` —
and the round bound is applied by the count rather than by the view:
the history is a view without further proof, and the direct predicate at
round `r'` reads rounds `[r', r' + waveLength)` only (A3), so the two
readings count the same slots. The count is over *slots* where the
paper iterates over leader blocks: two directly committed candidates of
one slot are one block by `BaseRule.Laws.agree`, so the counts agree, and
counting slots is what `expected` counts.

The threshold is an integer pair `(num, den)` and the test an integer
comparison, as the implementation executes it; the paper's `0.96` is
`(96, 100)`.

**Trusted core of the arc: definitions only.** The `Decidable` instance
is by `inferInstanceAs`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- The mechanism's parameters: the reconfiguration interval in rounds,
the cap on the leader count, and the health threshold `num / den`. -/
structure Params where
  /-- Rounds between reconfigurations. -/
  interval : ℕ
  /-- The upper bound on the leader count. -/
  maxLeaders : ℕ
  /-- The threshold's numerator. -/
  num : ℕ
  /-- The threshold's denominator. -/
  den : ℕ
  interval_pos : 0 < interval
  max_pos : 0 < maxLeaders

namespace BaseRule

/-- Slot `κ` of schedule `S` has a candidate directly committed on view
`V`. The unit the window count counts. -/
def SlotDirect (R : BaseRule Validator BlockId Payload) (S : Slots Validator)
    (U : R.Universe) (V : R.View U) (κ : ℕ) : Prop :=
  ∃ L ∈ R.ids U, R.IsLeaderBlock S U κ L ∧ R.DirectCommitIn V L (S.slotRound κ)

instance instDecidableSlotDirect (R : BaseRule Validator BlockId Payload)
    (S : Slots Validator) (U : R.Universe) (V : R.View U) (κ : ℕ) :
    Decidable (R.SlotDirect S U V κ) :=
  inferInstanceAs (Decidable (∃ L ∈ R.ids U, R.IsLeaderBlock S U κ L ∧
    R.DirectCommitIn V L (S.slotRound κ)))

end BaseRule

/-- **The window count** (`CountDirectCommits`): the slots `(r', l)`, for
`r'` in the `interval + 1` rounds up to the anchor's and `l` below the
count `m`, whose candidate is directly committed on the anchor's history
view. Slot `(r', l)` is slot `m * r' + l` of `Sched m`. Zero when the
anchor is not a block of the universe.

The clause `d ≤ round` keeps truncated subtraction from counting round
`0` once per excess `d`; inside a run the anchor's round exceeds the
interval and the clause is vacuous. -/
def observed (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (U : R.Universe) (A : BlockId) (m : ℕ) (hm : 0 < m) (hmax : m ≤ P.maxLeaders) : ℕ :=
  if hA : A ∈ R.ids U then
    ((Finset.range (P.interval + 1) ×ˢ Finset.range m).filter (fun dl : ℕ × ℕ =>
      dl.1 ≤ (R.block U A).round ∧
      R.SlotDirect (Sched getLeader hk m hm hmax) U (R.historyView U A hA)
        (m * ((R.block U A).round - dl.1) + dl.2))).card
  else 0

/-- **The expected count** (`ExpectedCommits`): the decidable slots of the
window under count `m`, `interval − waveLength + 1` rounds of `m` slots.
Below `waveLength ≤ interval` the subtraction truncates; the results
that bound the count carry that hypothesis. -/
def expected (R : BaseRule Validator BlockId Payload) (P : Params) (m : ℕ) : ℕ :=
  (P.interval - R.waveLength + 1) * m

namespace Aimd

/-- **Additive increase, multiplicative decrease.** A healthy window
raises the count by one, capped at `maxLeaders`, and resets the back-off;
an unhealthy one lowers it by `2^backoff`, floored at one, and doubles
the next step. -/
def update (P : Params) (m backoff : ℕ) (healthy : Bool) : ℕ × ℕ :=
  if healthy then (min (m + 1) P.maxLeaders, 0)
  else (max (m - 2 ^ backoff) 1, backoff + 1)

/-- **The paper's `UpdateLeaders`** as an update rule: healthy when
`den · observed ≥ num · expected`. A count outside `[1, maxLeaders]`
cannot arise from a run; the rule returns the initial state there so
that it is total. -/
def rule (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) :
    UpdateRule R :=
  fun m backoff U _V A =>
    if hm : 0 < m ∧ m ≤ P.maxLeaders then
      update P m backoff
        (decide (P.num * expected R P m ≤
          P.den * observed R P getLeader hk U A m hm.1 hm.2))
    else (1, 0)

end Aimd

/-- The constant rule: reconfigure nothing. The conservativity anchor —
under it the arc collapses onto the base development at one leader. -/
def constRule (R : BaseRule Validator BlockId Payload) : UpdateRule R :=
  fun m b _ _ _ => (m, b)

end Barnacle

end LeanDag
