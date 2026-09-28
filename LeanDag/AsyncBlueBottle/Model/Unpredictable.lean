import LeanDag.AsyncBlueBottle.Model.Good
import LeanDag.MahiMahi.Model.Unpredictable
/-!
# Async BlueBottle — the unpredictable-leader clause

The hypothesis under which the rule is live with no network assumption
(`async-bluebottle.md` §6), Mahi-Mahi's clause at a fixed three-round
wave: in every stretch of `c` consecutive slots, the schedule names a
validator whose block the DAG actually committed. It relates the
schedule to the DAG rather than fixing a target set, since under
asynchrony only the DAG's shape guarantees a commit. The paper supplies
it by a threshold-signature common coin with an asynchronous key setup
(Appendix G.1), which the model does not formalize: its effect is this
clause. Both the single-hit and run forms
quantify only below a horizon `N`, since `good` is empty past some round
in any finite DAG. Definitions only.
-/

namespace LeanDag

namespace AsyncBlueBottle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-! Measurability reads Mahi-Mahi's `AgreeUpto`: two universes with the
same ids and blocks at rounds up to `d`. -/

section Slots

variable [S : Slots Validator]

/-- **The single-hit form.** In every window of `c` slots whose decision
rounds lie below the horizon `N`, the schedule names a committed
candidate at least once. -/
def UnpredictableWithin (U : BlockUniverse Validator BlockId Payload) (c N : ℕ) : Prop :=
  ∀ k,
    -- the window's last decision round lies below the horizon
    (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound (k + c) ≤ N →
    -- some slot of the window is led by a validator whose block commits
    ∃ k', k ≤ k' ∧ k' < k + c ∧ S.leader k' ∈ good U k'

/-- **The run form.** In every window of `c` slots below the horizon, a
run of `d` consecutive slots whose leaders are all committed candidates.
The bound reads the last slot of the latest possible run, `k + c + d − 1`,
so that small universes are not vacuously covered. -/
def UnpredictableRunWithin (U : BlockUniverse Validator BlockId Payload) (c d N : ℕ) : Prop :=
  ∀ k,
    -- the latest run's last decision round lies below the horizon
    (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound (k + c + d - 1) ≤ N →
    -- some run of d slots starting in the window is led by committed candidates
    ∃ k', k ≤ k' ∧ k' < k + c ∧ ∀ i < d, S.leader (k' + i) ∈ good U (k' + i)

end Slots

end AsyncBlueBottle

end LeanDag
