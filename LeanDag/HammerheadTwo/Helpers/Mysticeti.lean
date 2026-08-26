import LeanDag.HammerheadTwo.Model.Rule
import LeanDag.History
import LeanDag.Liveness

/-!
# Mysticeti instance helpers

Not part of the audit surface. The one construction the Mysticeti
instantiation needs beyond core theorems applied: a block's causal
history as a `View`, closed under references because reachability is
transitive — the construction of `viewAt` (`ViewPace.lean`), for a
single root.
-/

namespace LeanDag

namespace HammerheadTwo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [Faults Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- The causal history of a block of the universe, as a view. -/
def historyViewOf (U : BlockUniverse Validator BlockId Payload) (A : BlockId)
    (hA : A ∈ U.ids) : LeanDag.View Validator BlockId Payload U where
  ids := history U A
  subset_ids := history_subset_ids hA
  complete := fun _ hi _ hj =>
    (mem_history_iff hA).mpr (((mem_history_iff hA).mp hi).trans (Reaches.single hj))

end HammerheadTwo

end LeanDag
