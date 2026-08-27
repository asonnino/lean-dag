import LeanDag.HammerheadTwo.Model.Rule
import LeanDag.Nemo.History
import LeanDag.Nemo.Liveness

/-!
# Nemo instance helpers

Not part of the audit surface. The crash-fault universe's history as a
`View`, closed under references because reachability is transitive —
`historyViewOf` for `Nemo.Universe`.
-/

namespace LeanDag

namespace HammerheadTwo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- The causal history of a block of a crash-fault universe, as a view. -/
def nemoHistoryViewOf (U : Nemo.Universe Validator BlockId Payload) (A : BlockId)
    (hA : A ∈ U.ids) : Nemo.View Validator BlockId Payload U where
  ids := Nemo.history U A
  subset_ids := U.causal.history_subset_ids hA
  complete := fun _ hi _ hj =>
    (Nemo.mem_history_iff hA).mpr (((Nemo.mem_history_iff hA).mp hi).trans (ReachesFrom.single hj))

end HammerheadTwo

end LeanDag
