import LeanDag.Barnacle.Mysticeti.Statement
import LeanDag.Liveness

/-!
# Barnacle over Mysticeti — proof

Generated proof layer; not part of the audit surface. Every law is a
core theorem applied: the view structure's own fields, `rfl` for the
two id equations, `decided_agree` (M6), `Decided.directCommit` and
`isLeaderBlock_of_decided`.
-/

namespace LeanDag

namespace Barnacle

namespace Mysticeti

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _
  exact
    { view_subset := fun V => V.subset_ids
      view_complete := fun V => V.complete
      full_ids := fun _ => rfl
      historyView_ids := fun _ _ _ => rfl
      agree := fun _ {_} _ _ _ _ _ h₁ h₂ => decided_agree h₁ h₂
      decided_of_directCommitIn := fun _ {_} _ _ _ hL hdc => Decided.directCommit hL hdc
      candidates := fun _ {_} _ _ _ h => isLeaderBlock_of_decided h }

end Mysticeti

end Barnacle

end LeanDag
