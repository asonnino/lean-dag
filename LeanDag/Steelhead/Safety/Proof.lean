import LeanDag.Steelhead.Safety.Statement
import LeanDag.Steelhead.Helpers.Safety
/-!
# Safety at any lawful rule — proof

Generated proof layer; not part of the audit surface. SH2 and SH5a are
the relation's `decided_unique`, SH3 and SH4 the helpers of
`Helpers/Safety.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Safety

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U R
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro V₁ V₂ k v₁ v₂ hl h₁ h₂
    exact AnchoredRule.decided_unique hl trivial h₁ V₂ v₂ h₂
  · intro V₁ V₂ k L hl hleast hL hc
    exact handover hl hleast hL hc
  · intro rules κ hr ht hkind V k v
    exact compose_decided_iff hr ht hkind
  · intro coin V₁ V₂ r v₁ v₂ hl h₁ h₂
    exact AnchoredRule.decided_unique (S := chainSlots coin) hl trivial h₁ V₂ v₂ h₂

end Safety

end Steelhead

end LeanDag
