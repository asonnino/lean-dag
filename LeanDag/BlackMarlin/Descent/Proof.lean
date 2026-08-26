import LeanDag.BlackMarlin.Descent.Statement
import LeanDag.BlackMarlin.Helpers.Descent

/-!
# Black Marlin — the descent computed, proved

Generated proof layer; not part of the audit surface. Each conjunct is
one helper of `Helpers/Descent.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Descent

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B A hB h
    exact ⟨descend_mem_ids hB h,
      (mem_anchorsOf.mp (mem_maxAnchor.mp (descend_mem h)).1).2,
      (mem_anchorsOf.mp (mem_maxAnchor.mp (descend_mem h)).1).1,
      round_descend h, descend_round_lt hB h⟩
  · intro B h
    exact descend_isSome h
  · intro B hB haB
    exact ⟨fun _ _ h => flushRecord_isAnchor hB haB h,
      fun _ _ _ hL hM => flushRecord_step hB hL hM,
      fun _ _ hM hcone => flushRecord_dense hB hM hcone⟩
  · intro B M σ ρ hB h hρ
    exact flushRecord_suffix hB h hρ
  · intro B₁ B₂ M σ ρ h₁ h₂ hm₁ hm₂ hρ
    exact flushRecord_agree h₁ h₂ hm₁ hm₂ hρ

end Descent

end BlackMarlin

end LeanDag
