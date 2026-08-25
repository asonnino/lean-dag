import LeanDag.BlackMarlin.Repair.Statement
import LeanDag.BlackMarlin.Helpers.Repair
import LeanDag.BlackMarlin.Helpers.Liveness

/-!
# Black Marlin — the repair, proved

Generated proof layer; not part of the audit surface. Each conjunct is
one helper of `Helpers/Repair.lean`; BMP6 is `Iff.rfl`, `Committed`
being that conjunction by definition.
-/

namespace LeanDag

namespace BlackMarlin

namespace Repair

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U
  refine ⟨?_, ?_, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · intro B A C hA hC
    exact suppCandidates_subsingleton A hA C hC
  · intro B L h hne
    exact descendSupp_supported h hne
  · intro B h
    exact descendSupp_eq_descend h
  · intro B
    exact descendSupp_isSome_iff
  · intro B L L' h h'
    exact descendSupp_round_eq h h'
  · intro f₁ f₂ ρ hp₁ hp₂ hs₁ hs₂ hex
    exact block_eq_of_supportPreferring hp₁ hp₂ hs₁ hs₂ hex
  · intro L ρ
    exact Iff.rfl
  · intro B L h
    exact (mem_suppAnchorsOf.mp (descendS_mem h).1).2
  · intro B L ρ hB hc hmem
    exact descentSUpto_reaches _ B hB (le_refl _) L ρ hc hmem
  · intro B₁ B₂ M σ ρ h₁ h₂ hm₁ hm₂ hρ
    exact flushRecordS_agree h₁ h₂ hm₁ hm₂ hρ
  · intro B h
    exact descendS_isSome h
  · intro B L hB h
    exact descendS_round_lt hB h
  · intro T R r hcard hfair
    exact recurrence hcard hfair

end Repair

end BlackMarlin

end LeanDag
