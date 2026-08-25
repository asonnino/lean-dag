import LeanDag.BlackMarlin.Ledger.Statement
import LeanDag.BlackMarlin.Helpers.Ledger

/-!
# Black Marlin — the delivered order, proved

Generated proof layer; not part of the audit surface. Each conjunct is
one helper of `Helpers/Ledger.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Ledger

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ρ M X Y hM hMr hX hY
    exact coneAnchors_subsingleton hM hMr X hX Y hY
  · intro ρ C X Y hc hX hY
    exact coneAnchors_subsingleton_of_correct hc X hX Y hY
  · intro f₁ f₂ ρ M h₁ h₂
    exact block_eq_of_succ h₁ h₂
  · intro f₁ f₂ ρ d h hdef
    exact block_eq_of_add d ρ h hdef
  · intro f₁ f₂ σ L₁ L₂ h₁ h₂ hc₁ hc₂
    exact block_eq_of_committed h₁ h₂ hc₁ hc₂
  · intro L C ρ h hC hCr
    exact coneAnchors_succ_nonempty_of_committed h hC hCr
  · intro f n m h
    exact ledgerSet_mono f h
  · intro f₁ f₂ n h
    exact ledgerSet_agree h
  · intro f b ρ₁ ρ₂ h₁ h₂
    exact outputAt_unique h₁ h₂
  · intro f₁ f₂ n b ρ h hρ ho
    exact outputAt_agree h hρ ho
  · intro f ρ L b hL hb
    exact mem_ledgerSet_of_block f hL hb

end Ledger

end BlackMarlin

end LeanDag
