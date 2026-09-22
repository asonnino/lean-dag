import LeanDag.AsyncBlueBottle.Safety.Statement
import LeanDag.AsyncBlueBottle.Helpers.Decision
/-!
# Safety — proof

Generated proof layer; not part of the audit surface. Each conjunct is
one helper: the arithmetic core of `Helpers/Rules.lean` for ABB1–ABB4′,
and `decided_unique` at `asyncBlueBottleLaws` for ABB5.
-/

namespace LeanDag

namespace AsyncBlueBottle

namespace Safety

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro L r hLr hc hk
    exact not_directSkip_of_directCommit hLr hc hk
  · intro r L₁ L₂ h₁ h₂ hcr hrr
    exact eq_of_directCommit h₁ h₂ hcr hrr
  · intro a r L A hk hLc hLr
    exact not_weakLink_of_directSkip hk hLc hLr A
  · intro L r A h hA hround
    exact weakLink_of_directCommit h hA hround
  · intro r L₁ L₂ A h₁ ht hcr hrr
    exact eq_of_directCommit_of_weakLink h₁ ht hcr hrr
  · intro a r
    exact directSkip_iff_mahiMahi
  · intro V₁ V₂ k v₁ v₂ h₁ h₂
    exact AnchoredRule.decided_unique asyncBlueBottleLaws trivial h₁ V₂ v₂ h₂

end Safety

end AsyncBlueBottle

end LeanDag
