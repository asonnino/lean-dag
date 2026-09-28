import LeanDag.Steelhead.BlueBottlePair.Period.Statement
import LeanDag.Steelhead.Helpers.BlueBottlePair.Period
/-!
# The `5f + 1` pair's period sequence — proof

Generated proof layer; not part of the audit surface. Each conjunct is a
helper of `Helpers/BlueBottlePair/Period.lean`, or the generic one with
Async BlueBottle's laws.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Period

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U I K _
  refine ⟨periodHypotheses, ?_, ?_, ?_⟩
  · intro coin upd k₀ V₁ V₂ j st₁ st₂ h₁ h₂
    exact periodAt_unique AsyncBlueBottle.asyncBlueBottleLaws h₁ h₂
  · intro coin upd k₀ V c N hI h₀ hK hupd hrun hV j hN
    exact periodAt_of_clause hI h₀ hK hupd hrun hV j hN
  · intro coin upd k₀ V per c N hid hkind hI hlead h₀ hK hupd hcK hrun hV hper s h₁ hN
    exact all_decided hid hkind hI hlead h₀ hK hupd hcK hrun hV hper s h₁ hN

end Period

end BlueBottlePair

end Steelhead

end LeanDag
