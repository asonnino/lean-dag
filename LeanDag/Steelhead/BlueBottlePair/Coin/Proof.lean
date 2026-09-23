import LeanDag.Steelhead.BlueBottlePair.Coin.Statement
import LeanDag.Steelhead.Helpers.BlueBottlePair.Coin
/-!
# The `5f + 1` pair's coin — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/BlueBottlePair/Coin.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Coin

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ U I K _
  refine ⟨coinHypotheses, fun T r h => floor_le_commitProb h, ?_, ?_, ?_⟩
  · intro T V d s b M hs hpop
    exact ⟨expected_firstGoodBlock_le hpop, fun g hM hV => decided_of_firstGoodBlock hs hM hV⟩
  · intro T upd k₀ known d q s M hKI hwaI hq h₁ h₀ hK hupd hpop
    exact undecidedProb_le hKI hwaI hq h₀ hK hupd h₁ hpop
  · intro _ _ U T upd k₀ known q s hKI hwaI hq h₁ h₀ hK hupd hpop
    exact decidedAlmostSurely hKI hwaI hq h₀ hK hupd h₁ hpop

end Coin

end BlueBottlePair

end Steelhead

end LeanDag
