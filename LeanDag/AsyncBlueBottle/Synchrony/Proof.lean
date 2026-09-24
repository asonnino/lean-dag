import LeanDag.AsyncBlueBottle.Synchrony.Statement
import LeanDag.AsyncBlueBottle.Helpers.Synchrony
/-!
# Partial synchrony, recovered — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Synchrony.lean`.
-/

namespace LeanDag

namespace AsyncBlueBottle

namespace Synchrony

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U
  refine ⟨?_, ?_⟩
  · intro T R k hT hcard hs hR hpop0 hpop1 hpopd hlead
    exact good_of_synchronisedOn hT hcard hs hR hpop0 hpop1 hpopd hlead
  · intro T c N hT hcard hs hpop fair
    exact unpredictableWithin_of_synchronisedOn hT hcard hs hpop fair

end Synchrony

end AsyncBlueBottle

end LeanDag
