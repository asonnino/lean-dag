import LeanDag.MahiMahi.Synchrony.Statement
import LeanDag.MahiMahi.Helpers.Synchrony

/-!
# Partial synchrony, recovered — proof

Generated proof layer; not part of the audit surface.
-/

namespace LeanDag

namespace MahiMahi

namespace Synchrony

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U w
  refine ⟨?_, ?_⟩
  · intro T R k hw hT hcard hs hR hpop0 hpop1 hpopd hlead
    exact good_of_synchronisedOn hw hT hcard hs hR hpop0 hpop1 hpopd hlead
  · intro T c N hw hT hcard hs hpop fair
    exact unpredictableWithin_of_synchronisedOn hw hT hcard hs hpop fair

end Synchrony

end MahiMahi

end LeanDag
