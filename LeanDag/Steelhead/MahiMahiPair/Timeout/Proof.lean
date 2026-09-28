import LeanDag.Steelhead.MahiMahiPair.Timeout.Statement
import LeanDag.Steelhead.Helpers.MahiMahiPair.Timeout
/-!
# The `3f + 1` pair's mistimed leader timeout — proof

Generated proof layer; not part of the audit surface. Each conjunct is the
helper of the same name in `Helpers/MahiMahiPair/Timeout.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

namespace Timeout

theorem holds : Statement := by
  refine ⟨?_, ?_⟩
  · intro n f hn hf
    exact ⟨certProb_self, certProb_pred hn hf⟩
  · intro p _ hp1
    exact tsum_tail_eq_inv hp1

end Timeout

end MahiMahiPair

end Steelhead

end LeanDag
