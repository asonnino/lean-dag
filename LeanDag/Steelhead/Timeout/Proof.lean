import LeanDag.Steelhead.Timeout.Statement
import LeanDag.Steelhead.Helpers.Timeout
/-!
# The mistimed leader timeout — proof

Generated proof layer; not part of the audit surface. Each conjunct is the
helper of the same name in `Helpers/Timeout.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Timeout

theorem holds : Statement := by
  refine ⟨?_, ?_⟩
  · intro n f hn hf
    exact ⟨certProb_self, certProb_pred hn hf⟩
  · intro p _ hp1
    exact tsum_tail_eq_inv hp1

end Timeout

end Steelhead

end LeanDag
