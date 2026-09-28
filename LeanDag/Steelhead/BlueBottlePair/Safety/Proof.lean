import LeanDag.Steelhead.BlueBottlePair.Safety.Statement
import LeanDag.Steelhead.Helpers.Safety
import LeanDag.Steelhead.Helpers.BlueBottlePair
/-!
# The `5f + 1` pair's conservativity — proof

Generated proof layer; not part of the audit surface. Both halves are SH4
(`compose_decided_iff`) at the family, whose rung count and tie-break
agree.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Safety

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U
  exact ⟨fun hkind V k v => compose_decided_iff (rules := blueBottlePair Validator BlockId Payload)
      pair_rungs pair_tie hkind,
    fun hkind V k v => compose_decided_iff (rules := blueBottlePair Validator BlockId Payload)
      pair_rungs pair_tie hkind⟩

end Safety

end BlueBottlePair

end Steelhead

end LeanDag
