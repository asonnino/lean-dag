import LeanDag.Steelhead.Helpers.BlueBottlePair
/-!
# The `5f + 1` pair — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/BlueBottlePair.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ U _
  exact ⟨pairHandover, halvesLawful, pairAgreement, pairAgreesOnRungsAndTie, pairWavesDiffer⟩

end BlueBottlePair

end Steelhead

end LeanDag
