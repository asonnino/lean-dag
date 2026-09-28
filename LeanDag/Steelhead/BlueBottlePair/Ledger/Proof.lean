import LeanDag.Steelhead.BlueBottlePair.Ledger.Statement
import LeanDag.Steelhead.Ledger.Proof
import LeanDag.Steelhead.Helpers.BlueBottlePair
/-!
# The `5f + 1` pair's ledger — proof

Generated proof layer; not part of the audit surface. SH13 at the pair's
composite, its laws `blueBottlePairLaws`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Ledger

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U
  have hg := Steelhead.Ledger.holds Validator BlockId Payload U
    (blueBottlePairAnchored Validator BlockId Payload)
  exact ⟨fun V₁ V₂ n g₁ g₂ h₁ h₂ => hg.1 V₁ V₂ n g₁ g₂ blueBottlePairLaws h₁ h₂, hg.2⟩

end Ledger

end BlueBottlePair

end Steelhead

end LeanDag
