import LeanDag.Steelhead.BlueBottlePair.Broadcast.Statement
import LeanDag.Steelhead.Broadcast.Proof
import LeanDag.Steelhead.Helpers.BlueBottlePair
/-!
# The `5f + 1` pair's atomic broadcast — proof

Generated proof layer; not part of the audit surface. SH17 at the pair's
composite, its laws `blueBottlePairLaws` where a claim reads them.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Broadcast

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U
  obtain ⟨hagree, hint, hval, hevent, horder⟩ := Steelhead.Broadcast.holds Validator BlockId
    Payload U (blueBottlePairAnchored Validator BlockId Payload)
  exact ⟨fun V₁ V₂ n m g₁ g₂ b => hagree V₁ V₂ n m g₁ g₂ b blueBottlePairLaws, hint, hval, hevent,
    fun V₁ V₂ n g₁ g₂ b b' k k' => horder V₁ V₂ n g₁ g₂ b b' k k' blueBottlePairLaws⟩

end Broadcast

end BlueBottlePair

end Steelhead

end LeanDag
