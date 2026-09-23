import LeanDag.Steelhead.MahiMahiPair.Broadcast.Statement
import LeanDag.Steelhead.Broadcast.Proof
import LeanDag.Steelhead.Helpers.Decision
/-!
# The `3f + 1` pair's atomic broadcast — proof

Generated proof layer; not part of the audit surface. Every conjunct is
the generic claim (`Broadcast/Statement.lean`) at `steelheadAnchored w`,
with `steelheadLaws` where the claim reads the laws.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

namespace Broadcast

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U w
  obtain ⟨hagree, hint, hval, hevent, horder⟩ := Steelhead.Broadcast.holds Validator BlockId
    Payload U (steelheadAnchored Validator BlockId Payload w)
  exact ⟨fun V₁ V₂ n m g₁ g₂ b hw => hagree V₁ V₂ n m g₁ g₂ b (steelheadLaws hw), hint, hval,
    hevent, fun V₁ V₂ n g₁ g₂ b b' k k' hw => horder V₁ V₂ n g₁ g₂ b b' k k' (steelheadLaws hw)⟩

end Broadcast

end MahiMahiPair

end Steelhead

end LeanDag
