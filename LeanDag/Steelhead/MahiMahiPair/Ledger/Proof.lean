import LeanDag.Steelhead.MahiMahiPair.Ledger.Statement
import LeanDag.Steelhead.Ledger.Proof
import LeanDag.Steelhead.Helpers.Decision
/-!
# The `3f + 1` pair's ledger — proof

Generated proof layer; not part of the audit surface. Both conjuncts are
the generic ledger claims (`Ledger/Statement.lean`) at `steelheadAnchored
w`, whose laws `steelheadLaws` gives at waves of two rounds or more.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

namespace Ledger

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U w
  have hg := Steelhead.Ledger.holds Validator BlockId Payload U
    (steelheadAnchored Validator BlockId Payload w)
  exact ⟨fun V₁ V₂ n g₁ g₂ hw h₁ h₂ => hg.1 V₁ V₂ n g₁ g₂ (steelheadLaws hw) h₁ h₂, hg.2⟩

end Ledger

end MahiMahiPair

end Steelhead

end LeanDag
