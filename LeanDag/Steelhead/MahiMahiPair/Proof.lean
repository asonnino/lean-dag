import LeanDag.Steelhead.Helpers.MahiMahiPair
/-!
# The `3f + 1` pair — proof

Generated proof layer; not part of the audit surface. SH-MM16c is
definitional and SH-MM19 is the helper of the same name.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _
  exact ⟨steelheadAnchored_eq_compose, periodicClass⟩

end MahiMahiPair

end Steelhead

end LeanDag
