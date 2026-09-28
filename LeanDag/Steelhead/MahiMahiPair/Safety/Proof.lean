import LeanDag.Steelhead.MahiMahiPair.Safety.Statement
import LeanDag.Steelhead.Safety.Proof
import LeanDag.Steelhead.Helpers.Decision
/-!
# The `3f + 1` pair's safety — proof

Generated proof layer; not part of the audit surface. SH-MM1 is
Mahi-Mahi's certificate lemmas at the slot's wave. SH-MM2, SH-MM3 and
SH-MM5a are the generic claims (`Safety/Statement.lean`) at
`steelheadAnchored w` and at Mahi-Mahi's rule on the chain schedule, the
tie-break having a choice since there is no tie. SH-MM4 is definitional
up to the two kind lemmas and Mahi-Mahi's wave-three correspondence,
whose converse `decided_of_core_decided` mirrors it.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

namespace Safety

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U w ws wa
  have hg := Steelhead.Safety.holds Validator BlockId Payload U
    (steelheadAnchored Validator BlockId Payload w)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a r κ L hw h _ hLc hLr
    exact MahiMahi.certificates_eq_empty_of_directSkip (by omega) h hLc hLr
  · intro r κ L₁ L₂ hw h₁ h₂ hc hr
    exact MahiMahi.eq_of_certificates_nonempty (by omega) h₁ h₂ hc hr
  · intro L r κ hw h A hA hAr
    exact MahiMahi.certifiedIn_of_directCommit h hA (by unfold MahiMahi.decisionRoundAt; omega)
  · intro V₁ V₂ k v₁ v₂ hw h₁ h₂
    exact hg.1 V₁ V₂ k v₁ v₂ (steelheadLaws hw) h₁ h₂
  · intro V₁ V₂ k L hw hL hc
    exact hg.2.1 V₁ V₂ k L (steelheadLaws hw) (fun hi h => exists_least hi h) hL hc
  · exact ⟨fun _ => rfl, wavelength_periodicKind, periodicKind_one⟩
  · intro V k v
    exact ⟨MahiMahi.core_decided_of_decided, decided_of_core_decided⟩
  · intro coin V₁ V₂ r v₁ v₂ hwa h₁ h₂
    exact (Steelhead.Safety.holds Validator BlockId Payload U
      (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa)).2.2.2 coin V₁ V₂ r v₁ v₂
      (MahiMahi.mahiMahiLaws (by omega)) h₁ h₂
  · intro coin V r L hid hr hlead
    exact direct_agrees_with_chain hid hr hlead

end Safety

end MahiMahiPair

end Steelhead

end LeanDag
