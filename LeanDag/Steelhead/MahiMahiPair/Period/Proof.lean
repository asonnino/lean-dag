import LeanDag.Steelhead.MahiMahiPair.Period.Statement
import LeanDag.Steelhead.Helpers.MahiMahiPair.Period
/-!
# The `3f + 1` pair's period sequence — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the generic helper of the same name in `Helpers/Period.lean`, its laws and
clauses discharged by Mahi-Mahi's (`Helpers/MahiMahiPair/Period.lean`), or
that file's own helper of the name.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

namespace Period

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U ws wa I K _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro coin upd k₀ V₁ V₂ w j st₁ st₂ hwa h₁ h₂
    exact periodAt_unique (MahiMahi.mahiMahiLaws (by omega)) h₁ h₂
  · intro coin known upd k₀ N V₁ V₂ per₁ per₂ k v₁ v₂ hws hwa hN hk h₁ h₂ d₁ d₂
    have hw := wavelength_two_le (by omega : 2 ≤ ws) (by omega : 2 ≤ wa)
    exact ⟨adaptive_periods_agree (MahiMahi.mahiMahiLaws (by omega)) (steelheadLaws hw)
      (viewLaws_steelhead hw) h₁ h₂, adaptive_decided_unique (MahiMahi.mahiMahiLaws (by omega))
      (steelheadLaws hw) (viewLaws_steelhead hw) hN hk h₁ h₂ d₁ d₂⟩
  · intro coin upd k₀ V w j st hw hp hall
    exact exists_periodAt_succ (viewLaws_steelhead hw) hp hall
  · intro coin upd k₀ V w c N hwa hI hw h₀ hK hupd hrun hV j hN
    exact periodAt_of_clause (leastLinked_mahiMahi wa) (goodCommits_mahiMahi wa)
      (by change wa - 1 + 1 ≤ wa; omega) (viewLaws_steelhead hw) hI h₀ hK hupd hrun hV j
      (by unfold MahiMahi.decisionRoundAt at hN; omega)
  · intro coin upd k₀ V w j i next' last' st A hA hp ha hadv h
    exact periodAt_one_of_anchor hp ha hadv h
  · intro j k hk hI
    exact two_async_rounds hk hI
  · intro coin upd k₀ V w j st h₀ hK hupd hp
    exact periodAt_mem_range h₀ hK hupd hp
  · intro coin upd k₀ V w j st hw hp
    exact decided_of_lt_next (commitLaws_mahiMahi wa) (steelheadLaws hw) hp
  · intro coin upd k₀ V w j s st hw hid hp h₁ hund
    exact stalled_below_undecided (commitLaws_mahiMahi wa) (steelheadLaws hw) hid hp h₁ hund
  · intro k top hk hK hwa hI htop
    exact window_resolves hk hK hwa hI htop
  · intro j k r
    exact controlRounds j k r
  · intro coin j k V₁ V₂ i v₁ v₂ hwa h₁ h₂
    exact controlDecided_unique (MahiMahi.mahiMahiLaws (by omega)) h₁ h₂
  · intro coin upd k₀ V w i next' last' st A hA hI hp ha hadv
    exact periodAt_warmUp hI hp ha hadv
  · intro k top hk hI htop
    exact two_async_rounds_in_window hk hI htop
  · intro coin upd k₀ V w j st h₀ hupd hp
    exact periodAt_dvd h₀ hupd hp
  · intro coin known per j i hI hdvd hj
    exact controlRound_adaptive_async hI hdvd hj
  · intro coin upd k₀ V w j st' hp
    exact periodAt_gated hp
  · intro coin upd k₀ V per s j₁ i₁ b A hws hle hwa hid hkind hI hper hlead h₁ hs hA hb hgood hV
    exact output_liveness hws hle hwa hid hkind hI hper hlead h₁ hs hA hb hgood hV
  · intro coin upd k₀ V per c N hws hle hwa hid hkind hI hlead h₀ hK hupd hcK hrun hV hper s h₁ hN
    exact all_decided hws hle hwa hid hkind hI hlead h₀ hK hupd hcK hrun hV hper s h₁ hN
  · intro coin upd k₀ V per s j b hws hle hwa hid hkind hI hlead hper h₁ hs hk hkI hgood hb hgoodb
      hV
    exact output_liveness_of_runs hws hle hwa hid hkind hI hlead hper h₁ hs hk hkI hgood hb hgoodb
      hV

end Period

end MahiMahiPair

end Steelhead

end LeanDag
