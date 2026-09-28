import LeanDag.Steelhead.Period.Statement
import LeanDag.Steelhead.Helpers.Period
/-!
# The period sequence at any rules — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Period.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Period

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U Ra R p good wa I K _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro coin upd k₀ V₁ V₂ j st₁ st₂ hRa h₁ h₂
    exact periodAt_unique hRa h₁ h₂
  · intro coin known upd k₀ N V₁ V₂ per₁ per₂ k v₁ v₂ hRa hR hv hN hk h₁ h₂ d₁ d₂
    exact ⟨adaptive_periods_agree hRa hR hv h₁ h₂,
      adaptive_decided_unique hRa hR hv hN hk h₁ h₂ d₁ d₂⟩
  · intro coin upd k₀ V j st hv hp hall
    exact exists_periodAt_succ hv hp hall
  · intro coin upd k₀ V c N hleast hgc hwa hv hI h₀ hK hupd hrun hV j hN
    exact periodAt_of_clause hleast hgc hwa hv hI h₀ hK hupd hrun hV j hN
  · intro coin upd k₀ V j i next' last' st A hA hp ha hadv h
    exact periodAt_one_of_anchor hp ha hadv h
  · intro j k hk hI
    exact two_async_rounds hk hI
  · intro coin upd k₀ V j st h₀ hK hupd hp
    exact periodAt_mem_range h₀ hK hupd hp
  · intro coin upd k₀ V j st hca hR hp
    exact decided_of_lt_next hca hR hp
  · intro coin upd k₀ V j s st hca hR hid hp h₁ hund
    exact stalled_below_undecided hca hR hid hp h₁ hund
  · intro k top hk hK hwa hI htop
    exact window_resolves hk hK hwa hI htop
  · intro j k r
    exact controlRounds j k r
  · intro coin j k V₁ V₂ i v₁ v₂ hRa h₁ h₂
    exact controlDecided_unique hRa h₁ h₂
  · intro coin upd k₀ V i next' last' st A hA hI hp ha hadv
    exact periodAt_warmUp hI hp ha hadv
  · intro k top hk hI htop
    exact two_async_rounds_in_window hk hI htop
  · intro coin upd k₀ V j st h₀ hupd hp
    exact periodAt_dvd h₀ hupd hp
  · intro coin known per j i hI hdvd hj
    exact controlRound_adaptive_async hI hdvd hj
  · intro coin upd k₀ V j st' hp
    exact periodAt_gated hp
  · intro coin upd k₀ V per s j₁ i₁ b A hsl hal hsll hall hac hgc hws hwa hid hkind hI hper hlead
      h₁ hs hA hb hgood hV
    exact output_liveness hsl hal hsll hall hac hgc hws hwa hid hkind hI hper hlead h₁ hs hA hb
      hgood hV
  · intro coin upd k₀ V per c N hsl hal hsll hall hac hgc hws hwa hid hkind hI hlead h₀ hK hupd
      hcK hrun hV hper s h₁ hN
    exact all_decided hsl hal hsll hall hac hgc hws hwa hid hkind hI hlead h₀ hK hupd hcK hrun hV
      hper s h₁ hN
  · intro coin upd k₀ V per s j b hsl hal hsll hall hac hgc hws hwa hid hkind hI hlead hper h₁ hs
      hk hkI hgood hb hgoodb hV
    exact output_liveness_of_runs hsl hal hsll hall hac hgc hws hwa hid hkind hI hlead hper h₁ hs
      hk hkI hgood hb hgoodb hV

end Period

end Steelhead

end LeanDag
