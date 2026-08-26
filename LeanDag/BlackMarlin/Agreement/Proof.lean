import LeanDag.BlackMarlin.Agreement.Statement
import LeanDag.BlackMarlin.Helpers.Agreement

/-!
# Black Marlin — agreement, proved

Generated proof layer; not part of the audit surface.
`history_subset_of_committed` for BMA1, `Pace.committedIn_local` for
BMA2, `Pace.agreement` for BMA3, and the fairness clause unfolded for
BMA4.
-/

namespace LeanDag

namespace BlackMarlin

namespace Agreement

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U
  refine ⟨?_, ?_, ?_⟩
  · intro V₁ V₂ A₁ A₂ B r₁ r₂ h₁ h₂ hr hB
    exact history_subset_of_committed (committed_of_committedIn h₁)
      (committed_of_committedIn h₂) hr hB
  · intro T r hfair
    obtain ⟨r', hr', hrun⟩ := hfair r
    exact ⟨r', hr', by simpa using hrun 0 (by omega), by simpa using hrun 1 (by omega)⟩
  · intro T N pc
    refine ⟨?_, ?_⟩
    · intro R r hT hcard hgst hto hR hN hlead hlead1
      exact pc.committedIn_local hT hcard hgst hto hR hN hlead hlead1
    · intro R r ρ V A B hT hcard hgst hto hR hN hρ hlead hlead1 hA hB
      exact pc.agreement hT hcard hgst hto hR hN hlead hlead1 hρ hA hB

end Agreement

end BlackMarlin

end LeanDag
