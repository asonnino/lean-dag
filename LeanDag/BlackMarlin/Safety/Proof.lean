import LeanDag.BlackMarlin.Safety.Statement
import LeanDag.BlackMarlin.Helpers.Decision

/-!
# Black Marlin — safety of the commit rule, proved

Generated proof layer; not part of the audit surface. Each conjunct is
one helper: `eq_of_isAnchor_of_supported` for BM1, `reaches_of_supported`
for BM2, `quorum_authorsAt_of_lt` for BM3, `committed_of_committedIn`
with `mem_ids_of_committedIn` for BM4, and `reaches_of_committed_of_le`
for BM5 and BM6, applied to whichever of the two rounds is the lower.
BM7 unfolds both sides.
-/

namespace LeanDag

namespace BlackMarlin

namespace Safety

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r L₁ L₂ ha₁ ha₂ hs₁ hs₂
    exact eq_of_isAnchor_of_supported ha₁ ha₂ hs₁ hs₂
  · intro L r c hs hc hcr
    exact reaches_of_supported hs hc hcr
  · intro c r hc hlt
    exact quorum_authorsAt_of_lt hc hlt
  · intro V L r h
    exact ⟨committed_of_committedIn h, mem_ids_of_committedIn h⟩
  · intro V₁ V₂ L₁ L₂ r₁ r₂ h₁ h₂
    rcases Nat.le_total r₁ r₂ with hr | hr
    · rcases reaches_of_committed_of_le (committed_of_committedIn h₁)
        (committed_of_committedIn h₂) hr with heq | hre
      · exact Or.inl heq
      · exact Or.inr (Or.inr hre)
    · rcases reaches_of_committed_of_le (committed_of_committedIn h₂)
        (committed_of_committedIn h₁) hr with heq | hre
      · exact Or.inl heq.symm
      · exact Or.inr (Or.inl hre)
  · intro V₁ V₂ L₁ L₂ r₁ r₂ h₁ h₂ hr
    rcases reaches_of_committed_of_le (committed_of_committedIn h₁)
      (committed_of_committedIn h₂) hr with heq | hre
    · exact heq ▸ Finset.Subset.refl _
    · exact history_subset_of_reaches h₂.1.1 hre
  · intro r L
    constructor
    · intro h
      exact ⟨h.1, by simpa using h.2.1, by simpa using h.2.2⟩
    · intro h
      exact ⟨h.1, by simpa using h.2.1, by simpa using h.2.2⟩

end Safety

end BlackMarlin

end LeanDag
