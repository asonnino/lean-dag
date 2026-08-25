import LeanDag.BlackMarlin.ViewOrder.Statement
import LeanDag.BlackMarlin.Order.Proof
import LeanDag.BlackMarlin.Ledger.Proof

/-!
# Black Marlin — the delivered order at a validator's view, proved

`ViewOrder/Statement.lean` states it. BMT1 is `no_equivocation` read at
an anchor; BMT2 is BMT1 handed to BMD3; BMT3 is BMT1 pointwise handed to
BMO2. Nothing here is new work at the level of the DAG — what was
missing was that a reliable anchor leaves the descent no choice at all,
which is a fact about the universe and therefore holds of every view.
-/

namespace LeanDag

namespace BlackMarlin

namespace ViewOrder

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ Rot U
  have pins : ReliableAnchorPins U := by
    intro f₁ f₂ ρ L₁ L₂ hrel h₁ h₂
    obtain ⟨hm₁, hr₁, hc₁⟩ := f₁.isAnchor ρ L₁ h₁
    obtain ⟨hm₂, hr₂, hc₂⟩ := f₂.isAnchor ρ L₂ h₂
    exact U.eq_of_creator_eq hm₁ hm₂ hrel hc₁ hc₂ (hr₁.trans hr₂.symm)
  refine ⟨pins, ?_, ?_⟩
  · intro f₁ f₂ ρ d hrel h₁ h₂ hdense
    obtain ⟨L₁, hL₁⟩ := Option.isSome_iff_exists.mp h₁
    obtain ⟨L₂, hL₂⟩ := Option.isSome_iff_exists.mp h₂
    refine (Ledger.holds Validator BlockId Payload U).2.2.2.1 f₁ f₂ ρ d ?_ hdense
    rw [hL₁, hL₂, pins f₁ f₂ (ρ + d) L₁ L₂ hrel hL₁ hL₂]
  · intro f₁ f₂ τ n hrel hsome
    refine (Order.holds Validator BlockId Payload U).2.1 f₁ f₂ τ n ?_
    intro σ hσ
    by_cases h1 : (f₁.block σ).isSome
    · obtain ⟨L₁, hL₁⟩ := Option.isSome_iff_exists.mp h1
      obtain ⟨L₂, hL₂⟩ := Option.isSome_iff_exists.mp ((hsome σ hσ).mp h1)
      rw [hL₁, hL₂, pins f₁ f₂ σ L₁ L₂ (hrel σ hσ) hL₁ hL₂]
    · have h2 : ¬ (f₂.block σ).isSome := fun hc => h1 ((hsome σ hσ).mpr hc)
      rw [Option.not_isSome_iff_eq_none.mp h1, Option.not_isSome_iff_eq_none.mp h2]

end ViewOrder

end BlackMarlin

end LeanDag
