import LeanDag.HammerheadTwo.Odontoceti.Statement
import LeanDag.HammerheadTwo.Helpers.Heads

/-!
# Odontoceti instance helpers

Not part of the audit surface. The laws are O5 (`decided_unique`), the
direct constructor and `isLeaderBlock_of_decided`; the descent laws are
O7 (`decided_of_leader_mem`) and the two indirect constructors, the
commit one at the least candidate with a thick link.
-/

namespace LeanDag

namespace HammerheadTwo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- The laws, for Odontoceti. -/
theorem odontoceti_laws [Faults5 Validator] :
    BaseRule.Laws (odontoceti (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  view_subset := fun V => V.subset_ids
  view_complete := fun V => V.complete
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := fun _ {_} _ _ _ _ _ h₁ h₂ => Odontoceti.decided_unique h₁ _ _ h₂
  decided_of_directCommitIn := fun _ {_} _ _ _ hL hdc => Odontoceti.Decided.directCommit hL hdc
  candidates := fun _ {_} _ _ _ h => Odontoceti.isLeaderBlock_of_decided h

/-- The descent laws, for Odontoceti at slack `f`. -/
theorem odontocetiLive_descent [F : Faults5 Validator] :
    (odontocetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      F.f where
  goodLeaders := by
    intro U Rnd N hgood
    obtain ⟨T, -, hcard, hsync, hpop⟩ := hgood
    refine ⟨T, by omega, ?_⟩
    intro S κ hRnd hN hlead
    letI := S
    change S.slotRound κ + 2 ≤ N at hN
    obtain ⟨L, -, hdec⟩ := Odontoceti.decided_of_leader_mem hcard hsync hRnd
      (hpop _ hRnd (by omega)) (hpop _ (by omega) (by omega)) hlead
    exact ⟨L, hdec⟩
  indirect := by
    intro S U V i j A hij hj hmid
    letI := S
    change S.slotRound i + 2 ≤ S.slotRound j at hij
    have helig : Odontoceti.Eligible Validator i j := Odontoceti.eligible_iff.mpr hij
    have hmid' : ∀ i', i < i' → i' < j → Odontoceti.Eligible Validator i i' →
        Odontoceti.Decided U V i' none :=
      fun i' h1 h2 h3 => hmid i' h1 h2 (Odontoceti.eligible_iff.mp h3)
    classical
    -- The candidates of `i` with a thick link to the anchor.
    by_cases hne : (U.ids.filter
        (fun L => IsLeaderBlock U i L ∧ Odontoceti.ThickLink U A L (S.slotRound i))).Nonempty
    · obtain ⟨_, hL, ht⟩ := Finset.mem_filter.mp (Finset.min'_mem _ hne)
      refine ⟨some _, Odontoceti.Decided.indirectCommit
        (Odontoceti.lt_of_eligible helig) helig hj hmid' hL ht ?_⟩
      intro L' hL' ht' hlt
      have hL's : L' ∈ U.ids.filter
          (fun L => IsLeaderBlock U i L ∧ Odontoceti.ThickLink U A L (S.slotRound i)) :=
        Finset.mem_filter.mpr ⟨hL'.1, hL', ht'⟩
      exact absurd hlt (not_lt.mpr (Finset.min'_le _ L' hL's))
    · refine ⟨none, Odontoceti.Decided.indirectSkip
        (Odontoceti.lt_of_eligible helig) helig hj hmid' ?_⟩
      intro L hL ht
      exact hne ⟨L, Finset.mem_filter.mpr ⟨hL.1, hL, ht⟩⟩

end HammerheadTwo

end LeanDag
