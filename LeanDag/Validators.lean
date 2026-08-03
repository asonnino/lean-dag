import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra

/-!
# Validators, faults, and quorum intersection

The system model of `spec.md` §2, plus the quorum-intersection lemma T0.

There are `3f+1` validators, of which at most `f` are Byzantine. A *quorum*
is any set of at least `2f+1` validators. The single fact everything
downstream rests on is that two quorums always share a **correct** validator
(`exists_correct_mem_inter`): two sets of size `2f+1` drawn from `3f+1`
overlap in at least `f+1` elements, one more than the fault bound.

The fault model is bundled as a class `Faults` rather than threaded as
section variables. Bundling keeps the two cardinality hypotheses attached to
the instance, so they never appear as explicit arguments and no `include` is
needed; it also lets `Correct` be written without an argument, since the
instance is inferred from `Validator`. Refer to the fault bound as `F.f`,
never as a bare `f` — a bare field access cannot determine which `Validator`
it belongs to and will elaborate to a metavariable.
-/

namespace LeanDag

/-- The fault model: exactly `3f+1` validators, at most `f` of them
Byzantine. -/
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  /-- The fault bound. -/
  f : ℕ
  /-- The Byzantine validators. Everything else is correct. -/
  byzantine : Finset Validator
  /-- There are exactly `3f+1` validators. -/
  card_validators : Fintype.card Validator = 3 * f + 1
  /-- At most `f` validators are Byzantine. -/
  card_byzantine : byzantine.card ≤ f

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]

/-- The correct (non-Byzantine) validators. -/
def Correct : Finset Validator := (F.byzantine)ᶜ

@[simp]
theorem mem_correct {v : Validator} : v ∈ (Correct : Finset Validator) ↔ v ∉ F.byzantine := by
  simp [Correct]

/-- At least `2f+1` validators are correct. -/
theorem card_correct : 2 * F.f + 1 ≤ (Correct : Finset Validator).card := by
  have h : (Correct : Finset Validator).card = Fintype.card Validator - F.byzantine.card :=
    Finset.card_compl F.byzantine
  have hle : F.byzantine.card ≤ Fintype.card Validator := Finset.card_le_univ _
  have := F.card_validators
  have := F.card_byzantine
  omega

/-- Any set of more than `f` validators contains a correct one, since the
Byzantine validators number at most `f`. -/
theorem exists_correct_of_card {S : Finset Validator} (h : F.f + 1 ≤ S.card) :
    ∃ v ∈ S, v ∈ (Correct : Finset Validator) := by
  by_contra hcon
  push Not at hcon
  have hsub : S ⊆ F.byzantine := fun v hv => by simpa using hcon v hv
  have := Finset.card_le_card hsub
  have := F.card_byzantine
  omega

/-- **T0 (cardinality half).** Two quorums overlap in at least `f+1`
validators: `(2f+1) + (2f+1) - (3f+1) = f+1`. -/
theorem card_inter_ge_of_quorum {Q₁ Q₂ : Finset Validator}
    (h₁ : 2 * F.f + 1 ≤ Q₁.card) (h₂ : 2 * F.f + 1 ≤ Q₂.card) :
    F.f + 1 ≤ (Q₁ ∩ Q₂).card := by
  have hunion : (Q₁ ∪ Q₂).card ≤ 3 * F.f + 1 := by
    rw [← F.card_validators]; exact Finset.card_le_univ _
  have hadd := Finset.card_union_add_card_inter Q₁ Q₂
  omega

/-- **T0.** Two quorums always share a *correct* validator. This is the form
every later proof cites. -/
theorem exists_correct_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : 2 * F.f + 1 ≤ Q₁.card) (h₂ : 2 * F.f + 1 ≤ Q₂.card) :
    ∃ v ∈ Q₁ ∩ Q₂, v ∈ (Correct : Finset Validator) :=
  exists_correct_of_card (card_inter_ge_of_quorum h₁ h₂)

end LeanDag
