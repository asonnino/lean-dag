import LeanDag.History

/-!
# Density: histories are almost all of the correct past

`dos-equivocation-and-growth.md` §5, **D25**.

The quorum condition says a block's references carry `2f+1` distinct
creators, of which at most `f` are Byzantine — so at least `2f+1 - β`
correct, where `β := |byzantine|`. Since the correct validators number
exactly `3f+1 - β`, a block *misses* at most
`(3f+1-β) - (2f+1-β) = f` of the correct validators of the round below —
independent of `β`. And missing is monotone through any correct reference:
what `b`'s history lacks at a deep round, its references' histories lack
too. Inducting through any one correct reference:

> **D25 (density).** A valid block's history contains a block by all but at
> most `f` of the correct validators, at *every* round strictly below it.

This is T3/L0 sharpened from "a quorum of authors appears" to "almost
everyone appears", and it is the model's strongest expression of the fact
the DoS analysis leans on: **cones cannot be selectively blind**. A block
may curate its `≤ f` misses, but it swallows everything else — including
everything those correct blocks had already swallowed. Nothing here needs
`DoSValid` or self-parents; it is pure validity.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The correct validators with no block at round `δ` in `b`'s history. -/
def missingAt (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (δ : ℕ) :
    Finset Validator :=
  (Correct : Finset Validator).filter fun v =>
    ∀ i ∈ history U b, ¬ ((U.block i).creator = v ∧ (U.block i).round = δ)

/-- Membership in `missingAt`, unfolded: a correct validator is missing at depth `δ` when the history contains none of its blocks there. -/
theorem mem_missingAt {b : BlockId} {δ : ℕ} {v : Validator} :
    v ∈ missingAt U b δ ↔ v ∈ (Correct : Finset Validator) ∧
      ∀ i ∈ history U b, ¬ ((U.block i).creator = v ∧ (U.block i).round = δ) := by
  simp [missingAt]

/-- Missing is monotone through references: what `b` lacks, its references
lack. -/
theorem missingAt_subset_of_mem_refs {b p : BlockId} (hb : b ∈ U.ids)
    (hp : p ∈ (U.block b).refs) {δ : ℕ} :
    missingAt U b δ ⊆ missingAt U p δ := by
  intro v hv
  rw [mem_missingAt] at hv ⊢
  refine ⟨hv.1, fun i hi => hv.2 i ?_⟩
  exact history_subset_of_reaches hb (Reaches.single hp) hi

/-- The one-round case: the references themselves witness all but at most
`f` of the correct validators of the round below. -/
private theorem card_missingAt_le_base {b : BlockId} (hb : b ∈ U.ids) {δ : ℕ}
    (hδ : δ + 1 = (U.block b).round) : (missingAt U b δ).card ≤ F.f := by
  have hquorum := (U.valid b hb).quorum (by omega)
  have hinter :=
    card_le_card_inter_correct_add_byzantine (creators U.block (U.block b))
  have hbyz := F.card_byzantine
  have hcorrect := card_correct_add_byzantine (Validator := Validator)
  have hdisj : ∀ v ∈ creators U.block (U.block b) ∩ (Correct : Finset Validator),
      v ∉ missingAt U b δ := by
    intro v hv hmiss
    rw [Finset.mem_inter] at hv
    obtain ⟨p, hp, hpc⟩ := mem_creatorsOf.mp hv.1
    rw [mem_missingAt] at hmiss
    exact hmiss.2 p (mem_history_of_mem_refs hb hp)
      ⟨hpc, by have := U.round_of_mem_refs hb hp; omega⟩
  have hsub : (creators U.block (U.block b) ∩ (Correct : Finset Validator))
      ∪ missingAt U b δ ⊆ (Correct : Finset Validator) := by
    intro v hv
    rcases Finset.mem_union.mp hv with h | h
    · exact (Finset.mem_inter.mp h).2
    · exact (mem_missingAt.mp h).1
  have hunion := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint (Finset.disjoint_left.mpr hdisj)] at hunion
  omega

private theorem card_missingAt_le_aux (n : ℕ) :
    ∀ {b : BlockId}, b ∈ U.ids → ∀ {δ : ℕ}, δ < (U.block b).round →
      (U.block b).round - δ ≤ n + 1 → (missingAt U b δ).card ≤ F.f := by
  induction n with
  | zero =>
      intro b hb δ hδ hfuel
      exact card_missingAt_le_base hb (by omega)
  | succ n ih =>
      intro b hb δ hδ hfuel
      rcases Nat.lt_or_ge δ ((U.block b).round - 1) with hlt | hge
      · -- step through any correct reference
        have hquorum := (U.valid b hb).quorum (by omega)
        have hinter :=
          card_le_card_inter_correct_add_byzantine (creators U.block (U.block b))
        have hbyz := F.card_byzantine
        have hpos : 0 < (creators U.block (U.block b)
            ∩ (Correct : Finset Validator)).card := by
          have := F.card_validators
          omega
        obtain ⟨v, hv⟩ := Finset.card_pos.mp hpos
        rw [Finset.mem_inter] at hv
        obtain ⟨p, hp, hpc⟩ := mem_creatorsOf.mp hv.1
        have hp_ids : p ∈ U.ids := U.complete b hb p hp
        have hp_round := U.round_of_mem_refs hb hp
        refine le_trans
          (Finset.card_le_card (missingAt_subset_of_mem_refs hb hp)) ?_
        exact ih hp_ids (by omega) (by omega)
      · exact card_missingAt_le_base hb (by omega)

/-- **D25 (density).** A valid block's history contains a block by all but
at most `f` of the correct validators at every round strictly below it. -/
theorem card_missingAt_le {b : BlockId} (hb : b ∈ U.ids) {δ : ℕ}
    (hδ : δ < (U.block b).round) : (missingAt U b δ).card ≤ F.f :=
  card_missingAt_le_aux ((U.block b).round - δ) hb hδ (by omega)

end LeanDag
