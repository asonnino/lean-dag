import LeanDagTest.Model
import LeanDag.Exposure

/-!
# Exposure on concrete DAGs

`dos-equivocation-and-growth.md` §11, the `f = 1` witness. Two models, and the
contrast between them is the point.

`Model.lean`'s **`U6`** has an equivocation — validator 0, Byzantine under this
fault model, authors both genesis blocks `0` and `4` — and yet **nothing in it
is ever exposed**, because no block references block `4`. That is D8 on real
data: the reference graph cannot carry evidence of an equivocation, so an
equivocation nobody builds on stays invisible. By D11 it is also harmless,
since no history holds two blocks by validator 0.

**`Umerge`** below is the same equivocation with the branches brought back
together:

```
  round 0   ids 0-3   genesis by validators 0,1,2,3
            id  4     a SECOND genesis by validator 0        -- the equivocation
  round 1   id  5     by 0, refs {0,1,2}
            id  6     by 1, refs {0,1,2}                     -- the A branch
            id  7     by 2, refs {4,1,2}                     -- the B branch
            id  8     by 3, refs {1,2,3}                     -- neither
  round 2   ids 9-11  by 1,2,3, refs {6,7,8}                 -- the MERGE
  round 3   id  12    by 1, refs {9,10,11}
```

Blocks `9`-`11` reach `0` through `6` and `4` through `7`, so validator 0 is
exposed to them — and to everything above (D12). `Umerge` still satisfies
`DoSValid`, and it does so **non-vacuously**: the merging blocks reference
`{6,7,8}`, authored by `1,2,3`, precisely because validator 0 is no longer
available to them. Block `5` exists and is perfectly valid, and no block from
round 2 on may name it.

That last point is what makes this a witness rather than a demonstration. A
model where the condition holds because nothing is exposed would leave every
theorem taking `DoSValid` vacuously true.
-/

open LeanDag

/-! ## D8 on `U6` — an equivocation nobody built on -/

-- Validator 0 really does equivocate: two distinct genesis blocks, one author.
example : (U6.block 0).creator = (U6.block 4).creator := by decide
example : (U6.block 0).round = (U6.block 4).round := by decide
example : (0 : Fin 13) ≠ 4 := by decide

-- But block 4 is referenced by nothing, so no history holds both halves ...
example : ∀ b ∈ U6.ids, (4 : Fin 13) ∉ (U6.block b).refs := by decide
example : ∀ b ∈ U6.ids, ¬ ExposedIn U6 b 0 := by decide

-- ... and the DoS condition is therefore satisfied vacuously here.
example : DoSValid U6 := by decide

/-! ## `history` computes

The fuel-indexed definition (§13 S6) against hand-checked answers. Block 9 of
`U6` sits at round 2 with refs `{5,6,7}`, and those reference `{0,1,2}`. -/

example : history U6 0 = {0} := by decide
example : history U6 5 = {5, 0, 1, 2} := by decide
example : history U6 9 = {9, 5, 6, 7, 0, 1, 2} := by decide

-- And it agrees with `Reaches`, which is the only lemma of substance in the file.
example : Reaches U6 9 0 := (mem_history_iff (by decide)).mp (by decide)
example : ¬ Reaches U6 9 4 := fun h => by
  have := (mem_history_iff (U := U6) (b := 9) (i := 4) (by decide)).mpr h
  revert this; decide

/-! ## `Umerge` — the branches meet -/

def lkm : Fin 13 → Block (Fin 4) (Fin 13) Unit := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if (i : ℕ) = 4 then
    { round := 0, creator := 0, refs := ∅, payload := () }
  else if (i : ℕ) = 5 then
    { round := 1, creator := 0, refs := {0, 1, 2}, payload := () }
  else if (i : ℕ) = 6 then
    { round := 1, creator := 1, refs := {0, 1, 2}, payload := () }
  else if (i : ℕ) = 7 then
    { round := 1, creator := 2, refs := {4, 1, 2}, payload := () }
  else if (i : ℕ) = 8 then
    { round := 1, creator := 3, refs := {1, 2, 3}, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 2, creator := ⟨(i : ℕ) - 8, by omega⟩, refs := {6, 7, 8}, payload := () }
  else
    { round := 3, creator := 1, refs := {9, 10, 11}, payload := () }

def Umerge : BlockUniverse (Fin 4) (Fin 13) Unit where
  ids := Finset.univ
  block := lkm
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ### The equivocation is exposed at the merge, and not before -/

-- Neither branch alone reveals anything — this is *potential* equivocation.
example : ¬ ExposedIn Umerge 6 0 := by decide
example : ¬ ExposedIn Umerge 7 0 := by decide
example : history Umerge 6 = {6, 0, 1, 2} := by decide
example : history Umerge 7 = {7, 4, 1, 2} := by decide

-- The merging block holds both halves, so validator 0 is exposed to it.
example : ExposedIn Umerge 9 0 := by decide
example : (0 : Fin 13) ∈ history Umerge 9 ∧ (4 : Fin 13) ∈ history Umerge 9 := by decide

-- Nobody else is ever exposed: accusations land only on the guilty (D15, ahead).
example : ∀ b ∈ Umerge.ids, ∀ X : Fin 4, ExposedIn Umerge b X → X = 0 := by decide

/-! ### The condition holds, and bites

`DoSValid` is satisfied — but not for want of an exposure. Blocks 9-12 are
exposed to validator 0 and are debarred from naming it, which is why they
reference `{6,7,8}` and `{9,10,11}` rather than anything of validator 0's. -/

theorem umerge_dosValid : DoSValid Umerge := by decide

-- Validator 0 has a perfectly valid round-1 block ...
example : (5 : Fin 13) ∈ Umerge.ids ∧ (Umerge.block 5).creator = 0 := by decide

-- ... which no block from the merge onward may reference.
example : ∀ i ∈ (Umerge.block 9).refs, (Umerge.block i).creator ≠ 0 := by decide
example : (5 : Fin 13) ∉ (Umerge.block 9).refs := by decide

/-! ### D11, D12 and D13 applied -/

/-- **D11 applied.** For validator 0 at the merge the theorem takes its second
branch: the block does not reference it. -/
example : ∀ i ∈ (Umerge.block 9).refs, (Umerge.block i).creator ≠ 0 :=
  (card_le_one_or_not_mem_refs umerge_dosValid (by decide) 0).resolve_left
    (by rw [not_forall]; exact ⟨0, by decide⟩)

/-- And below the merge it takes the first: one block per round, so
equivocating bought validator 0 nothing in that history. -/
example : ∀ n, (historyBlocksOf Umerge 6 0 n).card ≤ 1 :=
  not_exposedIn_iff_card_le_one.mp (by decide)

/-- **D12 applied.** Exposure is inherited: block 12 reaches the merge, so it
inherits the exposure and is likewise debarred. -/
example : ExposedIn Umerge 12 0 :=
  ExposedIn.of_mem_refs (by decide) (b := 9) (by decide) (by decide)

example : ∀ i ∈ (Umerge.block 12).refs, (Umerge.block i).creator ≠ 0 := by decide

/-- **D13 applied.** A view holding the merge reaches the same verdict, and the
witnesses are already inside it. -/
def Vmerge : View (Fin 4) (Fin 13) Unit Umerge where
  ids := {9, 6, 7, 8, 0, 1, 2, 3, 4}
  subset_ids := by decide
  complete := by decide

example : history Umerge 9 ⊆ Vmerge.ids := history_subset_view (by decide)

example : ∃ i ∈ Vmerge.ids, ∃ j ∈ Vmerge.ids,
    i ∈ history Umerge 9 ∧ j ∈ history Umerge 9 ∧ EquivPair Umerge 0 i j :=
  (exposedIn_iff_of_view (V := Vmerge) (by decide)).mpr (by decide)

#print axioms umerge_dosValid
