import LeanDagTest.Model
import LeanDag.Density
import LeanDag.Pedigree

/-!
# Density, and the anchor factor made real

`dos-equivocation-and-growth.md` §5. Two things on one small model.

**D25 on real data.** Every block of `Utwin` misses at most `f = 1` correct
validator at every round below it — and the budget is *spent*: block 5's
history misses exactly one (validator 2, excluded by choice).

**The anchor factor is attained.** `Utwin` puts **two chains of the same
author into one history at `f = 1`** — the minimum possible fault budget —
by exactly the mechanism the tightened count charges for: two correct
validators adopt the two halves of the equivocation while spending their
`f`-miss budget on excluding *each other*:

```
  round 0   ids 0-3    genesis by validators 0,1,2,3
            id  4      a SECOND genesis by validator 0     -- the equivocation
  round 1   id  5      by 1, refs {1, 3, 0}                -- adopts half A, misses 2
            id  6      by 2, refs {2, 3, 4}                -- adopts half B, misses 1
            id  7      by 3, refs {1, 2, 3}                -- silent on 0
  round 2   id  8      by 3, refs {5, 6, 7}                -- the merge
```

Block 8 — a **correct** validator's block — then holds both chains:
`topsOf Utwin 8 0 = {0, 4}`, against the proved ceiling
`(3f+1-e)·e^(e-1) = 3`. So the `(3f+1-e)` anchor factor in
`card_topsOf_le_of_exposed` cannot be reduced below the number of correct
validators that can sustain divergent adoptions — which D25 pins at
"pairwise exclusion costs one miss each, out of `f`".
-/

namespace LeanDagTest

open LeanDag

def lkt : Fin 9 → Block (Fin 4) (Fin 9) Unit := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if (i : ℕ) = 4 then
    { round := 0, creator := 0, refs := ∅, payload := () }
  else if (i : ℕ) = 5 then
    { round := 1, creator := 1, refs := {1, 3, 0}, payload := () }
  else if (i : ℕ) = 6 then
    { round := 1, creator := 2, refs := {2, 3, 4}, payload := () }
  else if (i : ℕ) = 7 then
    { round := 1, creator := 3, refs := {1, 2, 3}, payload := () }
  else
    { round := 2, creator := 3, refs := {5, 6, 7}, payload := () }

def Utwin : BlockUniverse (Fin 4) (Fin 9) Unit where
  ids := Finset.univ
  block := lkt
  complete := by decide
  valid := by decide
  no_equivocation := by decide

theorem utwin_dosValid : DoSValid Utwin := by decide

/-! ## D25 on real data -/

/-- **D25 applied**: every round below block 8 misses at most `f = 1`
correct validator. -/
example : ∀ δ < (Utwin.block 8).round, (missingAt Utwin 8 δ).card ≤ Faults.f (Fin 4) :=
  fun _ hδ => card_missingAt_le (by decide) hδ

-- Block 8 in fact misses nobody; block 5 misses exactly validator 2 — the
-- budget of `f = 1` spent in full, which is what sustains the divergence.
example : missingAt Utwin 8 0 = ∅ := by decide
example : missingAt Utwin 5 0 = {2} := by decide
example : (missingAt Utwin 5 0).card = Faults.f (Fin 4) := by decide
example : missingAt Utwin 6 0 = {1} := by decide

/-! ## Two chains of one author at `f = 1` -/

-- The two adoptions are individually clean — neither round-1 block is
-- exposed to validator 0, so each may lawfully reference its half.
example : ¬ ExposedIn Utwin 5 0 := by decide
example : ¬ ExposedIn Utwin 6 0 := by decide

-- The merge holds both chains: a correct validator's own block, carrying
-- two chains of the equivocator.
example : ExposedIn Utwin 8 0 := by decide
example : topsOf Utwin 8 0 = {0, 4} := by decide
example : (Utwin.block 8).creator ∈ (Correct : Finset (Fin 4)) := by decide

/-- The tightened ceiling `(3f+1-e)·e^(e-1) = 3` against the attained `2`:
the anchor factor is not slack — it is the count of correct validators able
to sustain divergent adoptions under the `f`-miss budget. -/
example : (topsOf Utwin 8 0).card ≤
    (Fintype.card (Fin 4) - (exposedTo Utwin 8).card) *
      (exposedTo Utwin 8).card ^ ((exposedTo Utwin 8).erase 0).card :=
  card_topsOf_le_of_exposed utwin_dosValid (by decide) (by decide)

example : (topsOf Utwin 8 0).card = 2 := by decide
example : (Fintype.card (Fin 4) - (exposedTo Utwin 8).card) *
    (exposedTo Utwin 8).card ^ ((exposedTo Utwin 8).erase 0).card = 3 := by decide

end LeanDagTest
