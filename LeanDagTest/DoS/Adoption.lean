import LeanDagTest.DoS.Exposure
import LeanDagTest.DoS.Exclusion
import LeanDag.DoS.Adoption

/-!
# The adoption collapse on concrete DAGs

`dos-equivocation-and-growth.md` §5, witnesses for the tops machinery and
the main bound.

The count to watch: in `H(12)` of `Umerge`, validator 0 — the equivocator —
has **two tops**, its two genesis blocks, because the merge holds both
branches. Validator 1 — clean — has exactly **one**, block 12 itself. The
number of tops *is* the number of chains, and the equivocation is visible as
a chain count: `2` where honesty gives `1`, and never more than `3f` (the
namer authors) by `card_topsOf_le`.

Both witness models run at `f = 1`, so `card_history_le_of_f_le_one` applies
with no side condition beyond `DoSValid` — the first end-to-end instance of
C1′'s target: a *dirty* history (exposure and all) bounded linearly by its
round.
-/

namespace LeanDagTest

open LeanDag

/-! ## Tops are chains made countable -/

-- The equivocator's content in the merge history is TWO chains — the two
-- genesis blocks, neither with a 0-authored child in the history.
example : topsOf Umerge 12 0 = {0, 4} := by decide

-- The clean author's content is ONE chain, topped by the block itself.
example : topsOf Umerge 12 1 = {12} := by decide

-- Correct authors that stop building also top out: one chain each.
example : topsOf Umerge 12 2 = {10} := by decide
example : topsOf Umerge 12 3 = {11} := by decide

/-- **`card_topsOf_le` applied.** The equivocator's chain count is bounded by
the number of possible namer authors, `3f = 3` — and it is `2`. -/
example : (topsOf Umerge 12 0).card ≤ 3 * Faults.f (Fin 4) :=
  card_topsOf_le umerge_dosValid (by decide) (by decide) (by decide)

example : (topsOf Umerge 12 0).card = 2 := by decide

/-- **The fiber bound applied**: validator 0 contributes at most
`tops × rounds = 2 · 4 = 8` blocks to `H(12)` — it contributes 2. -/
example : ((history Umerge 12).filter
    (fun i => (Umerge.block i).creator = 0)).card
      ≤ (topsOf Umerge 12 0).card * ((Umerge.block 12).round + 1) :=
  card_filter_creator_le_card_topsOf umerge_dosValid (by decide) 0

/-! ## The main bound -/

/-- **The main bound applied** (`f = 1` form): every history of `Umerge` is
linear in its round. For block 12: `12 ≤ 7 · 4 = 28`. -/
example : (history Umerge 12).card ≤
    ((2 * Fintype.card (Fin 4) - 1)) * ((Umerge.block 12).round + 1) :=
  card_history_le_of_f_le_one umerge_dosValid (by decide) (by decide)

/-- The same through the counted hypothesis: exactly one author is caught in
`H(12)`, and one is what the single-equivocator regime allows. -/
example : (exposedTo Umerge 12).card ≤ 1 := by decide

example : (history Umerge 12).card ≤
    ((2 * Fintype.card (Fin 4) - 1)) * ((Umerge.block 12).round + 1) :=
  card_history_le_of_card_exposedTo_le_one umerge_dosValid (by decide) (by decide)

/-- And on the six-round `Uexcl`, whose exclusion story is §4's: the top
block's history is `18 ≤ 7 · 6 = 42`. The bound holds *through* the
exclusion — the history carries the equivocator's two chains (its two
geneses) and is bounded all the same. -/
example : (history Uexcl 17).card ≤
    ((2 * Fintype.card (Fin 4) - 1)) * ((Uexcl.block 17).round + 1) :=
  card_history_le_of_f_le_one uexcl_dosValid (by decide) (by decide)

example : topsOf Uexcl 17 0 = {0, 4} := by decide

/-! ## The floor and the ceiling together

With D24 this pins the answer to §5's question on real data: block 17's
history must hold at least `(2f+1)·5 + 1 = 16` blocks and may hold at most
`(6f+1)·6 = 42`; it holds `18`. Both sides are `Θ(f·r)` — the DoS condition
plus self-parents make history size a *bounded resource*, not merely a
monitored one. -/

example : ((Fintype.card (Fin 4) - Faults.f (Fin 4))) * (Uexcl.block 17).round + 1
      ≤ (history Uexcl 17).card ∧
    (history Uexcl 17).card
      ≤ ((2 * Fintype.card (Fin 4) - 1)) * ((Uexcl.block 17).round + 1) :=
  ⟨card_history_ge (by decide) (by decide),
    card_history_le_of_f_le_one uexcl_dosValid (by decide) (by decide)⟩

end LeanDagTest
