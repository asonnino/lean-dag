import LeanDagTest.TwoFaults
import LeanDag.Pedigree

/-!
# The general bound at `f = 2`

`dos-equivocation-and-growth.md` §10.5, the multi-equivocator witness.

`Ufault` is exactly the case `Adoption.lean`'s unique-equivocator theorem
cannot touch: **both** Byzantine validators equivocate and both are exposed
at the merge, so no choice of `X` leaves the others unexposed. The pedigree
machinery closes it: `card_history_le` bounds every history with no
hypothesis beyond `DoSValid`, at any fault budget.

The constant is enormous — `(3f+1)·(3f+2)^(3f+1) = 7·8⁷` at `f = 2`, against
an actual history of 20 blocks — but the point is its *shape*: constant in
`r`. C1′ asked for exactly that (`card_historyBlocksOf_le`): a per-author
per-round contribution that cannot compound down the rounds, whatever the
number of equivocators.
-/

namespace LeanDagTest

open LeanDag

/-! ## Two equivocators, both exposed — the case beyond `Adoption.lean` -/

-- Both Byzantine validators are exposed in the round-3 block's history, so
-- the unique-equivocator hypothesis genuinely fails here.
example : (exposedTo Ufault 19).card = 2 := by decide

-- Each equivocator's content is two chains: its two genesis blocks.
example : topsOf Ufault 19 0 = {0, 7} := by decide
example : topsOf Ufault 19 1 = {1, 8} := by decide

-- Honest authors: one chain each.
example : topsOf Ufault 19 2 = {19} := by decide

/-! ## C1′ and the general bound, applied -/

/-- **C1′ applied** at `f = 2`: validator 0's per-round contribution to the
history is bounded by `c(f) = 8⁷`, with no unique-equivocator hypothesis.
(The actual count at round 0 is `2` — the two geneses.) -/
example : ∀ n, (historyBlocksOf Ufault 19 0 n).card ≤ (3 * 2 + 2) ^ (3 * 2 + 1) :=
  fun n => card_historyBlocksOf_le ufault_dosValid (by decide) 0 n

example : (historyBlocksOf Ufault 19 0 0).card = 2 := by decide

/-- **The general bound applied**: the whole 20-block history is bounded
linearly in its round, both equivocators notwithstanding. -/
example : (history Ufault 19).card
    ≤ (3 * Faults.f (Fin 7) + 1) * (3 * Faults.f (Fin 7) + 2) ^ (3 * Faults.f (Fin 7) + 1)
      * ((Ufault.block 19).round + 1) :=
  card_history_le ufault_dosValid (by decide)

example : (history Ufault 19).card = 20 := by decide

/-- The tops count behind it: even with the budget fully spent, no author's
chain count exceeds the pedigree ceiling. -/
example : ∀ X : Fin 7, (topsOf Ufault 19 X).card ≤ (3 * 2 + 2) ^ (3 * 2 + 1) :=
  fun X => card_topsOf_le_pow ufault_dosValid (by decide) X

end LeanDagTest
