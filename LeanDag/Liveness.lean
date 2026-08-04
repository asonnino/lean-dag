import LeanDag.Support

/-!
# Liveness — the DAG grows regardless

`liveness.md` §6, result L0.

This file needs **no liveness primitives at all**. L0 is a consequence of
validity alone: neither `Live` nor `Synchronised` appears, and nothing here
mentions correctness. It opens the liveness development because it is the
precise form of the notes' *"the DAG grows regardless"*, and because it is
what makes the pre-GST phase (§4.1) say something despite assuming nothing.

The content is not that the DAG grows — it is that the DAG **cannot grow tall
and thin**. A single block high up forces a quorum of distinct authors at
*every* round beneath it.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- A round with any author at all has a block. The bridge that lets L0's
induction step back down: a cardinality bound on `authorsAt` is turned into
a witness block, which the next step then references from. -/
theorem exists_mem_of_authorsAt_card_pos {n : ℕ} (h : 0 < (authorsAt U n).card) :
    ∃ i ∈ U.ids, (U.block i).round = n := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp h
  obtain ⟨i, hi, hir, _⟩ := mem_authorsAt.mp hv
  exact ⟨i, hi, hir⟩

/-- One step of L0: a block at round `n+1` forces a quorum of authors at
round `n`.

Immediate from validity — the block's references carry `2f+1` distinct
creators, and every one of them holds a round-`n` block. -/
theorem card_authorsAt_of_succ {n : ℕ} {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = n + 1) :
    2 * F.f + 1 ≤ (authorsAt U n).card :=
  le_trans (U.creators_quorum hi (by omega))
    (Finset.card_le_card (creators_refs_subset_authorsAt hi hir))

/-- **L0 — the DAG is dense below its frontier.** If any block exists at
round `r`, then *every* round `n < r` has at least `2f+1` distinct authors.

Downward induction on the gap `r - n`. The step is where the two lemmas
above meet: the inductive hypothesis gives a quorum of authors one round
higher, that quorum is nonempty so some block sits there, and
`card_authorsAt_of_succ` walks it down one more round.

The induction runs on the gap rather than on `r` itself because the
statement is not about `r`: nothing distinguishes the block's own round, and
generalising over `n` is what lets the step re-enter at `n+1`. -/
theorem card_authorsAt_of_lt {r n : ℕ} (hn : n < r) {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    2 * F.f + 1 ≤ (authorsAt U n).card := by
  obtain ⟨d, rfl⟩ : ∃ d, r = n + 1 + d := ⟨r - n - 1, by omega⟩
  clear hn
  induction d generalizing n i with
  | zero => exact card_authorsAt_of_succ hi hir
  | succ d ih =>
      have h1 : 2 * F.f + 1 ≤ (authorsAt U (n + 1)).card :=
        ih (n := n + 1) (i := i) hi (by omega)
      obtain ⟨j, hj, hjr⟩ := exists_mem_of_authorsAt_card_pos (U := U) (n := n + 1)
        (by omega)
      exact card_authorsAt_of_succ hj hjr

end LeanDag
