import LeanDagTest.AsyncBlueBottle.Model
import LeanDag.AsyncBlueBottle.Counting.Statement
/-!
# Async BlueBottle witnesses — the counting lemma on data

`goodAt`, the common core, and the statement hypotheses of
`Counting/Statement.lean` settled by `decide` on the **aiming pattern**
`aim6` of `Model.lean` (`async-bluebottle.md` §6): an adversary that
knows slot `0`'s leader keeps that leader's block out of every cone it
can. Two witnesses:

* `aim6` — the targeted leader is exactly the validator that is not good;
  the other five are good, four of them correct, so the `n − 3f = 3`
  bound of `GoodCard` holds with room;
* `multi` — four distinct leaders per round (`3f + 1 = 4`) always include
  a good one, the conclusion of `MultiLeader` as an explicit slot.

Same committee as `Model.lean` (validator `0` Byzantine, `f = 1`, quorum
`5`); the schedules are local instances.
-/

namespace LeanDagTest

set_option maxRecDepth 4096

open LeanDag LeanDag.AsyncBlueBottle

/-- Round-robin from validator `1`, one leader per round. -/
local instance abbSlotsC : Slots (Fin 6) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨(k + 1) % 6, by omega⟩)

/-! ## `aim6` — the aiming pattern against slot `0`

The universe is `Model.lean`'s; here it carries the counting facts. -/

/-! ### The target -/

-- The good validators at round `0` are everyone but the target: the
-- leader round-robin names is exactly the one the adversary starved.
example : goodAt aim6 0 = {0, 2, 3, 4, 5} := by decide
example : (1 : Fin 6) ∉ goodAt aim6 0 := by decide
example : good aim6 0 = {0, 2, 3, 4, 5} := by decide

/-! ### The common core on data -/

-- Block `2` (validator `2`, round `0`) is referenced by every round-`1`
-- block, and so lies in the cone of every round-`2` block.
example : ∀ c : Fin 18, 2 ≤ (aim6.block c).round → 2 ∈ history aim6 c := by decide

-- Its author is correct and good — a witness `GoodNonempty` may name.
example : (2 : Fin 6) ∈ goodAt aim6 0 ∩ (Correct : Finset (Fin 6)) := by decide

/-! ### The statement hypotheses hold on `aim6` -/

-- Population at the rounds the statements read, for the reliable set
-- `T = Correct = {1, 2, 3, 4, 5}`.
example : PopulatedOn aim6 (Correct : Finset (Fin 6)) 1 := by
  unfold PopulatedOn; decide
example : PopulatedOn aim6 (Correct : Finset (Fin 6)) 2 := by
  unfold PopulatedOn; decide
example : quorumCard (Fin 6) ≤ (Correct : Finset (Fin 6)).card := by decide

-- `GoodCard` on data: `n − 3f = 3 ≤ |good ∩ Correct| = 4`.
example : Fintype.card (Fin 6) ≤
    (goodAt aim6 0 ∩ (Correct : Finset (Fin 6))).card + 3 * Faults.f (Fin 6) := by
  decide
example : (goodAt aim6 0 ∩ (Correct : Finset (Fin 6))).card = 4 := by decide

/-! ## `multi` — four leaders per round -/

/-- Four slots per round, led by validators `0`, `1`, `2`, `3` in turn:
slots `4k, …, 4k+3` sit at round `k`. The `hblock` obligation is that
the four leaders of a round are distinct, which `k % 4` supplies. -/
@[reducible] def abbMultiSlots : Slots (Fin 6) :=
  Slots.uniform 1 4 (by omega) (by omega) (fun k => ⟨k % 4, by omega⟩)
    (fun k₁ k₂ h₁ h₂ => by
      have : k₁ % 4 = k₂ % 4 := by simpa using congrArg Fin.val h₂
      omega)

-- At round `0` the slots are `0, 1, 2, 3`, led by `0, 1, 2, 3`: `3f + 1 = 4`
-- distinct leaders, the threshold of `MultiLeader`.
example : 3 * Faults.f (Fin 6) + 1 ≤ ({0, 1, 2, 3} : Finset (Fin 6)).card := by decide
example : abbMultiSlots.slotRound 2 = 0 ∧ abbMultiSlots.leader 2 = 2 := by decide

-- Slot `1` is led by the starved validator and is not good; slot `2` is.
example : abbMultiSlots.leader 1 ∉ good (S := abbMultiSlots) aim6 1 := by decide
example : abbMultiSlots.leader 2 ∈ good (S := abbMultiSlots) aim6 2 := by decide

-- The conclusion of `MultiLeader` as an explicit slot.
example : ∃ k, abbMultiSlots.slotRound k = 0 ∧
    abbMultiSlots.leader k ∈ good (S := abbMultiSlots) aim6 k :=
  ⟨2, by decide, by decide⟩

/-! ## Axioms -/

#print axioms aim6

end LeanDagTest
