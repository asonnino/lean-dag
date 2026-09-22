import LeanDag.Steelhead.BlueBottlePair.Proof
import LeanDagTest.AsyncBlueBottle.Model
import LeanDagTest.Odontoceti.Model
/-!
# Steelhead witness: the `5f + 1` pair on one DAG

The `3f + 1` pair is one predicate family read at two numbers, so a
witness for it settles little. BlueBottle's pair is two rules, and this
file runs both of them on one universe under one schedule, so that
neither half is vacuous where the other fires and the two floors are
seen to differ on data.

The universe is Async BlueBottle's `full6`: six validators, `f = 1`, four
rounds, every non-genesis block referencing the whole round below. The
schedule gives one slot per round and alternates the kinds, so slot `0`
is Odontoceti's and slot `1` is Async BlueBottle's.

The schedule is a `def` and every claim passes `(S := pairSlots)`: the
Odontoceti witnesses this file imports declare a `Slots (Fin 6)`
instance of their own, and synthesis would otherwise pick it and decide a
different statement.
-/

namespace LeanDagTest

set_option maxRecDepth 4096

open LeanDag LeanDag.Steelhead

/-- One slot per round, led round-robin, synchronous at the even rounds and asynchronous at the
odd ones. -/
@[reducible]
def pairSlots : Slots (Fin 6) :=
  { Slots.identity (fun k => (⟨k % 6, by omega⟩ : Fin 6)) with kind := fun r => r % 2 }

example : pairSlots.slotRound 1 = 1 := rfl
example : pairSlots.kind 0 = 0 := rfl
example : pairSlots.kind 1 = 1 := rfl

/-- The composite's direct commit is decidable, the field being each half's own test. -/
instance pairCommitDecidable (U : BlockUniverse (Fin 6) (Fin 24) Unit)
    (V : View (Fin 6) (Fin 24) Unit U) (L : Fin 24) (r κ : ℕ) :
    Decidable ((blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Commit U V L r κ) :=
  (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).decCommit U V L r κ

/-! ## Both halves fire -/

/-- **The synchronous half decides slot `0`**: Odontoceti's quorum of round-`1` supporters, the
wave-two rule, under the composite. -/
theorem pair_full6_slot0 :
    (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Decided (S := pairSlots) full6
      (View.full full6) 0 (some 0) :=
  AnchoredRule.Decided.directCommit (S := pairSlots) (by decide) (by decide)

/-- **The asynchronous half decides slot `1`**: Async BlueBottle's cone vote at round `3`, the
wave-three rule, on the same universe and the same schedule. -/
theorem pair_full6_slot1 :
    (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Decided (S := pairSlots) full6
      (View.full full6) 1 (some 7) :=
  AnchoredRule.Decided.directCommit (S := pairSlots) (by decide) (by decide)

/-! ## The two floors differ

SH21e as arithmetic; here it is on the schedule the two slots above run under. -/

-- Slot `0` is synchronous, so round `2` is already eligible to anchor it.
example : (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Eligible (S := pairSlots) 0 2 := by decide

-- Slot `1` is asynchronous, so round `3` is not: its floor is `1 + 3`.
example :
    ¬ (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Eligible (S := pairSlots) 1 3 := by decide

example : (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Eligible (S := pairSlots) 1 4 := by decide

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms pair_full6_slot0
#print axioms pair_full6_slot1

end LeanDagTest
