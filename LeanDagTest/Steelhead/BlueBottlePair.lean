import LeanDag.Steelhead.BlueBottlePair.Liveness.Proof
import LeanDag.Steelhead.Helpers.BlueBottlePair.Coin
import Mathlib.Tactic.IntervalCases
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

SH-BB16e as arithmetic; here it is on the schedule the two slots above run under. -/

-- Slot `0` is synchronous, so round `2` is already eligible to anchor it.
example : (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Eligible (S := pairSlots) 0 2 := by decide

-- Slot `1` is asynchronous, so round `3` is not: its floor is `1 + 3`.
example :
    ¬ (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Eligible (S := pairSlots) 1 3 := by decide

example : (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Eligible (S := pairSlots) 1 4 := by decide

/-! ## The pair's commit clause fires at both kinds (SH-BB6a)

The clause is an implication, so its hypotheses are exhibited here on `full6`: the five correct
validators are synchronised from round `0` and populate every round, and the clause then commits a
slot of each kind in the full view, slot `2` by Odontoceti one round up and slot `1` by Async
BlueBottle two rounds up. -/

/-- The five correct validators of `full6`. -/
def full6Correct : Finset (Fin 6) := {1, 2, 3, 4, 5}

/-- Every block of `full6` references every block of the round below. -/
theorem full6_refs_below :
    ∀ a b : Fin 24, (full6.block a).round + 1 = (full6.block b).round →
      a ∈ (full6.block b).refs := by
  decide

/-- Any set of validators is synchronised on `full6` from round `0`. -/
theorem full6_synchronisedOn (T : Finset (Fin 6)) : SynchronisedOn full6 T 0 :=
  fun _ _ b _ hbr _ a _ har _ => full6_refs_below a b (by rw [har, hbr])

/-- The correct validators populate every round of `full6`. -/
theorem full6_populatedOn (r : ℕ) (hr : r ≤ 3) : PopulatedOn full6 full6Correct r := by
  interval_cases r <;> decide

/-- **SH-BB6a at the synchronous kind**: slot `2`, led by validator `2`, commits. -/
theorem pair_full6_clause_sync :
    ∃ L, IsLeaderBlock (S := pairSlots) full6 2 L ∧
      (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Commit full6 (View.full full6) L
        (pairSlots.slotRound 2) (pairSlots.kind 2) :=
  BlueBottlePair.commitsUnderSync_pair (S := pairSlots) full6 full6Correct (View.full full6) 0 3 2
    (by decide) (by decide) (full6_synchronisedOn _) (fun r _ hr => full6_populatedOn r hr)
    (by decide) (by decide) (View.coversUpto_full _ _) (by decide)

/-- **SH-BB6a at the asynchronous kind**: slot `1`, led by validator `1`, commits. -/
theorem pair_full6_clause_async :
    ∃ L, IsLeaderBlock (S := pairSlots) full6 1 L ∧
      (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).Commit full6 (View.full full6) L
        (pairSlots.slotRound 1) (pairSlots.kind 1) :=
  BlueBottlePair.commitsUnderSync_pair (S := pairSlots) full6 full6Correct (View.full full6) 0 3 1
    (by decide) (by decide) (full6_synchronisedOn _) (fun r _ hr => full6_populatedOn r hr)
    (by decide) (by decide) (View.coversUpto_full _ _) (by decide)

-- The two slots read two decision rounds, `2 + 1` and `1 + 2`, both at the top of `full6`.
example : (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).decisionRound (S := pairSlots) 2 = 3 := by
  decide
example : (blueBottlePairAnchored (Fin 6) (Fin 24) Unit).decisionRound (S := pairSlots) 1 = 3 := by
  decide

/-! ## The coin's floor fires (SH-BB11a)

ABB7's population hypothesis holds on `full6` at round `1`: the five correct validators are a
quorum and populate rounds `2` and `3`. SH-BB11a then puts the coin among the committed round-`1`
candidates with probability at least `(6 − 3 · 1) / 6`. -/

/-- **SH-BB11a's hypothesis on `full6`.** -/
theorem full6_coinPopulated : BlueBottlePair.Coin.Populated full6 full6Correct 1 :=
  ⟨by decide, by decide, full6_populatedOn 2 (by omega), full6_populatedOn 3 (by omega)⟩

/-- **SH-BB11a on `full6`**: the coin names a committed round-`1` candidate with probability at
least one half. -/
theorem pair_full6_commitProb :
    ((6 - 3 * 1 : ℕ) : ENNReal) / Fintype.card (Fin 6) ≤
      commitProb (AsyncBlueBottle.goodAt full6) 1 :=
  BlueBottlePair.floor_le_commitProb full6_coinPopulated

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms pair_full6_slot0
#print axioms pair_full6_slot1
#print axioms pair_full6_clause_sync
#print axioms pair_full6_clause_async
#print axioms pair_full6_commitProb

end LeanDagTest
