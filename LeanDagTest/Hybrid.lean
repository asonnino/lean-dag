import LeanDag.Hybrid.Conservativity
import LeanDag.Schedule
import LeanDagTest.Odontoceti.Model

/-!
# The hybrid fault model, witnessed

Two models, per `hybrid-plan.md` H9.

**`Uhyb4`** is the headline: `fb = 0, fc = 1, n = 4` — the classical
committee of `3f + 1` = 4 with **two-round finality**, when the single
tolerated fault is a crash. Tolerating it as Byzantine would cost six
validators. Validator `3` halts after its genesis block; the other
three run three full rounds at quorum `q = 3`, slots commit directly in
one delivery, and the crashed validator's slot is skipped vacuously.

**`Uhyb9`** is genuinely hybrid: `fb = 1, fc = 1, n = 9 = 5 + 3 + 1`,
tight. Validator `0` is Byzantine and equivocates at round `1` (blocks
`9` and `17`, one author, one round); validator `8` crashes after
genesis. `HonestNoEquiv` *holds* — the only twins are the Byzantine
validator's — the fully-correct class numbers exactly `q = 7` (the
tight committee has no slack), and slot `0` commits directly on eight
supporting authors.

The conservativity bridge is exercised on the existing Odontoceti
committee: `Faults5.toHybrid` reads the `n = 6, f = 1` model as a
crash-free hybrid one, and the two derived instances are equal.
-/

namespace LeanDagTest

open LeanDag LeanDag.Hybrid

/-! ## `Uhyb4` — one crash, four validators, two-round commits -/

instance hyb4 : HybridFaults (Fin 4) where
  fb := 0
  fc := 1
  byzantine := ∅
  crash := {3}
  disjoint := by decide
  card_byzantine := by decide
  card_crash := by decide
  card_validators := by decide

-- The thresholds, on data: quorum 3, indirect threshold 2, tight.
example : Hybrid.q (Fin 4) = 3 := by decide
example : kTight (Fin 4) = 2 := by decide
example : kRel (Fin 4) = 2 := by decide
example : Admissible (Fin 4) 2 := by decide

-- The derived instance: the union class, quorum `n − (fb + fc)`.
example : (Faults.byzantine (Validator := Fin 4)) = {3} := by decide
example : (Correct : Finset (Fin 4)) = {0, 1, 2} := by decide
example : Honest (Fin 4) = {0, 1, 2, 3} := by decide

-- The tight committee has no slack: the correct class is exactly `q`.
example : (Correct : Finset (Fin 4)).card = Hybrid.q (Fin 4) := by decide

/-- Three full lines and one that stops: validator `3` authors only its
genesis block. Rounds `1`–`3` run at quorum `3` among the survivors. -/
def hyb4Blk : Fin 13 → Block (Fin 4) (Fin 13) Unit := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 7 then
    { round := 1, creator := ⟨(i : ℕ) - 4, by omega⟩,
      refs := {0, 1, 2}, payload := () }
  else if h : (i : ℕ) < 10 then
    { round := 2, creator := ⟨(i : ℕ) - 7, by omega⟩,
      refs := {4, 5, 6}, payload := () }
  else
    { round := 3, creator := ⟨(i : ℕ) - 10, by have := i.isLt; omega⟩,
      refs := {7, 8, 9}, payload := () }

/-- The universe: the derived instance's quorum `q = 3` is what P3
demands, so three referenced authors per round suffice — with four
validators. -/
def Uhyb4 : BlockUniverse (Fin 4) (Fin 13) Unit where
  ids := Finset.univ
  block := hyb4Blk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- The strengthened clause holds — vacuously strong here: no one
-- equivocates at all.
example : HonestNoEquiv Uhyb4 := by decide

instance hyb4Slots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

-- Slot 1: leader 1, leader block 5, supported by all three survivors.
example : IsLeaderBlock Uhyb4 1 5 := by decide
example : Hybrid.DirectCommit Uhyb4 5 1 := by decide

/-- **Two-round commit under a crash**: slot `1` decided in one
delivery, at four validators. -/
theorem uhyb4_slot1 :
    Hybrid.Decided 2 Uhyb4 (View.full Uhyb4) 1 (some 5) :=
  Decided.directCommit (by decide) (by decide)

/-- **The crashed validator's slot is skipped vacuously**: validator
`3` authored nothing at round `3`, so there is no candidate. -/
theorem uhyb4_slot3 :
    Hybrid.Decided 2 Uhyb4 (View.full Uhyb4) 3 none := by
  have hall : ∀ L : Fin 13, ¬ IsLeaderBlock Uhyb4 3 L := by decide
  exact Decided.directSkip (fun L hL => absurd hL (hall L))

-- Agreement, exercised across the two routes at the admissible
-- threshold.
example : ∀ v, Hybrid.Decided 2 Uhyb4 (View.full Uhyb4) 1 v → v = some 5 :=
  fun v hv =>
    (decided_agree (by decide) (by decide) hv uhyb4_slot1)

/-! ## `Uhyb9` — Byzantine and crash together, at the tight committee -/

instance hyb9 : HybridFaults (Fin 9) where
  fb := 1
  fc := 1
  byzantine := {0}
  crash := {8}
  disjoint := by decide
  card_byzantine := by decide
  card_crash := by decide
  card_validators := by decide

example : Hybrid.q (Fin 9) = 7 := by decide
example : kTight (Fin 9) = 4 := by decide
example : kRel (Fin 9) = 4 := by decide
example : (Correct : Finset (Fin 9)).card = Hybrid.q (Fin 9) := by decide

/-- Round `0` from all nine; round `1` from validators `0`–`7`
(validator `8` has crashed), with the Byzantine validator `0` producing
**two** round-`1` blocks — ids `9` and `17`, one author, one round,
different references. -/
def hyb9Blk : Fin 18 → Block (Fin 9) (Fin 18) Unit := fun i =>
  if h : (i : ℕ) < 9 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 16 then
    { round := 1, creator := ⟨(i : ℕ) - 9, by omega⟩,
      refs := {0, 1, 2, 3, 4, 5, 6}, payload := () }
  else if h : (i : ℕ) = 16 then
    { round := 1, creator := ⟨7, by omega⟩,
      refs := {0, 1, 2, 3, 4, 5, 7}, payload := () }
  else
    { round := 1, creator := ⟨0, by omega⟩,
      refs := {0, 1, 2, 3, 4, 5, 7}, payload := () }

def Uhyb9 : BlockUniverse (Fin 9) (Fin 18) Unit where
  ids := Finset.univ
  block := hyb9Blk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- The Byzantine validator genuinely equivocates: two round-1 ids, one
-- author — and `HonestNoEquiv` nonetheless holds, because the author
-- is Byzantine. The crash-prone and correct validators author at most
-- one block per round.
example : (Uhyb9.block 9).creator = 0 ∧ (Uhyb9.block 17).creator = 0 ∧
    (Uhyb9.block 9).round = 1 ∧ (Uhyb9.block 17).round = 1 := by decide
example : HonestNoEquiv Uhyb9 := by decide

instance hyb9Slots : Slots (Fin 9) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 9, by omega⟩)

-- Slot 0: leader 0 (Byzantine!), leader block 0, supported by eight
-- distinct authors at round 1 — above the quorum 7.
example : IsLeaderBlock Uhyb9 0 0 := by decide
example : (supporters Uhyb9 0 1 : Finset (Fin 9)).card = 8 := by decide
example : Hybrid.DirectCommit Uhyb9 0 0 := by decide

/-- **The genuinely hybrid commit**: one equivocator, one crashed line,
and slot `0` commits directly at the tight committee. -/
theorem uhyb9_slot0 :
    Hybrid.Decided 4 Uhyb9 (View.full Uhyb9) 0 (some 0) :=
  Decided.directCommit (by decide) (by decide)

#print axioms uhyb4_slot1
#print axioms uhyb9_slot0

/-! ## Conservativity, exercised

The existing `n = 6, f = 1` Odontoceti committee, read as a crash-free
hybrid one. -/

example : (Faults5.toHybrid : HybridFaults (Fin 6)).fb = 1 := rfl
example : (Faults5.toHybrid : HybridFaults (Fin 6)).fc = 0 := rfl
example : (HybridFaults.toFaults (H := (Faults5.toHybrid : HybridFaults (Fin 6)))) =
    Faults5.toFaults := toHybrid_toFaults

#print axioms LeanDag.Hybrid.decided_unique
#print axioms LeanDag.Hybrid.safety
#print axioms LeanDag.Hybrid.all_decided_below_of_fairRun
#print axioms LeanDag.Hybrid.toHybrid_toFaults

end LeanDagTest
