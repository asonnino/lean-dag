import LeanDagTest.Odontoceti.Model
import LeanDag.AsyncBlueBottle.Model.Decision
/-!
# Async BlueBottle witnesses — an equivocating leader

Two universes with the Byzantine validator `0` leading slot `0` and
proposing two round-`0` twins, under Odontoceti's committee and a local
round-robin schedule with slot `k` at round `k` led by `k % 6` (the
other witness files start the rotation at validator `1`, so that their
slot `0` has a correct leader; here it must be the equivocator):

* `twin6` — **the canonicity finding, on data** (`async-bluebottle.md`
  §4): each twin gathers exactly three voters at the decision round —
  the cone vote picks one twin per voter, so the two voter sets are
  disjoint — and a round-`3` block that sees all of round `2` passes
  **both** twins through `WeakLink`. No counting argument separates
  them; the least-candidate rule is what restores agreement, and at the
  slot's actual anchor the derivation commits the least twin.
* `hazard6` — **the paper's Algorithm 2, on data** (`async-bluebottle.md`
  §4): both twins lie in every decision-round cone, so every voter votes
  for the least twin. The least twin is directly committed while the
  other has a quorum of *per-candidate* non-voters; the pseudocode's
  `TryDirectDecide` returns `Skip` or `Commit` according to which twin
  it examines first. Under the paper's Observation 4 — at most one block
  per author and round counts as valid — the hazard cannot arise; it
  arises as soon as both twins are valid, as they are in the DAG of
  Figure 1 and in the implementation. The slot-level blame this arc
  adopts, as the implementation does, has no blamer at all.
-/

namespace LeanDagTest

set_option maxRecDepth 4096

open LeanDag LeanDag.AsyncBlueBottle

/-- Round-robin from validator `0`: slot `k` at round `k`, led by `k % 6`. -/
local instance abbSlotsT : Slots (Fin 6) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 6, by omega⟩)

/-! ## `twin6` — both twins pass the weak test at one anchor -/

/-- Round `0`: blocks `0`–`5` by validators `0`–`5` and block `6`, a
second round-`0` block by validator `0`. Block `6m + v + 1` is then
validator `v`'s round-`m` block. Round `1`: validator `0` references
twin `0`, validator `1` references twin `6`, the others neither. Round
`2`: validators `0`, `1`, `2` reach twin `0` (validator `1`'s cone holds
both twins, and its vote goes to the least), validators `3`, `4`, `5`
reach only twin `6`. Round `3`: validator `3`'s block `22`, the slot-`3`
anchor, omits validator `5`'s round-`2` block; every other block
references the whole round below, as do rounds `4` and `5`. -/
def twinBlk6 : Fin 37 → Block (Fin 6) (Fin 37) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) = 6 then
    { round := 0, creator := 0, refs := ∅, payload := () }
  else if h : (i : ℕ) < 13 then
    { round := 1, creator := ⟨(i : ℕ) - 7, by omega⟩,
      refs := if (i : ℕ) = 7 then {0, 1, 2, 3, 4}        -- twin 0
        else if (i : ℕ) = 8 then {6, 1, 2, 3, 4}         -- twin 6
        else {1, 2, 3, 4, 5},                            -- neither
      payload := () }
  else if h : (i : ℕ) < 19 then
    { round := 2, creator := ⟨(i : ℕ) - 13, by omega⟩,
      refs := if (i : ℕ) = 14 then {7, 8, 9, 10, 11}     -- both twins: votes 0
        else if (i : ℕ) ≤ 15 then {7, 9, 10, 11, 12}     -- twin 0 only
        else {8, 9, 10, 11, 12},                         -- twin 6 only
      payload := () }
  else if h : (i : ℕ) < 25 then
    { round := 3, creator := ⟨(i : ℕ) - 19, by omega⟩,
      refs := if (i : ℕ) = 22 then {13, 14, 15, 16, 17}  -- the anchor omits 18
        else {13, 14, 15, 16, 17, 18},
      payload := () }
  else if h : (i : ℕ) < 31 then
    { round := 4, creator := ⟨(i : ℕ) - 25, by omega⟩,
      refs := {19, 20, 21, 22, 23, 24}, payload := () }
  else
    { round := 5, creator := ⟨(i : ℕ) - 31, by have := i.isLt; omega⟩,
      refs := {25, 26, 27, 28, 29, 30}, payload := () }

/-- A valid universe: the twins are the Byzantine validator's, so
`no_equivocation` is not violated. -/
def twin6 : BlockUniverse (Fin 6) (Fin 37) Unit where
  ids := Finset.univ
  block := twinBlk6
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Both twins are slot `0`'s candidates.
example : IsLeaderBlock twin6 0 0 ∧ IsLeaderBlock twin6 0 6 := by decide

-- Validator `1`'s round-`2` block holds both twins in its cone and votes
-- for the least; the vote is unique per block.
example : MahiMahi.candidatesAt twin6 14 0 0 = {0, 6} := by decide
example : MahiMahi.Votes twin6 14 0 ∧ ¬ MahiMahi.Votes twin6 14 6 := by decide

-- The split: three voters each, no blamer — neither direct rule fires
-- for either twin, and the slot is not skipped.
example : AsyncBlueBottle.supporters twin6 0 0 = {0, 1, 2} := by decide
example : AsyncBlueBottle.supporters twin6 6 0 = {3, 4, 5} := by decide
example : blamers twin6 0 0 = ∅ := by decide
example : ¬ AsyncBlueBottle.DirectCommit twin6 0 0 ∧ ¬ AsyncBlueBottle.DirectCommit twin6 6 0 := by
  decide
example : ¬ AsyncBlueBottle.DirectSkip twin6 0 0 := by decide

/-- **The finding, realised**: block `19` sees all of round `2`, and
**both** twins pass the weak test against it. -/
theorem twin6_both_pass : WeakLink twin6 19 0 0 ∧ WeakLink twin6 19 6 0 := by
  constructor <;> decide

-- Slot `3` (leader `3`, block `22`) commits directly…
theorem twin6_slot3 :
    AsyncBlueBottle.Decided twin6 (View.full twin6) 3 (some 22) :=
  Decided.directCommit (by decide) (by decide)

-- …and at that anchor only the least twin passes: block `22`'s cone
-- misses validator `5`'s vote for twin `6`.
example : AsyncBlueBottle.coneSupporters twin6 22 0 0 = {0, 1, 2} := by decide
example : AsyncBlueBottle.coneSupporters twin6 22 6 0 = {3, 4} := by decide
example : WeakLink twin6 22 0 0 ∧ ¬ WeakLink twin6 22 6 0 := by decide

/-- The derivation commits the canonical twin. -/
theorem twin6_slot0 :
    AsyncBlueBottle.Decided twin6 (View.full twin6) 0 (some 0) := by
  refine Decided.indirectCommit (i := 0) (by omega) (by decide) twin6_slot3
    ?_ (by decide) (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) (by decide) (by decide) ?_
  · intro i h1 h2 h3
    have : i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl <;> exact absurd h3 (by decide)
  · intro L' hL' ht' hlt
    have hall : ∀ M : Fin 37, IsLeaderBlock twin6 0 M → M = 0 ∨ M = 6 := by decide
    rcases hall L' hL' with h | h <;> subst h
    · exact absurd (show (0 : Fin 37) < 0 from hlt) (lt_irrefl _)
    · exact absurd (show WeakLink _ _ _ _ from ht') (by decide)

/-! ## `hazard6` — the pseudocode's direct rule is order-dependent -/

/-- Round `0`: blocks `0`–`5` and the twin `6` by validator `0`. Round
`1`: validators `0`, `1`, `2` reference twin `0`, validators `3`, `4`,
`5` reference twin `6` (a block cannot reference both, its references
having distinct creators). Round `2`: every block references the whole
of round `1`, so every cone holds both twins. -/
def hazardBlk6 : Fin 19 → Block (Fin 6) (Fin 19) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) = 6 then
    { round := 0, creator := 0, refs := ∅, payload := () }
  else if h : (i : ℕ) < 13 then
    { round := 1, creator := ⟨(i : ℕ) - 7, by omega⟩,
      refs := if (i : ℕ) ≤ 9 then {0, 1, 2, 3, 4}
        else if (i : ℕ) ≤ 11 then {6, 1, 2, 3, 4}
        else {6, 1, 2, 3, 5},
      payload := () }
  else
    { round := 2, creator := ⟨(i : ℕ) - 13, by have := i.isLt; omega⟩,
      refs := {7, 8, 9, 10, 11, 12}, payload := () }

def hazard6 : BlockUniverse (Fin 6) (Fin 19) Unit where
  ids := Finset.univ
  block := hazardBlk6
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- The paper's per-candidate blame: the authors of decision-round blocks
that do **not** vote for `L`, whether they vote for a twin or for
nothing. Local to this witness — the arc's rule blames the slot. -/
def nonVoters (U : BlockUniverse (Fin 6) (Fin 19) Unit) (L : Fin 19) (r : ℕ) :
    Finset (Fin 6) :=
  creatorsOf U.block ((blocksAt U (r + 2)).filter (fun q => ¬ MahiMahi.Votes U q L))

-- Every decision-round cone holds both twins, and every vote goes to
-- the least: twin `0` is directly committed…
example : MahiMahi.candidatesAt hazard6 13 0 0 = {0, 6} := by decide
example : AsyncBlueBottle.supporters hazard6 0 0 = Finset.univ := by decide
theorem hazard6_commit : AsyncBlueBottle.DirectCommit hazard6 0 0 := by decide

-- …while twin `6` has a quorum of per-candidate non-voters: the
-- pseudocode's `SkippedLeader(6)` holds, and `TryDirectDecide` returns
-- `Skip` if it examines twin `6` before twin `0`.
theorem hazard6_skipped_twin : quorumCard (Fin 6) ≤ (nonVoters hazard6 6 0).card := by decide

-- The slot-level blame has no blamer: the arc's `DirectSkip` does not
-- fire, and the slot commits.
example : blamers hazard6 0 0 = ∅ := by decide
example : ¬ AsyncBlueBottle.DirectSkip hazard6 0 0 := by decide
example : AsyncBlueBottle.Decided hazard6 (View.full hazard6) 0 (some 0) :=
  Decided.directCommit (by decide) (by decide)

#print axioms twin6_both_pass
#print axioms twin6_slot0
#print axioms hazard6_commit
#print axioms hazard6_skipped_twin

end LeanDagTest
