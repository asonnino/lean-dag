import LeanDagTest.Odontoceti.Model
import LeanDag.AsyncBlueBottle.Model.Decision
/-!
# Async BlueBottle witnesses — the rule on data

Every definition of `LeanDag/AsyncBlueBottle/Model/` settled by `decide`
on six-validator universes before anything is proved from it
(`async-bluebottle.md` §7). The committee is Odontoceti's boundary
instance — `Fin 6`, validator `0` Byzantine, `f = 1`, DAG quorum and
direct thresholds `5`, indirect threshold `3`. The schedule is a local
instance, slot `k` at round `k` led by `(k + 1) % 6`, so that slot `0`
is led by a correct validator; it shadows the imported `odoSlots`
(leader `k % 6`), which the equivocation witnesses of `Twins.lean` use.

* `full6` — four fully connected rounds: the wave arithmetic, the
  cone vote at the decision round, a direct commit, and the weak link
  from a round-`3` block;
* `aim6` — the **aiming pattern**: the leader's block is kept out of
  every cone but its own, five blamers, a **direct skip** with the
  leader's block present;
* `five6`, `four6` — the direct commit at exactly the quorum, and one
  short of it;
* `icommit6` — slot `0` split three against three at its decision
  round, neither direct rule firing, committed **indirectly** through
  the slot-`3` anchor whose cone carries exactly the threshold;
* `iskip6` — slot `0` split two against four, **indirectly skipped**
  through the same anchor: two voters cannot reach three in any cone.
-/

namespace LeanDagTest

set_option maxRecDepth 4096

open LeanDag LeanDag.AsyncBlueBottle

/-- Round-robin from validator `1`: slot `k` at round `k`, led by
`(k + 1) % 6`. -/
local instance abbSlots : Slots (Fin 6) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨(k + 1) % 6, by omega⟩)

/-! ## `full6` — four rounds, everyone referencing the whole round below -/

/-- Block `6m + v` is validator `v`'s round-`m` block; every non-genesis
block references all six blocks of the round below. -/
def abbFullBlk : Fin 24 → Block (Fin 6) (Fin 24) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 1, creator := ⟨(i : ℕ) - 6, by omega⟩,
      refs := {0, 1, 2, 3, 4, 5}, payload := () }
  else if h : (i : ℕ) < 18 then
    { round := 2, creator := ⟨(i : ℕ) - 12, by omega⟩,
      refs := {6, 7, 8, 9, 10, 11}, payload := () }
  else
    { round := 3, creator := ⟨(i : ℕ) - 18, by have := i.isLt; omega⟩,
      refs := {12, 13, 14, 15, 16, 17}, payload := () }

/-- The fully connected universe: the existing `BlockUniverse` accepts it
unchanged at the `5f + 1` committee, the reuse claim of
`async-bluebottle.md` §2. -/
def full6 : BlockUniverse (Fin 6) (Fin 24) Unit where
  ids := Finset.univ
  block := abbFullBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-! ### The wave arithmetic -/

-- A round-`r` candidate is voted on and decided at round `r + 2`.
example : decisionRoundAt 0 = 2 ∧ decisionRoundAt 3 = 5 := by decide
example : (asyncBlueBottleAnchored (Fin 6) (Fin 24) Unit).decisionRound 0 = 2 := by decide
example : (asyncBlueBottleAnchored (Fin 6) (Fin 24) Unit).decisionRound 3 = 5 := by decide

-- Slot `3` may anchor slot `0`; slot `2` may not: the anchor floor is
-- three rounds above the proposal, at every slot.
example : (asyncBlueBottleAnchored (Fin 6) (Fin 24) Unit).Eligible 0 3 := by decide
example : ¬ (asyncBlueBottleAnchored (Fin 6) (Fin 24) Unit).Eligible 0 2 := by decide
example : (asyncBlueBottleAnchored (Fin 6) (Fin 24) Unit).Eligible 3 6 := by decide
example : ¬ (asyncBlueBottleAnchored (Fin 6) (Fin 24) Unit).Eligible 3 5 := by decide

/-! ### The cone vote at the decision round -/

-- Slot `0`'s candidate is block `1` (round `0`, author `1`).
example : IsLeaderBlock full6 0 1 := by decide

-- Validator `0`'s round-`2` block (id `12`) has exactly one block of
-- author `1` at round `0` in its cone, and votes for it.
example : MahiMahi.candidatesAt full6 12 1 0 = {1} := by decide
example : MahiMahi.Votes full6 12 1 := by decide
example : ¬ MahiMahi.Blames full6 12 1 0 := by decide

-- Every round-`2` block votes for it: a strong certificate.
example : voters full6 1 0 = {12, 13, 14, 15, 16, 17} := by decide
example : AsyncBlueBottle.supporters full6 1 0 = Finset.univ := by decide
example : AsyncBlueBottle.DirectCommit full6 1 0 := by decide
example : ¬ AsyncBlueBottle.DirectSkip full6 1 0 := by decide
example : blamers full6 1 0 = ∅ := by decide

-- The decision, from the full view.
example : AsyncBlueBottle.Decided full6 (View.full full6) 0 (some 1) :=
  Decided.directCommit (by decide) (by decide)

-- The weak link on data: block `19` (round `3`) reaches every voter.
example : AsyncBlueBottle.coneSupporters full6 19 1 0 = Finset.univ := by decide
example : WeakLink full6 19 1 0 := by decide

/-! ## `aim6` — the aiming pattern, and the direct skip -/

/-- Block `6m + v` is validator `v`'s round-`m` block. The target is block
`1`, validator `1`'s round-`0` block. Round `1`: only validator `1` itself
references `1` (its self-parent); the others reference `{0, 2, 3, 4, 5}`.
Round `2`: validator `1` must reference its own block `7` and so reaches
`1`; the others reference `{6, 8, 9, 10, 11}` and do not. The leader's
own vote is pinned by its self-parent chain at two levels, the twist the
three-round wave adds to Odontoceti's one-level skip witness. -/
def aimBlk6 : Fin 18 → Block (Fin 6) (Fin 18) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 1, creator := ⟨(i : ℕ) - 6, by omega⟩,
      refs := if (i : ℕ) = 7 then {1, 2, 3, 4, 5} else {0, 2, 3, 4, 5},
      payload := () }
  else
    { round := 2, creator := ⟨(i : ℕ) - 12, by have := i.isLt; omega⟩,
      refs := if (i : ℕ) = 13 then {6, 7, 8, 9, 10} else {6, 8, 9, 10, 11},
      payload := () }

/-- The aiming pattern is a valid universe: every block references a
quorum including its own author's, and nobody equivocates. Validity is
what makes the pattern available to an asynchronous adversary. -/
def aim6 : BlockUniverse (Fin 6) (Fin 18) Unit where
  ids := Finset.univ
  block := aimBlk6
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Slot `0` is led by validator `1`, whose block `1` is present.
example : IsLeaderBlock aim6 0 1 := by decide

-- Only validator `1`'s decision-round block votes for it; the other five
-- blame the slot — exactly the quorum — so it is **directly skipped**.
example : MahiMahi.Votes aim6 13 1 := by decide
example : MahiMahi.Blames aim6 12 1 0 := by decide
example : blamerBlocks aim6 1 0 = {12, 14, 15, 16, 17} := by decide
example : (blamers aim6 1 0 : Finset (Fin 6)) = {0, 2, 3, 4, 5} := by decide
example : (AsyncBlueBottle.supporters aim6 1 0 : Finset (Fin 6)) = {1} := by decide
example : AsyncBlueBottle.DirectSkip aim6 1 0 := by decide
example : ¬ AsyncBlueBottle.DirectCommit aim6 1 0 := by decide

/-- **The direct skip, as a decision**: the slot is blamed by a quorum in
the full view. -/
theorem aim6_slot0 : AsyncBlueBottle.Decided aim6 (View.full aim6) 0 none :=
  Decided.directSkip (by decide)

/-! ## `five6`, `four6` — the direct commit at the quorum boundary -/

/-- As `aim6`, but at round `2` validators `1` to `5` reference block `7`
and so reach the candidate; only the Byzantine validator omits it. -/
def fiveBlk6 : Fin 18 → Block (Fin 6) (Fin 18) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 1, creator := ⟨(i : ℕ) - 6, by omega⟩,
      refs := if (i : ℕ) = 7 then {1, 2, 3, 4, 5} else {0, 2, 3, 4, 5},
      payload := () }
  else
    { round := 2, creator := ⟨(i : ℕ) - 12, by have := i.isLt; omega⟩,
      refs := if (i : ℕ) = 12 then {6, 8, 9, 10, 11}
        else if (i : ℕ) = 17 then {6, 7, 9, 10, 11}     -- keeps its self-parent 11
        else {6, 7, 8, 9, 10},
      payload := () }

def five6 : BlockUniverse (Fin 6) (Fin 18) Unit where
  ids := Finset.univ
  block := fiveBlk6
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Five voters, exactly the quorum: committed.
example : (AsyncBlueBottle.supporters five6 1 0 : Finset (Fin 6)) = {1, 2, 3, 4, 5} := by decide
example : AsyncBlueBottle.DirectCommit five6 1 0 := by decide

/-- As `five6`, but validator `5` omits block `7` too: four voters. -/
def fourBlk6 : Fin 18 → Block (Fin 6) (Fin 18) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 1, creator := ⟨(i : ℕ) - 6, by omega⟩,
      refs := if (i : ℕ) = 7 then {1, 2, 3, 4, 5} else {0, 2, 3, 4, 5},
      payload := () }
  else
    { round := 2, creator := ⟨(i : ℕ) - 12, by have := i.isLt; omega⟩,
      refs := if (i : ℕ) = 12 ∨ (i : ℕ) = 17 then {6, 8, 9, 10, 11} else {6, 7, 8, 9, 10},
      payload := () }

def four6 : BlockUniverse (Fin 6) (Fin 18) Unit where
  ids := Finset.univ
  block := fourBlk6
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Four voters, one short of the quorum: neither direct rule fires.
example : (AsyncBlueBottle.supporters four6 1 0 : Finset (Fin 6)) = {1, 2, 3, 4} := by decide
example : (blamers four6 1 0 : Finset (Fin 6)) = {0, 5} := by decide
example : ¬ AsyncBlueBottle.DirectCommit four6 1 0 := by decide
example : ¬ AsyncBlueBottle.DirectSkip four6 1 0 := by decide

/-! ## `icommit6` — the indirect commit at exactly the threshold -/

/-- Six rounds of six. Slot `0`'s candidate is block `1` (author `1`).
Round `1`: only its author's own block `7` references it, the other
five omit it. Round `2`: authors `1`, `2`, `3` reference block `7` and so
reach the candidate; authors `0`, `4`, `5` omit it and blame the slot.
Rounds `3` to `5` reference the whole round below. -/
def icommitBlk : Fin 36 → Block (Fin 6) (Fin 36) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 1, creator := ⟨(i : ℕ) - 6, by omega⟩,
      refs := if (i : ℕ) = 7 then {1, 2, 3, 4, 5}    -- the candidate's own child
        else {0, 2, 3, 4, 5},                        -- omits the candidate
      payload := () }
  else if h : (i : ℕ) < 18 then
    { round := 2, creator := ⟨(i : ℕ) - 12, by omega⟩,
      refs := if (i : ℕ) = 13 ∨ (i : ℕ) = 14 ∨ (i : ℕ) = 15 then
          {6, 7, 8, 9, 10}      -- reaches the candidate: a vote
        else {6, 8, 9, 10, 11},  -- does not: a blame
      payload := () }
  else if h : (i : ℕ) < 24 then
    { round := 3, creator := ⟨(i : ℕ) - 18, by omega⟩,
      refs := {12, 13, 14, 15, 16, 17}, payload := () }
  else if h : (i : ℕ) < 30 then
    { round := 4, creator := ⟨(i : ℕ) - 24, by omega⟩,
      refs := {18, 19, 20, 21, 22, 23}, payload := () }
  else
    { round := 5, creator := ⟨(i : ℕ) - 30, by have := i.isLt; omega⟩,
      refs := {24, 25, 26, 27, 28, 29}, payload := () }

def icommit6 : BlockUniverse (Fin 6) (Fin 36) Unit where
  ids := Finset.univ
  block := icommitBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Slot `0` splits three against three: neither direct rule fires.
example : AsyncBlueBottle.supporters icommit6 1 0 = {1, 2, 3} := by decide
example : blamers icommit6 1 0 = {0, 4, 5} := by decide
example : ¬ AsyncBlueBottle.DirectCommit icommit6 1 0 := by decide
example : ¬ AsyncBlueBottle.DirectSkip icommit6 1 0 := by decide

-- Slot `3` (leader `4`, block `22`) commits directly: every round-`5`
-- block reaches it.
theorem icommit6_slot3 :
    AsyncBlueBottle.Decided icommit6 (View.full icommit6) 3 (some 22) :=
  Decided.directCommit (by decide) (by decide)

-- The anchor's cone carries exactly the threshold.
example : AsyncBlueBottle.coneSupporters icommit6 22 1 0 = {1, 2, 3} := by decide
example : WeakLink icommit6 22 1 0 := by decide

/-- **The indirect commit, on data**: slot `0` is undecided by the
direct rules and committed through the slot-`3` anchor — the nearest
eligible one, with nothing eligible between. -/
theorem icommit6_slot0 :
    AsyncBlueBottle.Decided icommit6 (View.full icommit6) 0 (some 1) := by
  refine Decided.indirectCommit (i := 0) (by omega) (by decide) icommit6_slot3
    ?_ (by decide) (fun i' hi' => absurd hi' (Nat.not_lt_zero _)) (by decide) (by decide) ?_
  · intro i h1 h2 h3
    have : i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl <;> exact absurd h3 (by decide)
  · intro L' hL' _ hlt
    have hall : ∀ M : Fin 36, IsLeaderBlock icommit6 0 M → M = 1 := by decide
    have := hall L' hL'
    subst this
    exact absurd (show (1 : Fin 36) < 1 from hlt) (lt_irrefl _)

/-! ## `iskip6` — the indirect skip -/

/-- As `icommit6`, but at round `2` only authors `1` and `2` reach the
candidate: two voters, four blamers. -/
def iskipBlk : Fin 36 → Block (Fin 6) (Fin 36) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 1, creator := ⟨(i : ℕ) - 6, by omega⟩,
      refs := if (i : ℕ) = 7 then {1, 2, 3, 4, 5} else {0, 2, 3, 4, 5},
      payload := () }
  else if h : (i : ℕ) < 18 then
    { round := 2, creator := ⟨(i : ℕ) - 12, by omega⟩,
      refs := if (i : ℕ) = 13 ∨ (i : ℕ) = 14 then {6, 7, 8, 9, 10}
        else {6, 8, 9, 10, 11},
      payload := () }
  else if h : (i : ℕ) < 24 then
    { round := 3, creator := ⟨(i : ℕ) - 18, by omega⟩,
      refs := {12, 13, 14, 15, 16, 17}, payload := () }
  else if h : (i : ℕ) < 30 then
    { round := 4, creator := ⟨(i : ℕ) - 24, by omega⟩,
      refs := {18, 19, 20, 21, 22, 23}, payload := () }
  else
    { round := 5, creator := ⟨(i : ℕ) - 30, by have := i.isLt; omega⟩,
      refs := {24, 25, 26, 27, 28, 29}, payload := () }

def iskip6 : BlockUniverse (Fin 6) (Fin 36) Unit where
  ids := Finset.univ
  block := iskipBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Two voters, four blamers: undecided by the direct rules.
example : AsyncBlueBottle.supporters iskip6 1 0 = {1, 2} := by decide
example : blamers iskip6 1 0 = {0, 3, 4, 5} := by decide
example : ¬ AsyncBlueBottle.DirectCommit iskip6 1 0 := by decide
example : ¬ AsyncBlueBottle.DirectSkip iskip6 1 0 := by decide

theorem iskip6_slot3 :
    AsyncBlueBottle.Decided iskip6 (View.full iskip6) 3 (some 22) :=
  Decided.directCommit (by decide) (by decide)

-- Two voters cannot reach the threshold in **any** cone.
example : AsyncBlueBottle.coneSupporters iskip6 22 1 0 = {1, 2} := by decide
example : ¬ WeakLink iskip6 22 1 0 := by decide

/-- **The indirect skip, on data**: slot `0`, anchored on slot `3`, has
no candidate passing the weak test. -/
theorem iskip6_slot0 :
    AsyncBlueBottle.Decided iskip6 (View.full iskip6) 0 none := by
  refine Decided.indirectSkip (by omega) (by decide) iskip6_slot3 ?_ ?_
  · intro i h1 h2 h3
    have : i = 1 ∨ i = 2 := by omega
    rcases this with rfl | rfl <;> exact absurd h3 (by decide)
  · intro _ _ L hL
    have hall : ∀ M : Fin 36, IsLeaderBlock iskip6 0 M → M = 1 := by decide
    have := hall L hL
    subst this
    change ¬ WeakLink _ _ _ _
    decide

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms full6
#print axioms aim6_slot0
#print axioms icommit6_slot0
#print axioms iskip6_slot0

end LeanDagTest
