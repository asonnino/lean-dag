import LeanDag.Persistence
import LeanDag.CommonCore
open LeanDag

#print axioms LeanDag.BlockUniverse.eq_of_creator_eq
#print axioms LeanDag.BlockUniverse.creators_quorum
#print axioms LeanDag.round_le_of_reaches
#print axioms LeanDag.reaches_of_quorum_support
#print axioms LeanDag.exists_correct_common_support
#print axioms LeanDag.exists_common_correct_ancestor

instance : Faults (Fin 4) where
  f := 1
  byzantine := {0}
  card_validators := by decide
  card_byzantine := by decide

/-- ids 0-3: genesis, one per validator.
    ids 4-7: round 1, validator `i-4`, each referencing genesis `{0,1,2}`. -/
def lk : Fin 8 → Block (Fin 4) (Fin 8) Unit := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else
    { round := 1, creator := ⟨(i : ℕ) - 4, by omega⟩, refs := {0, 1, 2}, payload := () }

/-- A genuine two-round block DAG satisfying ALL FOUR universe conditions. -/
def U : BlockUniverse (Fin 4) (Fin 8) Unit where
  ids := Finset.univ
  block := lk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Inhabited and non-trivial.
example : U.ids.card = 8 := by decide
example : (U.block 4).round = 1 := by decide

-- Validator 1 is correct; validator 0 is Byzantine and so exempt from T1.
example : (1 : Fin 4) ∈ (Correct : Finset (Fin 4)) := by decide
example : (0 : Fin 4) ∉ (Correct : Finset (Fin 4)) := by decide

-- T1 applies to real blocks of a correct author.
example : (5 : Fin 8) = 5 :=
  U.eq_of_creator_eq (v := 1) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide)

-- T1 has real content: validator 1 authors exactly one round-1 block, so no
-- id other than 5 can share its author and round.
example : ∀ j ∈ U.ids, (U.block j).creator = 1 → (U.block j).round = 1 → j = 5 := by decide

-- Refs of a round-1 block carry a real 3-validator quorum (T0's input).
example : 2 * Faults.f (Fin 4) + 1 ≤ (creatorsOf U.block (U.block 4).refs).card :=
  U.creators_quorum (by decide) (by decide)

-- Completeness and the round relation hold on real data.
example : (U.block 4).refs ⊆ U.ids := U.refs_subset (by decide)
example : (U.block 0).round + 1 = (U.block 4).round :=
  U.round_of_mem_refs (i := 4) (j := 0) (by decide) (by decide)

/-! ## Causal history (T2) on the concrete model -/

-- Block 4 (round 1) references genesis 0, 1, 2 -- so it reaches them.
example : Reaches U 4 0 := Reaches.single (by decide)
example : Reaches U 4 2 := Reaches.single (by decide)

-- Reflexivity.
example : Reaches U 4 4 := Reaches.refl

-- T2 has REAL content, not vacuous: genesis 0 does not reach genesis 1.
-- Note both sit at round 0, so this is not merely round monotonicity --
-- `Reaches` genuinely tracks the reference structure.
example : ¬ Reaches U 0 1 := fun h =>
  absurd (eq_of_reaches_of_refs_empty (by decide) h) (by decide)

-- Round monotonicity: nothing at round 0 reaches anything at round 1.
example : ¬ Reaches U 0 4 :=
  not_reaches_of_round_lt (by decide) (by decide)

-- And the positive direction: reaching never raises the round.
example : (U.block 0).round ≤ (U.block 4).round :=
  round_le_of_reaches (by decide) (Reaches.single (by decide))

-- Causal history stays inside the universe.
example : (0 : Fin 8) ∈ U.ids :=
  mem_ids_of_reaches (c := 4) (by decide) (Reaches.single (by decide))

/-! ## Persistence (T3) on a three-round model

The two-round model above cannot exercise T3: it has nothing at round `r+2`.
This extends it to three rounds so the theorem has real content.

ids 0-3   : genesis, one per validator
ids 4-7   : round 1, validator i-4, refs {0,1,2}   -- quorum backing block 0
ids 8-11  : round 2, validator i-8, refs {4,5,6}   -- quorum at round 2
-/

def lk3 : Fin 12 → Block (Fin 4) (Fin 12) Unit := fun i =>
  if h4 : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h8 : (i : ℕ) < 8 then
    { round := 1, creator := ⟨(i : ℕ) - 4, by omega⟩, refs := {0, 1, 2}, payload := () }
  else
    { round := 2, creator := ⟨(i : ℕ) - 8, by omega⟩, refs := {4, 5, 6}, payload := () }

def U3 : BlockUniverse (Fin 4) (Fin 12) Unit where
  ids := Finset.univ
  block := lk3
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Blocks 4,5,6 are a round-1 quorum (3 = 2f+1 distinct authors) backing
-- genesis block 0.
example : 2 * Faults.f (Fin 4) + 1 ≤ (creatorsOf U3.block ({4, 5, 6} : Finset (Fin 12))).card := by
  decide

/-- **T3 applied.** Every round-2 block reaches genesis block 0 -- including
block 11, authored by validator 3, whose own references are {4,5,6} and
which therefore never mentions block 0 directly. -/
example : Reaches U3 11 0 :=
  reaches_of_quorum_support (b := 0) (r := 0) (Q := {4, 5, 6})
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

-- The conclusion is not reachable in one step: block 11 does NOT reference
-- block 0 directly, so T3 is saying something the DAG does not say outright.
example : (0 : Fin 12) ∉ (U3.block 11).refs := by decide

-- The derived facts really are derivable.
example : (0 : Fin 12) ∈ U3.ids ∧ (U3.block 0).round = 0 :=
  mem_ids_and_round_of_quorum_support (b := 0) (r := 0) (Q := {4, 5, 6})
    (by decide) (by decide) (by decide) (by decide)

-- The additive cardinality fact Phase 1b's counting argument divides by.
-- Concretely: 3 correct + 1 Byzantine = 4 = 3f+1 at f = 1.
example :
    (Correct : Finset (Fin 4)).card + (Faults.byzantine : Finset (Fin 4)).card = 3 * 1 + 1 :=
  card_correct_add_byzantine

/-! ## A common correct ancestor (T3a-T3c) on the three-round model -/

-- The round-1 author pool is all four validators, so this is the
-- full-participation case where the counting bound is tight.
example : (authorsAt U3 1).card = 4 := by decide

-- T3c: some correct validator's genesis block is reached by EVERY round-2
-- block. Note block 11 (validator 3) references only {4,5,6}, so this is
-- not something any single block states directly.
example : ∃ bw ∈ U3.ids, (U3.block bw).round = 0 ∧
    (U3.block bw).creator ∈ (Correct : Finset (Fin 4)) ∧
    ∀ c ∈ U3.ids, (U3.block c).round = 2 → Reaches U3 c bw :=
  exists_common_correct_ancestor (c₀ := 8) (by decide) (by decide)

-- T3a in isolation: the support threshold really is met.
example : ∃ bw ∈ U3.ids, (U3.block bw).round = 0 ∧
    (U3.block bw).creator ∈ (Correct : Finset (Fin 4)) ∧
    (authorsAt U3 1).card ≤ (correctSupporters U3 bw 1).card + 2 * Faults.f (Fin 4) :=
  exists_correct_common_support (by decide)

-- The reusable fault-counting lemmas, on concrete sets. At f = 1 with
-- Byzantine = {0}: the quorum {0,1,2} has 2 = f+1 correct members.
example : ({0, 1, 2} : Finset (Fin 4)).card
    ≤ (({0, 1, 2} : Finset (Fin 4)) ∩ (Correct : Finset (Fin 4))).card
      + (Faults.byzantine : Finset (Fin 4)).card :=
  card_le_card_inter_correct_add_byzantine _

example : Faults.f (Fin 4) + 1
    ≤ (({0, 1, 2} : Finset (Fin 4)) ∩ (Correct : Finset (Fin 4))).card :=
  card_inter_correct_of_quorum (by decide)

/-! ## Divergent round-2 views

`U3` has every round-2 block referencing the same `{4,5,6}`, so it never
tests whether T3c depends on round-`(r+2)` blocks agreeing. This model gives
each round-2 block a *different* 2f+1 subset of the round-1 blocks:

  id 8  (validator 0) refs {4,5,6}
  id 9  (validator 1) refs {5,6,7}
  id 10 (validator 2) refs {4,6,7}
  id 11 (validator 3) refs {4,5,7}

No two agree, and no single round-1 block is referenced by all of them.
-/

def lk4 : Fin 12 → Block (Fin 4) (Fin 12) Unit := fun i =>
  if h4 : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h8 : (i : ℕ) < 8 then
    { round := 1, creator := ⟨(i : ℕ) - 4, by omega⟩, refs := {0, 1, 2}, payload := () }
  else
    { round := 2, creator := ⟨(i : ℕ) - 8, by omega⟩,
      refs := if (i : ℕ) = 8 then {4, 5, 6}
              else if (i : ℕ) = 9 then {5, 6, 7}
              else if (i : ℕ) = 10 then {4, 6, 7} else {4, 5, 7},
      payload := () }

def U4 : BlockUniverse (Fin 4) (Fin 12) Unit where
  ids := Finset.univ
  block := lk4
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- The round-2 blocks genuinely disagree, and not just pairwise: the four
-- reference sets have EMPTY common intersection, so there is no round-1
-- block that all of them see.
example : (U4.block 8).refs ∩ (U4.block 9).refs
    ∩ (U4.block 10).refs ∩ (U4.block 11).refs = ∅ := by decide

-- Full participation at round 1, so this is the tight case: threshold
-- p - 2f = 4 - 2 = 2, and the count delivers 2f+1-b = 2.
example : (authorsAt U4 1).card = 4 := by decide

/-- **T3c with divergent views.** Despite no two round-2 blocks referencing
the same round-1 set, a single correct validator's genesis block lies in
*all* of their causal histories. -/
example : ∃ bw ∈ U4.ids, (U4.block bw).round = 0 ∧
    (U4.block bw).creator ∈ (Correct : Finset (Fin 4)) ∧
    ∀ c ∈ U4.ids, (U4.block c).round = 2 → Reaches U4 c bw :=
  exists_common_correct_ancestor (c₀ := 8) (by decide) (by decide)
