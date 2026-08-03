import LeanDag.CausalHistory
open LeanDag

#print axioms LeanDag.BlockUniverse.eq_of_creator_eq
#print axioms LeanDag.BlockUniverse.creators_quorum
#print axioms LeanDag.round_le_of_reaches

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
