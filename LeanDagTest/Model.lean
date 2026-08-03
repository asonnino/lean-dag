import LeanDag.Persistence
import LeanDag.CommonCore
import LeanDag.Mysticeti
open LeanDag

#print axioms LeanDag.BlockUniverse.eq_of_creator_eq
#print axioms LeanDag.BlockUniverse.creators_quorum
#print axioms LeanDag.round_le_of_reaches
#print axioms LeanDag.reaches_of_quorum_support
#print axioms LeanDag.exists_correct_common_support
#print axioms LeanDag.exists_common_correct_ancestor
#print axioms LeanDag.certificates_eq_empty_of_directSkip
#print axioms LeanDag.not_directCommit_of_directSkip
#print axioms LeanDag.exists_certificate_reaches_of_directCommit
#print axioms LeanDag.eq_of_directCommit_of_creator_eq
#print axioms LeanDag.View.mem_of_reaches
#print axioms LeanDag.indirect_agrees_with_direct

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

/-! ## Mysticeti direct rules (M1, M3) on the three-round model

`U3` exercises both sides. Round-1 blocks 4-7 all reference `{0,1,2}`, so:

  * genesis block 0 is voted for by every round-1 block, and every round-2
    block gathers 3 = 2f+1 such votes -- so block 0 is DIRECTLY COMMITTED;
  * genesis block 3 is referenced by nobody at round 1 -- so it is
    DIRECTLY SKIPPED.

Without both of these the M-theorems would be vacuous.
-/

-- Every round-1 block votes for genesis 0; block 3 gets no votes at all.
example : supporters U3 0 1 = {0, 1, 2, 3} := by decide
example : supporters U3 3 1 = ∅ := by decide
example : blames U3 3 1 = {0, 1, 2, 3} := by decide

-- Block 8 certifies genesis 0: its refs {4,5,6} are votes by 3 = 2f+1 authors.
example : Certifies U3 8 0 := by decide

-- DirectCommit is satisfiable -- so M1 is not vacuous.
example : DirectCommit U3 0 0 := by decide

-- DirectSkip is satisfiable, on a different block of the same round.
example : DirectSkip U3 3 0 := by decide

-- **M3** on real data: the skipped block has no certificate anywhere.
example : certificates U3 3 0 = ∅ :=
  certificates_eq_empty_of_directSkip (by decide)

-- **M1** on real data: the skipped block cannot also be committed.
example : ¬ DirectCommit U3 3 0 :=
  not_directCommit_of_directSkip (by decide)

-- And the two are genuinely different blocks of the same round: block 0 is
-- committed and NOT skipped, block 3 is skipped and NOT committed.
example : ¬ DirectSkip U3 0 0 := by decide

/-! ## M2 needs a fourth round

`U3` stops at round 2, so M2 -- which speaks about blocks at round `r+3` --
would be vacuous on it. `U5` adds a round:

  ids 0-3    round 0, genesis
  ids 4-7    round 1, refs {0,1,2}
  ids 8-11   round 2, refs {4,5,6}     -- these certify genesis block 0
  ids 12-15  round 3, refs {8,9,10}
-/

def lk5 : Fin 16 → Block (Fin 4) (Fin 16) Unit := fun i =>
  if h4 : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h8 : (i : ℕ) < 8 then
    { round := 1, creator := ⟨(i : ℕ) - 4, by omega⟩, refs := {0, 1, 2}, payload := () }
  else if h12 : (i : ℕ) < 12 then
    { round := 2, creator := ⟨(i : ℕ) - 8, by omega⟩, refs := {4, 5, 6}, payload := () }
  else
    { round := 3, creator := ⟨(i : ℕ) - 12, by omega⟩, refs := {8, 9, 10}, payload := () }

def U5 : BlockUniverse (Fin 4) (Fin 16) Unit where
  ids := Finset.univ
  block := lk5
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Genesis block 0 is directly committed, and its certificates really exist.
example : DirectCommit U5 0 0 := by decide
example : Certifies U5 8 0 := by decide

/-- **M2 applied.** Block 12 sits at round 3 = r+3 and has a certificate for
genesis block 0 in its causal history -- though it references neither block 0
nor any round-1 voter directly. -/
example : ∃ C ∈ certificates U5 0 0, Reaches U5 12 C :=
  exists_certificate_reaches_of_directCommit (by decide) (by decide) (by decide)

-- The indirection is real: block 12's own references are {8,9,10}.
example : (0 : Fin 16) ∉ (U5.block 12).refs := by decide
example : (4 : Fin 16) ∉ (U5.block 12).refs := by decide

/-! ## M5 needs an EQUIVOCATING leader to say anything

Every model above has one block per validator per round, so M5 would only
ever be applied with `L₁ = L₂` -- true but empty. `U6` gives the Byzantine
validator 0 **two** genesis blocks, which non-equivocation permits precisely
because it is Byzantine:

  ids 0-3   round 0, genesis by validators 0,1,2,3
  id  4     round 0, a SECOND genesis by validator 0   -- equivocation
  ids 5-8   round 1, refs {0,1,2}
  ids 9-12  round 2, refs {5,6,7}

Block 0 is directly committed. Block 4 has the same author and round, so M5
forbids it from also being committed -- which is the Byzantine-leader case
the whole distinctness invariant exists to handle.
-/

def lk6 : Fin 13 → Block (Fin 4) (Fin 13) Unit := fun i =>
  if h4 : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if (i : ℕ) = 4 then
    { round := 0, creator := 0, refs := ∅, payload := () }
  else if h9 : (i : ℕ) < 9 then
    { round := 1, creator := ⟨(i : ℕ) - 5, by omega⟩, refs := {0, 1, 2}, payload := () }
  else
    { round := 2, creator := ⟨(i : ℕ) - 9, by omega⟩, refs := {5, 6, 7}, payload := () }

def U6 : BlockUniverse (Fin 4) (Fin 13) Unit where
  ids := Finset.univ
  block := lk6
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- Validator 0 really does equivocate at round 0, and it is Byzantine.
example : (U6.block 0).creator = (U6.block 4).creator := by decide
example : (U6.block 0).round = (U6.block 4).round := by decide
example : (0 : Fin 13) ≠ 4 := by decide
example : (0 : Fin 4) ∉ (Correct : Finset (Fin 4)) := by decide

-- One of the two equivocating blocks is directly committed.
example : DirectCommit U6 0 0 := by decide

/-- **M5 applied.** The other one therefore cannot be — the conclusion is a
consequence of the theorem, not of the model being small. -/
example : ¬ DirectCommit U6 4 0 := fun h4 =>
  absurd (eq_of_directCommit_of_creator_eq (L₁ := 0) (L₂ := 4) (by decide) h4 (by decide))
    (by decide)

/-! ## Views and T6a

A view must be a *strict* subset to test anything -- over the whole universe
T6a is trivial. `V5` holds only part of `U5`, chosen downward-closed:

  {0,1,2}  round-0 blocks
  {4,5,6}  round-1 blocks, whose refs {0,1,2} are all present
  {8}      one round-2 block, whose refs {4,5,6} are all present

and omits 3, 7, 9-15.
-/

def V5 : View (Fin 4) (Fin 16) Unit U5 where
  ids := {0, 1, 2, 4, 5, 6, 8}
  subset_ids := by decide
  complete := by decide

-- The view is genuinely partial.
example : (8 : Fin 16) ∈ V5.ids := by decide
example : (3 : Fin 16) ∉ V5.ids := by decide
example : (12 : Fin 16) ∉ V5.ids := by decide

-- **T6a.** Causal history cannot escape the view: block 8 reaches genesis 0
-- two steps down, and 0 is in the view because it had to be.
example : (0 : Fin 16) ∈ V5.ids :=
  View.mem_of_reaches (V := V5) (c := 8) (by decide)
    (Reaches.of_mem_refs (i := 8) (j := 4) (by decide) (Reaches.single (by decide)))

/-- T6a has real content: since genesis 3 is outside the view, no block the
view holds can reach it. The view's boundary is a causal boundary. -/
example : ¬ Reaches U5 8 3 := fun h =>
  absurd (View.mem_of_reaches (V := V5) (c := 8) (by decide) h) (by decide)

/-! ## M4: the indirect test agrees with the direct rule

`U5` decides two genesis blocks in opposite directions, so one anchor can be
checked against both. Round-1 blocks all reference `{0,1,2}`, so block 0 is
directly committed while block 3 is directly skipped. Block 12 sits at round
3 = r+3 and serves as the anchor.
-/

example : DirectCommit U5 0 0 := by decide
example : DirectSkip U5 3 0 := by decide
example : (U5.block 12).round = 3 := by decide

-- The anchor finds a certificate for the committed block ...
example : CertifiedIn U5 12 0 0 :=
  certifiedIn_of_directCommit (by decide) (by decide) (by decide)

-- ... and none for the skipped one. Same anchor, opposite verdicts, both
-- matching the direct rule.
example : ¬ CertifiedIn U5 12 3 0 :=
  not_certifiedIn_of_directSkip (by decide)

/-! ### The same verdict from inside a view

`V5'` is a strict view holding block 12 and exactly its causal history. -/

def V5' : View (Fin 4) (Fin 16) Unit U5 where
  ids := {0, 1, 2, 4, 5, 6, 8, 9, 10, 12}
  subset_ids := by decide
  complete := by decide

example : (7 : Fin 16) ∉ V5'.ids := by decide
example : (13 : Fin 16) ∉ V5'.ids := by decide

/-- A validator holding only `V5'` still finds the certificate, and finds it
*inside its own view* -- derived from the universe-level fact via T6a. -/
example : ∃ C, C ∈ V5'.ids ∧ C ∈ certificates U5 0 0 ∧ Reaches U5 12 C :=
  (certifiedIn_iff_of_view (V := V5') (by decide)).mpr
    (certifiedIn_of_directCommit (by decide) (by decide) (by decide))

/-! ## C1: the decision relation is inhabited, including indirectly

Every model above decides each round-0 block *directly* -- all round-1 blocks
reference the same set, so a block is either fully voted or fully blamed. To
reach the indirect constructors a slot must be genuinely UNDECIDED: some
certificate exists, but too few to commit and too few blames to skip.

`U7` arranges that, over six rounds (slots at rounds 0 and 3 need round 5 to
certify the later one):

  round 0  ids 0-3     genesis
  round 1  ids 4-7     4,5,6 ref {0,1,2};  7 refs {1,2,3}
  round 2  ids 8-11    8 refs {4,5,6};     9,10,11 ref {5,6,7}
  round 3  ids 12-15   ref {8,9,10}
  round 4  ids 16-19   ref {12,13,14}
  round 5  ids 20-23   ref {16,17,18}

Block 0 then has exactly ONE certificate (block 8) -- one creator, short of
2f+1 -- and exactly ONE blamer (block 7), also short. Undecided both ways.
-/

def lk7 : Fin 24 → Block (Fin 4) (Fin 24) Unit := fun i =>
  if h : (i : ℕ) < 4 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 8 then
    { round := 1, creator := ⟨(i : ℕ) - 4, by omega⟩,
      refs := if (i : ℕ) = 7 then {1, 2, 3} else {0, 1, 2}, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 2, creator := ⟨(i : ℕ) - 8, by omega⟩,
      refs := if (i : ℕ) = 8 then {4, 5, 6} else {5, 6, 7}, payload := () }
  else if h : (i : ℕ) < 16 then
    { round := 3, creator := ⟨(i : ℕ) - 12, by omega⟩, refs := {8, 9, 10}, payload := () }
  else if h : (i : ℕ) < 20 then
    { round := 4, creator := ⟨(i : ℕ) - 16, by omega⟩, refs := {12, 13, 14}, payload := () }
  else
    { round := 5, creator := ⟨(i : ℕ) - 20, by omega⟩, refs := {16, 17, 18}, payload := () }

def U7 : BlockUniverse (Fin 4) (Fin 24) Unit where
  ids := Finset.univ
  block := lk7
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- Slots every three rounds, always led by validator 0. -/
instance : Slots (Fin 4) where
  slotRound k := 3 * k
  leader _ := 0
  spacing k := by omega

def V7 : View (Fin 4) (Fin 24) Unit U7 where
  ids := Finset.univ
  subset_ids := by decide
  complete := by decide

-- Slot 0's candidate is genesis block 0; slot 1's is block 12.
example : IsLeaderBlock U7 0 0 := by decide
example : IsLeaderBlock U7 1 12 := by decide

-- Slot 0 is genuinely UNDECIDED: one certificate, one blamer, neither a quorum.
example : certificates U7 0 0 = {8} := by decide
example : ¬ DirectCommit U7 0 0 := by decide
example : ¬ DirectSkip U7 0 0 := by decide

-- Slot 1 IS directly committed, so it can serve as slot 0's anchor.
example : DirectCommitIn U7 V7 12 3 := by decide

/-- **The indirect rule fires.** Slot 0 is undecided directly, but slot 1 is
directly committed and its leader block (12) reaches the lone certificate
(8) for slot 0's candidate. So slot 0 is committed *indirectly*, anchored on
the nearest committed slot after it.

This inhabits `Decided`'s indirect constructor — the case the whole Stage C
argument is about. -/
example : Decided U7 V7 0 (some 0) :=
  Decided.indirectCommit (j := 1) (A := 12) (by omega)
    (Decided.directCommit (by decide) (by decide))
    (fun i h1 h2 => absurd h2 (by omega))
    (by decide)
    ⟨8, by decide, Reaches.single (by decide)⟩

-- The anchor really is two rounds of indirection away from the certificate's
-- own evidence: block 12 does not reference slot 0's candidate directly.
example : (0 : Fin 24) ∉ (U7.block 12).refs := by decide

/-! ## C2: the direct rules lifted to views

`U5` with the standard schedule: slot 0 sits at round 0, slot 1 at round 3.
`V5'` is a *partial* view -- it holds three of the four certificates for
genesis block 0, which is still a quorum, so it commits slot 0 locally.
-/

example : IsLeaderBlock U5 0 0 := by decide
example : IsLeaderBlock U5 1 12 := by decide

-- A strictly partial view still reaches the quorum.
example : certificates U5 0 0 = {8, 9, 10, 11} := by decide
example : (11 : Fin 16) ∉ V5'.ids := by decide
example : DirectCommitIn U5 V5' 0 0 := by decide

/-- **The engine of M6, on real data.** A commit made in the partial view
`V5'` is visible from slot 1's leader block -- so a validator that never saw
that commit still recovers it indirectly. The slot spacing discharges the
round hypothesis. -/
example : CertifiedIn U5 12 0 0 :=
  certifiedIn_of_directCommitIn (V := V5') (k := 0) (j := 1) (L := 0) (A := 12)
    (by decide) (by decide) (by decide) (by omega)

/-- Cross-view M1: since *some* view commits genesis block 0, **no** view can
directly skip it -- whatever that other validator happens to hold. -/
example (V : View (Fin 4) (Fin 16) Unit U5) : ¬ DirectSkipIn U5 V 0 0 :=
  fun h => not_directSkipIn_of_directCommitIn (V₁ := V5') (by decide) h
