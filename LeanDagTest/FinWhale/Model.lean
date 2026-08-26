import LeanDag.FinWhale.Order

/-!
# FinWhale witnesses — the commit rules on data

Every definition of `LeanDag/FinWhale/` settled by `decide` on a concrete
execution before anything is proved from it (`finwhale.md` §7).

The committee is the smallest non-degenerate one: `f = 2` and `p = 2`, so
`n = 3f + 2p − 1 = 9`, the slow-path quorum is `2f + p = 6`, block
validity asks for `n − f = 7` parents and the fast path asks for
`n − p = 7` votes. At `p = 1` the slow-path quorum and the validity
quorum coincide, and the gap between them would go untested.

Three executions, because the rules they exercise exclude one another.
`Dfast` commits the round-0 leader by both paths. `Dequiv` has the leader
equivocate, and separates the two branches of FP-evidence. `Dskip` skips
the slot.
-/

namespace LeanDagTest

namespace FinWhale

set_option maxRecDepth 4000
set_option synthInstance.maxSize 1000
set_option synthInstance.maxHeartbeats 1000000

open LeanDag LeanDag.FinWhale

/-- Nine validators, two of them Byzantine. -/
local instance fwFaults : Faults (Fin 9) where
  f := 2
  byzantine := {0, 1}
  card_validators := by decide
  card_byzantine := by decide

/-- One fast-path slot: `p = 2`, so `n + 1 = 3f + 2p = 10`. -/
local instance fwParams : Params (Fin 9) where
  p := 2
  p_pos := by omega
  p_le_f := by decide
  card_add_one := by decide

/-- The committee's numbers, as the arc reads them. -/
example : spQuorum (Fin 9) = 6 ∧ fastCard (Fin 9) = 7 ∧ quorumCard (Fin 9) = 7 := by decide

/-- The slow-path quorum is strictly below the validity quorum, which is
what `p = 2` separates and `p = 1` would hide. -/
example : spQuorum (Fin 9) < quorumCard (Fin 9) := by decide

/-- Round robin: round `r` is led by validator `r % 9`. -/
def fwLeader : ℕ → Fin 9 := fun r => ⟨r % 9, Nat.mod_lt _ (by omega)⟩

/-! ## `Dfast` — the slot committed, by both paths

Four rounds of nine blocks: id `i` sits at round `i / 9` and is authored
by validator `i % 9`. Validators `0` to `6` vote for the round-0 leader
block, which is `n − p = 7` votes and a fast commit; validators `7` and
`8` do not. Every round-2 block carries `7` parents voting for it, above
the slow-path quorum of `6`, so the slot is committed by either path. -/
def fastBlk : Fin 36 → Block (Fin 9) (Fin 36) Unit := fun i =>
  { round := (i : ℕ) / 9,
    creator := ⟨(i : ℕ) % 9, Nat.mod_lt _ (by omega)⟩,
    refs :=
      if (i : ℕ) < 9 then ∅
      else if (i : ℕ) < 16 then {0, 1, 2, 3, 4, 5, 6}
      else if (i : ℕ) < 18 then {1, 2, 3, 4, 5, 6, 7}
      else if (i : ℕ) < 27 then {9, 10, 11, 12, 13, 14, 15}
      else {18, 19, 20, 21, 22, 23, 24},
    payload := () }

theorem fastValid : ∀ i : Fin 36, ValidHere fastBlk fwLeader (fastBlk i) := by
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩ <;> revert i <;> decide

/-- The execution, with all three DAG conditions by `decide`. -/
def Dfast : Dag (Fin 9) (Fin 36) Unit where
  ids := Finset.univ
  block := fastBlk
  leader := fwLeader
  complete := by decide
  valid := fun i _ => fastValid i
  correct_single := by decide

/-! ### The votes

Seven validators vote for the round-0 leader block, two do not. Seven is
`n − p`, so the fast path fires; the two abstainers are two short of the
slow-path skip quorum of six. -/

example : slotBlocks Dfast 0 = {0} := by decide

example : voters Dfast 0 = {0, 1, 2, 3, 4, 5, 6} ∧ nonVoters Dfast 0 = {7, 8} := by decide

example : FastCommit Dfast 0 := by decide

example : ¬ SPSkip Dfast 0 := by decide

/-! ### The slow path

Every round-2 block carries seven parents voting for the leader block,
one above the slow-path quorum, so each is an SP-certificate and six of
them are a slow-path commit. -/

example : parentsVoting Dfast 18 0 = {0, 1, 2, 3, 4, 5, 6} := by decide

example : SPCertificate Dfast 18 0 := by decide

/-- The certificates of validators `0` to `5` are a slow-path commit. -/
example : SPCommit Dfast 0 :=
  ⟨{0, 1, 2, 3, 4, 5}, by decide, by decide⟩

example : DirectCommit Dfast 0 := Or.inl (by decide)

/-- **The slot is not skipped**, by Lemma 6 rather than by search. -/
example : ¬ DirectSkip Dfast 0 :=
  no_directSkip_of_commit (l := 0) (by decide) (Or.inl (by decide))

/-! ### The fast path's evidence

No round-2 block has seen an equivocation here, so FP-evidence is the
weaker branch: `f + p − 1 = 3` parents voting, against the seven each of
them has. -/

example : ¬ ExposesEquivocation Dfast 18 := by decide

example : FPEvidence Dfast 18 0 := by decide

/-- Lemma 4 on data: under the fast commit, *every* round-2 block is
FP-evidence for the committed block. -/
example : ∀ b ∈ blocksAt Dfast 2, FPEvidence Dfast b 0 := by decide

/-! ### The anchor

A round-3 block reaches a round-2 certificate in one step, which is the
indirect rule's first route. -/

example : IndirectCommit Dfast 27 0 0 :=
  ⟨by decide, Or.inl ⟨18, by decide, ReachesFrom.single (by decide), by decide⟩⟩

/-! ## `Dequiv` — the leader equivocates

Three rounds of nine blocks, plus id `27`: a second round-0 block by
validator `0`, who is Byzantine and is the leader of round `0`. Five
round-1 blocks vote for one version, two for the other, two for neither,
so neither version reaches a quorum and the slot is decided by nobody
directly.

The round-2 blocks are where the two branches of FP-evidence separate.
Block `18` has seen both versions and carries the `f + p = 4` parents
voting for the first that the equivocating branch demands, against `2`
for the second. Block `19` has seen only the first, and the branch for a
block that has not seen the equivocation asks it for `f + p − 1 = 3`.
Block `20` has seen both and carries too few of either.

Validity is what forces block `18` to drop the leader's own round-1
block: a block whose parents disagree about the leader must exclude the
leader from its parents, which is `leader_not_parent_of_exposes`. -/
def eqBlk : Fin 28 → Block (Fin 9) (Fin 28) Unit := fun i =>
  if (i : ℕ) = 27 then
    { round := 0, creator := 0, refs := ∅, payload := () }
  else
  { round := (i : ℕ) / 9,
    creator := ⟨(i : ℕ) % 9, Nat.mod_lt _ (by omega)⟩,
    refs :=
      if (i : ℕ) < 9 then ∅
      else if (i : ℕ) < 14 then {0, 1, 2, 3, 4, 5, 6}
      else if (i : ℕ) < 16 then {27, 1, 2, 3, 4, 5, 6}
      else if (i : ℕ) < 18 then {1, 2, 3, 4, 5, 6, 7}
      else if (i : ℕ) = 18 then {10, 11, 12, 13, 14, 15, 16}
      else if (i : ℕ) = 20 then {11, 12, 13, 14, 15, 16, 17}
      else {9, 10, 11, 12, 13, 16, 17},
    payload := () }

theorem eqValid : ∀ i : Fin 28, ValidHere eqBlk fwLeader (eqBlk i) := by
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩ <;> revert i <;> decide

/-- The equivocating execution. Validator `0` is Byzantine, so
`correct_single` still holds. -/
def Dequiv : Dag (Fin 9) (Fin 28) Unit where
  ids := Finset.univ
  block := eqBlk
  leader := fwLeader
  complete := by decide
  valid := fun i _ => eqValid i
  correct_single := by decide

/-- The slot has two blocks, and they conflict. -/
example : slotBlocks Dequiv 0 = {0, 27} ∧ Conflicting Dequiv 0 27 := by decide

/-- The author of both is Byzantine — the only way `correct_single`
admits the pair. -/
example : (Dequiv.block 0).creator ∉ (Correct : Finset (Fin 9)) := by decide

/-- Neither version is committed or skipped: five votes and two against
the slow-path quorum of six, and four abstentions against the skip
quorum. -/
example : voters Dequiv 0 = {0, 1, 2, 3, 4} ∧ voters Dequiv 27 = {5, 6} := by decide

example : ¬ DirectCommit Dequiv 0 ∧ ¬ DirectCommit Dequiv 27 ∧ ¬ DirectSkip Dequiv 0 := by
  refine ⟨by decide, by decide, ?_⟩
  intro h
  exact absurd (h.1 0 (by decide)) (by decide)

/-! ### The two branches -/

/-- Block `18` has seen the equivocation, and its counts meet the
equivocating branch for one version and fail it for the other. -/
example : ExposesEquivocation Dequiv 18 ∧
    parentsVoting Dequiv 18 0 = {1, 2, 3, 4} ∧ parentsVoting Dequiv 18 27 = {5, 6} := by decide

example : FPEvidence Dequiv 18 0 ∧ ¬ FPEvidence Dequiv 18 27 := by decide

/-- Block `19` has not seen it, and the weaker branch applies. -/
example : ¬ ExposesEquivocation Dequiv 19 ∧ parentsVoting Dequiv 19 0 = {0, 1, 2, 3, 4} := by
  decide

example : FPEvidence Dequiv 19 0 ∧ ¬ FPEvidence Dequiv 19 27 := by decide

/-- Block `20` has seen the equivocation and carries too few of either
version: evidence for nothing in the slot. -/
example : NonFPEvidence Dequiv 20 (slotBlocks Dequiv 0) := by decide

/-- **The validity clause on data.** Block `18` exposes the equivocation,
so its parents exclude the leader's own round-1 block — `9`, which every
other round-2 block here carries. -/
example : (9 : Fin 28) ∉ (Dequiv.block 18).refs ∧ (9 : Fin 28) ∈ (Dequiv.block 19).refs := by
  decide

example : Dequiv.leader ((Dequiv.block 18).round - 2) ∉ parentSet Dequiv 18 :=
  leader_not_parent_of_exposes (D := Dequiv) (b := 18) (by decide) (by decide) (by decide)

/-- And the leader of the slot is validator `0`, whose round-1 block is
`9`: the parent block `18` had to drop. -/
example : Dequiv.leader ((Dequiv.block 18).round - 2) = 0 ∧
    (Dequiv.block 9).creator = 0 := by decide

/-! ## `Dskip` — the slot skipped

Three rounds of nine blocks, and no round-1 block references the round-0
leader. All nine validators decline, above the skip quorum of six, and no
round-2 block is FP-evidence for anything in the slot. -/
def skipBlk : Fin 27 → Block (Fin 9) (Fin 27) Unit := fun i =>
  { round := (i : ℕ) / 9,
    creator := ⟨(i : ℕ) % 9, Nat.mod_lt _ (by omega)⟩,
    refs :=
      if (i : ℕ) < 9 then ∅
      else if (i : ℕ) < 18 then {1, 2, 3, 4, 5, 6, 7}
      else {9, 10, 11, 12, 13, 14, 15},
    payload := () }

theorem skipValid : ∀ i : Fin 27, ValidHere skipBlk fwLeader (skipBlk i) := by
  intro i
  refine ⟨?_, ?_, ?_, ?_⟩ <;> revert i <;> decide

/-- The skipping execution. -/
def Dskip : Dag (Fin 9) (Fin 27) Unit where
  ids := Finset.univ
  block := skipBlk
  leader := fwLeader
  complete := by decide
  valid := fun i _ => skipValid i
  correct_single := by decide

example : slotBlocks Dskip 0 = {0} ∧ voters Dskip 0 = ∅ := by decide

example : SPSkip Dskip 0 ∧ nonVoters Dskip 0 = {0, 1, 2, 3, 4, 5, 6, 7, 8} := by decide

example : ∀ b ∈ blocksAt Dskip 2, NonFPEvidence Dskip b (slotBlocks Dskip 0) := by decide

/-- The direct skip, on the certificates of validators `0` to `5`. -/
example : DirectSkip Dskip 0 :=
  ⟨by decide, {0, 1, 2, 3, 4, 5}, by decide, by decide⟩

example : ¬ DirectCommit Dskip 0 := by decide

/-- **No anchor can reverse it**, whatever it reaches: the skip pattern
denies both routes of the indirect rule. -/
example (A : Fin 27) : ¬ IndirectCommit Dskip A 0 0 :=
  no_indirectCommit_of_directSkip ⟨by decide, {0, 1, 2, 3, 4, 5}, by decide, by decide⟩

/-! ## The commit sequence and the delivered order

The list layer, on concrete verdicts. A validator that commits at slot
`0`, skips slot `1` and has not decided slot `2` commits one block; a
validator that has decided one slot further commits a sequence extending
it, and the delivery orders extend likewise. -/

/-- Two verdict assignments, the second deciding one slot further. -/
def decA : ℕ → Verdict (Fin 4) := fun s =>
  if s = 0 then Verdict.commit 1 else if s = 1 then Verdict.skip else Verdict.undecided

/-- The same, with slot `2` committed. -/
def decB : ℕ → Verdict (Fin 4) := fun s =>
  if s = 0 then Verdict.commit 1 else if s = 1 then Verdict.skip
  else if s = 2 then Verdict.commit 2 else Verdict.undecided

example : commitSeq decA 2 = [1] ∧ commitSeq decB 3 = [1, 2] := by decide

/-- Lemma 13 on data: the shorter sequence is a prefix of the longer. -/
example : commitSeq decA 2 <+: commitSeq decB 3 ∨ commitSeq decB 3 <+: commitSeq decA 2 :=
  lemma13 (k := 2) (k' := 3)
    (by
      intro s h1 _
      match s with
      | 0 => rfl
      | 1 => rfl
      | (n + 2) => exact absurd (by simp [decA]) h1)
    (by decide) (by decide)

/-- Anti-vacuity: the two sequences are not the same list, so the prefix
above has content. -/
example : commitSeq decA 2 ≠ commitSeq decB 3 := by decide

/-- A causal history per block: everything reaches the genesis block `0`. -/
def histFW : Fin 4 → List (Fin 4) := fun b => if b = 0 then [0] else [b, 0]

/-- The delivery order, on histories that overlap: the second leader's
history repeats a block the first already delivered, and it is delivered
once. -/
example : linearise histFW [1, 2] = [1, 0, 2] := by decide

/-- Theorem 14 on the same data: one more leader extends the order rather
than revising it. -/
example : linearise histFW [1] <+: linearise histFW [1, 2] :=
  theorem14 _ ⟨[2], by decide⟩

/-- Theorem 15: block `0` lies in both histories and is delivered once. -/
example : (linearise histFW [1, 2]).Nodup := theorem15 _ (by decide) _

/-! ## The arc's axioms -/

#print axioms LeanDag.FinWhale.lemma12
#print axioms LeanDag.FinWhale.safety

end FinWhale

end LeanDagTest
