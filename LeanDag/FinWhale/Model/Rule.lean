import LeanDag.FinWhale.Counting
import LeanDag.Causality

/-!
# FinWhale — the fast path, as the paper defines it

The counting of `Counting.lean` is Lemma 4's arithmetic. This file is the
vocabulary the paper states Lemma 4 in: votes, leader-consistency, the
two branches of FP-evidence, and the direct decision rules. Only what the
fast path needs is modelled; the slow path is Mysticeti's and unchanged.

**Two readings of "exposes equivocation", and only one of them works.**
The paper writes: "a block `b′` of round `r+2` exposes equivocation by
`Lr` if its parent set is not leader-consistent, i.e., its causal history
contains multiple conflicting versions of `Lr`'s block". The two halves
of that sentence are not the same condition. A parent set that votes for
two versions puts both in the causal history, so the first implies the
second; the converse fails, since a history can carry both versions
through a grandparent while every parent votes for at most one.

The reading matters, because Lemma 4's equivocating branch needs the
*parent-set* one. Its argument is that a block exposing equivocation may
not reference `Lr`'s block, so at most `f − 1` of its parents are
Byzantine — and that comes from the block-validity rule, which is itself
stated over the parent set: a round-`r` block is valid when its parents
are leader-consistent with respect to `Lr₋₂`, **or** exclude `Lr₋₂`'s
block. A block whose parents are leader-consistent satisfies the first
clause and is under no obligation to exclude anything, whatever its
deeper history holds. So under the causal-history reading the `f − 1`
bound is unavailable and the branch is unsupported.

`ExposesEquivocation` is therefore the parent-set condition, and
`ExposesEquivocationHistory` is kept beside it to state the difference
(`exposes_of_parents`, and the converse refuted on data in
`LeanDagTest/FinWhale/Reading`).
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **Validity, as FinWhale extends Mysticeti's.** Every edge sits in the
round below, at most one edge per validator, a non-genesis block carries
`n − f` of them by distinct validators, and the parent set is either
leader-consistent with respect to the leader two rounds down or excludes
that leader's block. The last clause is FinWhale's addition and is what
the fast path's counting rests on. -/
structure ValidHere (blk : BlockId → Block Validator BlockId Payload)
    (leader : ℕ → Validator) (b : Block Validator BlockId Payload) : Prop where
  /-- Every edge points to the round immediately below. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- No two edges share a validator. -/
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  /-- A non-genesis block carries `n − f` edges by distinct validators. -/
  quorum : 0 < b.round → quorumCard Validator ≤ (creators blk b).card
  /-- **FinWhale's clause.** Either the parents agree on the leader two
  rounds down, or that leader's block is not among them. -/
  leader_clause : 2 ≤ b.round →
    (∀ i ∈ b.refs, ∀ j ∈ b.refs,
      (blk i).creator = leader (b.round - 2) → (blk j).creator = leader (b.round - 2) → i = j)
    ∨ (∀ i ∈ b.refs, (blk i).creator ≠ leader (b.round - 2))

/-- A DAG the communication component can build. Equivocating blocks are
admitted, of faulty validators only. -/
structure Dag (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [Params Validator] [DecidableEq BlockId] where
  /-- Which blocks exist. -/
  ids : Finset BlockId
  /-- What each identifier denotes. -/
  block : BlockId → Block Validator BlockId Payload
  /-- The leader schedule. -/
  leader : ℕ → Validator
  /-- The DAG is closed under edges. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  /-- Every block is valid. -/
  valid : ∀ i ∈ ids, ValidHere block leader (block i)
  /-- Only a faulty validator issues two blocks in one round. -/
  correct_single : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator ∈ (Correct : Finset Validator) →
    (block i).creator = (block j).creator →
    (block i).round = (block j).round → i = j

variable {D : Dag Validator BlockId Payload}

/-- The blocks of a round. -/
def blocksAt (D : Dag Validator BlockId Payload) (r : ℕ) : Finset BlockId :=
  D.ids.filter (fun b => (D.block b).round = r)

/-- The validators whose round-`(r+1)` block references `l`: `l`'s voters. -/
def voters (D : Dag Validator BlockId Payload) (l : BlockId) : Finset Validator :=
  creatorsOf D.block ((blocksAt D ((D.block l).round + 1)).filter
    (fun q => l ∈ (D.block q).refs))

/-- The parents of `b`, as validators. -/
def parentSet (D : Dag Validator BlockId Payload) (b : BlockId) : Finset Validator :=
  creatorsOf D.block ((D.block b).refs)

/-- The parents of `b` that vote for the leader block `l`. -/
def parentsVoting (D : Dag Validator BlockId Payload) (b l : BlockId) : Finset Validator :=
  creatorsOf D.block (((D.block b).refs).filter (fun q => l ∈ (D.block q).refs))

/-- Two blocks of the same slot: one leader, one round, not equal. -/
def Conflicting (D : Dag Validator BlockId Payload) (l l' : BlockId) : Prop :=
  l ≠ l' ∧ (D.block l).round = (D.block l').round ∧
    (D.block l).creator = (D.block l').creator

instance (D : Dag Validator BlockId Payload) (l l' : BlockId) :
    Decidable (Conflicting D l l') := inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **Exposing equivocation, the parent-set reading.** Two parents of `b`
vote for two different blocks of the round-`r` leader. This is the
reading the validity rule is stated in, and the one Lemma 4 needs. -/
def ExposesEquivocation (D : Dag Validator BlockId Payload) (b : BlockId) : Prop :=
  ∃ l ∈ (D.ids : Finset BlockId), ∃ l' ∈ (D.ids : Finset BlockId),
    Conflicting D l l' ∧ (parentsVoting D b l).Nonempty ∧ (parentsVoting D b l').Nonempty

/-- **Exposing equivocation, the causal-history reading**, the paper's
"i.e." gloss: the two conflicting blocks are anywhere below `b`, not
necessarily voted for by its parents. Weaker, and not what the validity
rule constrains. -/
def ExposesEquivocationHistory (D : Dag Validator BlockId Payload) (b : BlockId) : Prop :=
  ∃ l ∈ (D.ids : Finset BlockId), ∃ l' ∈ (D.ids : Finset BlockId),
    Conflicting D l l' ∧ l ∈ historyFrom D.block b ∧ l' ∈ historyFrom D.block b

instance (D : Dag Validator BlockId Payload) (b : BlockId) :
    Decidable (ExposesEquivocation D b) :=
  inferInstanceAs (Decidable (∃ _ ∈ _, ∃ _ ∈ _, _))

/-- **FP-evidence**, the two branches of the paper's definition. A block
that has seen the equivocation must carry `f + p` parents voting for `l`
and fewer than `f + p` for anything conflicting; one that has not needs
only `f + p − 1` voting for `l`. -/
def FPEvidence (D : Dag Validator BlockId Payload) (b l : BlockId) : Prop :=
  if ExposesEquivocation D b then
    F.f + P.p ≤ (parentsVoting D b l).card ∧
      ∀ l' ∈ (D.ids : Finset BlockId), Conflicting D l l' →
        (parentsVoting D b l').card + 1 ≤ F.f + P.p
  else
    F.f + P.p ≤ (parentsVoting D b l).card + 1

/-- **An SP-certificate**, Mysticeti's, at this committee's quorum. -/
def SPCertificate (D : Dag Validator BlockId Payload) (b l : BlockId) : Prop :=
  spQuorum Validator ≤ (parentsVoting D b l).card

/-- **The fast direct commit**: `n − p` distinct validators vote for `l`
one round up. -/
def FastCommit (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  fastCard Validator ≤ (voters D l).card

/-- The parent-set reading implies the causal-history one, since a
parent voting for a block puts it in the history. The converse fails, and
`LeanDagTest/FinWhale/Reading` exhibits a block that separates them. -/
theorem exposes_history_of_parents_of_mem
    (h : ExposesEquivocation D b)
    (hmem : ∀ l : BlockId, (parentsVoting D b l).Nonempty → l ∈ historyFrom D.block b) :
    ExposesEquivocationHistory D b := by
  obtain ⟨l, hl, l', hl', hconf, hv, hv'⟩ := h
  exact ⟨l, hl, l', hl', hconf, hmem l hv, hmem l' hv'⟩

end FinWhale

end LeanDag
