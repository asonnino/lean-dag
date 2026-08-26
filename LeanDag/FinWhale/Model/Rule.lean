import LeanDag.FinWhale.Counting
import LeanDag.Causality

/-!
# FinWhale — the fast path, as the paper defines it

The counting of `Counting.lean` is Lemma 4's arithmetic. This file is the
vocabulary the paper states Lemma 4 in: votes, leader-consistency, the
two branches of FP-evidence, and the direct decision rules. Only what the
fast path needs is modelled; the slow path is Mysticeti's and unchanged.

**Why the paper's gloss on "exposes equivocation" is exact.** The paper
writes that a block `b′` of round `r+2` exposes equivocation by `Lr` if
"its parent set is not leader-consistent, i.e., its causal history
contains multiple conflicting versions of `Lr`'s block". The two halves
are stated as if interchangeable, and at this depth they are, for a
reason worth naming: `b′`'s parents sit at round `r+1` and their
references at round `r`, so the round-`r` blocks in `b′`'s causal history
are exactly the blocks its parents vote for. Validity gives each parent
at most one edge per validator, so no single parent votes for two
versions. Two versions below `b′` therefore means two parents voting
differently, which is what a parent set failing to be leader-consistent
is.

The equivalence is what lets Lemma 4 use block validity the way it does.
Validity's leader clause is stated over the parent set — a round-`r`
block's parents are leader-consistent with respect to `Lr₋₂` or exclude
its block — and Lemma 4's equivocating branch reads the causal-history
side. `ExposesEquivocation` is the parent-set condition, the one the
validity rule constrains, and the one every count here is taken against.
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
  /-- **FinWhale's clause.** Either the parent set is leader-consistent
  with respect to the leader two rounds down — the parents vote for at
  most one of that leader's blocks — or that leader's block is not among
  the parents. Leader-consistency is a condition on what the parents
  *reference*, not on who authored them. -/
  leader_clause : 2 ≤ b.round →
    (∀ i ∈ b.refs, ∀ j ∈ b.refs, ∀ x ∈ (blk i).refs, ∀ y ∈ (blk j).refs,
      (blk x).creator = leader (b.round - 2) → (blk y).creator = leader (b.round - 2) → x = y)
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
    Conflicting D l l' ∧ (D.block l).creator = D.leader ((D.block b).round - 2) ∧
      (parentsVoting D b l).Nonempty ∧ (parentsVoting D b l').Nonempty

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

instance (D : Dag Validator BlockId Payload) (b l : BlockId) :
    Decidable (FPEvidence D b l) := by
  unfold FPEvidence; infer_instance

/-- **An SP-certificate**, Mysticeti's, at this committee's quorum. -/
def SPCertificate (D : Dag Validator BlockId Payload) (b l : BlockId) : Prop :=
  spQuorum Validator ≤ (parentsVoting D b l).card

instance (D : Dag Validator BlockId Payload) (b l : BlockId) :
    Decidable (SPCertificate D b l) := inferInstanceAs (Decidable (_ ≤ _))

/-- **The fast direct commit**: `n − p` distinct validators vote for `l`
one round up. -/
def FastCommit (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  fastCard Validator ≤ (voters D l).card

instance (D : Dag Validator BlockId Payload) (l : BlockId) :
    Decidable (FastCommit D l) := inferInstanceAs (Decidable (_ ≤ _))

end FinWhale

end LeanDag
