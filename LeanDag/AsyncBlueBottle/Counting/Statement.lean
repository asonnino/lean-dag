import LeanDag.AsyncBlueBottle.Model.Good
/-!
# The counting lemma — statement

What a wave commits with no network hypothesis (`async-bluebottle.md`
§5): `CommonCore` (a correct round-`r` block reached by every block two
rounds up), `GoodNonempty` (some correct validator's block is directly
committed), `GoodCard` (at least `n − 3f` of them — the paper's Lemmas
27–30 give `2f + 1` at `n = 5f+1`, and the same count yields the
relative bound at every `n ≥ 5f+1`), and `MultiLeader` (with `3f + 1`
distinct leaders at a round, one is committed, for every schedule — the
paper's Lemma 31 at `l > 3f`). The bounds count distinct correct
authors, so an equivocating author's twins, which can split the voters,
are never counted.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace AsyncBlueBottle

namespace Counting

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
  [S : Slots Validator]

/-- **The common core.** If some block exists at round `r + 2`, a correct
validator's round-`r` block lies in the causal history of every block at
every round `≥ r + 2`. The core's T3c (`CommonCore.lean`) at round `r + 2`,
carried upward through references. -/
def CommonCore (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (r : ℕ) (c₀ : BlockId),
    -- some block exists two rounds above r (its own quorum of references
    -- is what makes the round-(r+1) author pool large enough to count)
    c₀ ∈ U.ids → (U.block c₀).round = r + 2 →
    -- then there is a round-r block b ...
    ∃ b ∈ U.ids, (U.block b).round = r ∧
      -- ... by a correct validator ...
      (U.block b).creator ∈ (Correct : Finset Validator) ∧
      -- ... in the causal history of EVERY block at round ≥ r + 2
      ∀ c ∈ U.ids, r + 2 ≤ (U.block c).round → Reaches U c b

/-- **ABB6, some correct candidate commits.** Some correct validator's
round-`r` block is directly committed: the common core of round `r` is
reached by every decision-round block, so every reliable decision-round
block votes for it, and the reliable ones are a quorum. One populated
round, and no use of the `5f + 1` committee. -/
def GoodNonempty (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- every member of T has a block at the decision round r + 2 (so the
    -- common core exists, and the votes form a quorum)
    PopulatedOn U T (r + 2) →
    -- then some correct validator's round-r block is directly committed
    (goodAt U r ∩ (Correct : Finset Validator)).Nonempty

/-- **ABB7, at least `n − 3f` correct candidates commit** (the paper's
Lemmas 27–30, which state `2f + 1` at `n = 5f+1`). Double counting the
references from the reliable round-`(r + 1)` blocks to the correct
round-`r` blocks: each names at least `n − f − |byzantine|` correct
authors, so at least `n − 3f` correct round-`r` blocks are referenced by
`f + 1` reliable blocks each, and such a block is reached by every
round-`(r + 2)` block, which omits at most `f` authors. Stated
additively, as every threshold of the tree is. -/
def GoodCard (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- every member of T has a block at round r + 1 (the referencing layer) ...
    PopulatedOn U T (r + 1) →
    -- ... and at the decision round r + 2
    PopulatedOn U T (r + 2) →
    -- then at least n − 3f correct validators' round-r blocks are directly committed
    Fintype.card Validator ≤ (goodAt U r ∩ (Correct : Finset Validator)).card + 3 * F.f

/-- **ABB8, deterministic commits under multiple leaders.** If `3f + 1`
distinct validators lead slots at round `r`, one is good, for every
schedule: `n − 3f` good correct validators and `3f + 1` leaders cannot
be disjoint in `n`. The paper's Lemma 31 at `l > 3f`, at every
`n ≥ 5f + 1`. -/
def MultiLeader (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- the hypotheses of GoodCard, verbatim
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    PopulatedOn U T (r + 1) → PopulatedOn U T (r + 2) →
    -- M is a set of validators each of which leads some slot at round r ...
    ∀ M : Finset Validator, (∀ v ∈ M, ∃ k, S.slotRound k = r ∧ S.leader k = v) →
      -- ... with at least 3f + 1 members (distinct, being a Finset)
      3 * F.f + 1 ≤ M.card →
      -- then one of those slots is led by a good validator
      ∃ k, S.slotRound k = r ∧ S.leader k ∈ good U k

/-- The counting lemma, over every fault configuration, schedule and
block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload),
    CommonCore U ∧ GoodNonempty U ∧ GoodCard U ∧ MultiLeader U

end Counting

end AsyncBlueBottle

end LeanDag
