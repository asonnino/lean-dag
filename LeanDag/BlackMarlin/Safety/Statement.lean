import LeanDag.BlackMarlin.Model.Decision
import LeanDag.Schedule

/-!
# Black Marlin — safety of the commit rule, stated

The commit rule of `delivery(r)` never admits two anchors that disagree,
whatever DAG the validators hold. Seven claims (`black-marlin.md` §4),
following §5.1 of the paper:

* **BM1, anchor uniqueness** — the paper's Lemma 2: at most one anchor
  block of a round is supported, so at most one is committed there;
* **BM2, propagation** — the paper's Lemma 4: a supported block lies in
  the causal history of every block two rounds above it or higher;
* **BM3, density** — the paper's Lemma 3: below the highest round of the
  DAG, every round carries a quorum of distinct authors;
* **BM4, soundness of the view reading** — what a validator commits by
  reading its own DAG, the rule commits over the universe, and the
  validator holds the block it committed;
* **BM5, chaining** — the paper's Lemma 5: any two committed anchors,
  from any two views, are the same block or one lies in the causal
  history of the other;
* **BM6, prefix** — the causal history of the lower of two committed
  anchors is contained in that of the higher. This is what the paper
  means by the committed anchors defining one partial order across
  honest parties: `commit(B)` delivers exactly the undelivered blocks of
  `past(B)`, so nesting histories are nesting delivered prefixes, and
  the deterministic sort orders each increment;
* **BM7, the anchors are the core's candidates** — under the pipelined
  round-robin schedule an anchor block of round `r` is a leader block of
  slot `r`. A statement about definitions, which is how the arc's
  round-indexed rotation and the core's slot-indexed `Slots` are
  reconciled.

BM1, BM2 and BM3 are stated on the universe, where the counting happens;
BM4, BM5 and BM6 on views, where the protocol runs. None of them assumes
synchrony, a global stabilisation time, or any bound beyond
`n ≥ 3f + 1` — as in the paper, the safety results hold during the
asynchronous period as well.

Two readings differ from the paper's text and are recorded here rather
than in a proof. First, `Reaches` is reflexive where the paper's `past`
and `strong` exclude their own argument, which is why BM5 states
equality as a separate disjunct. Second, the causal history followed
throughout is the strong one: weak references are not modelled, so BM2
and BM5 conclude something stronger than the paper's `past`, and BM6 is
a statement about the strongly reachable prefix.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Safety

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [R : Rotation Validator]
  {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **BM1, anchor uniqueness** (the paper's Lemma 2): two supported anchor
blocks of one round are the same block. Their support quorums share
`n − 2f ≥ f + 1` authors, each supporting both, and a validator
supporting two blocks of one author and round is an equivocator — one
more than the fault bound admits. -/
def AnchorUniqueness (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (r : ℕ) (L₁ L₂ : BlockId),
    IsAnchor U r L₁ → IsAnchor U r L₂ →
    Supported U L₁ r → Supported U L₂ r → L₁ = L₂

/-- **BM2, propagation** (the paper's Lemma 4): a block supported at round
`r` lies in the causal history of every block of the universe at round
`r + 2` or above, whoever authored it.

The support quorum holds `f + 1` correct authors, each with a single
round-`(r + 1)` block, and a round-`(r + 2)` block names `n − f` of the
at most `n` authors of that round; above `r + 2` the property is
inherited along references. -/
def Propagation (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L : BlockId) (r : ℕ) (c : BlockId),
    Supported U L r → c ∈ U.ids → r + 2 ≤ (U.block c).round → Reaches U c L

/-- **BM3, density** (the paper's Lemma 3): if the universe holds a block
above round `r`, then round `r` carries blocks from a quorum of distinct
authors. A consequence of validity alone, and the reason the rule never
inspects a round that could be sparse. -/
def Density (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (c : BlockId) (r : ℕ), c ∈ U.ids → r < (U.block c).round →
    quorumCard Validator ≤ (authorsAt U r).card

/-- **BM4, soundness of the view reading**: a validator's verdict is a
verdict of the universe, and the validator holds the block it committed.

The second conjunct is not a clause of `CommittedIn` but a consequence of
one: the linking anchor is in the view, a view is closed under
references, and the link is a reference. -/
def ViewSound (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ),
    CommittedIn U V L r → Committed U L r ∧ L ∈ V.ids

/-- **BM5, chaining** (the paper's Lemma 5): two committed anchors, read
from any two views, are the same block or one lies in the causal history
of the other.

The three cases of the rule are the three ranges of the round gap. At
equal rounds BM1 identifies the two blocks. At a gap of one, the lower
anchor's linking block and the higher anchor are both supported anchors
of the same round, so BM1 identifies *them*, and the link is a direct
reference. At a gap of two or more BM2 applies to the higher block
itself. The rule's second clause exists for the middle case alone: with
support but no link, two anchors one round apart need not be
comparable. -/
def Chained (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (L₁ L₂ : BlockId) (r₁ r₂ : ℕ),
    CommittedIn U V₁ L₁ r₁ → CommittedIn U V₂ L₂ r₂ →
    L₁ = L₂ ∨ Reaches U L₁ L₂ ∨ Reaches U L₂ L₁

/-- **BM6, prefix**: of two committed anchors, the causal history of the
one at the lower round is contained in that of the one at the higher.

`commit(B)` delivers the undelivered blocks of `past(B)` and then `B`,
so containment of histories is containment of delivered prefixes: two
validators' deliveries agree wherever both have delivered, and neither
can retract. The order within each increment is the deterministic sort
`τ`, which the rule does not constrain and this arc does not model. -/
def HistoryPrefix (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (L₁ L₂ : BlockId) (r₁ r₂ : ℕ),
    CommittedIn U V₁ L₁ r₁ → CommittedIn U V₂ L₂ r₂ → r₁ ≤ r₂ →
    history U L₁ ⊆ history U L₂

/-- **BM7, the anchors are the core's candidates**: under the pipelined
round-robin schedule — one slot per round, slot `r` led by the validator
the rotation elects for round `r` — an anchor block of round `r` is a
leader block of slot `r`, and conversely.

This is what connects a round-indexed arc to the slot-indexed vocabulary
of the rest of the development. It asserts nothing about any verdict:
whether an anchor is committed is the business of the clauses above. -/
def AnchorsAreLeaderBlocks (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (r : ℕ) (L : BlockId),
    IsAnchor U r L ↔
      IsLeaderBlock (S := Slots.uniformSingle 1 Nat.one_pos R.anchor) U r L

/-- Safety of the Black Marlin commit rule, over every fault
configuration, anchor rotation and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    AnchorUniqueness U ∧ Propagation U ∧ Density U ∧ ViewSound U ∧
      Chained U ∧ HistoryPrefix U ∧ AnchorsAreLeaderBlocks U

end Safety

end BlackMarlin

end LeanDag
