import LeanDag.BlackMarlin.Model.Repair
import LeanDag.BlackMarlin.Liveness.Statement

/-!
# Black Marlin — the repair, stated

The execution of `black-marlin.md` §13 turns on `commit`'s descent
taking an unsupported twin where the rule had committed the supported
one. This phase asks what a side-condition on the descent buys, and what
it costs (`black-marlin.md` §14). Nothing in the model is altered: `descend`,
`flushRecord` and everything proved of them stand, and what is added
sits beside them. Six claims:

* **BMP1, `AtMostOneSupported`** — at most one candidate of a step is
  supported. The candidates of a step share a round and an anchor round
  has one supported anchor (BM1), so where the filter bites there is
  nothing left to break ties over;
* **BMP2, `RepairPrefers`** — `descendSupp` takes a supported candidate
  wherever there is one;
* **BMP3, `RepairRefines`** — and is L21–L24 verbatim where there is
  not, so it refines the rule rather than replacing it;
* **BMP4, `NoStall`** — the repaired step returns a block exactly when
  the unrepaired one does, and always at the same round. A *record* may
  still flush at different rounds, since a chain that passes through a
  different block passes through a different cone; what cannot happen is
  a step that stalls;
* **BMP5, `Agrees`** — two support-preferring records cannot part at a
  round that has a supported anchor. This is what the execution of
  `black-marlin.md` §13 needed and did not have;
* **BMP6, `LivenessUntouched`** — nothing the liveness results speak
  about mentions the descent: `Committed` is a property of the rule
  alone, so BML1 and BMR2 hold of the repaired protocol word for word;
* **BMP7–BMP10** are the strengthened form, which drops the tie-break
  rather than filtering it: every boundary is supported, no committed
  anchor is passed by, agreement runs down from any meeting point, and
  the descent still terminates and delivers everything.

**What this does not settle.** `Supported` is a fact about the universe,
and a validator computes support from its own view, which under-reports.
So a record built by a real validator meets `SupportPreferring` only if
the support it needs is in view when it descends — which holds in the
execution of `black-marlin.md` §13, where the second validator has the
whole round-4 layer by the time it commits, but is not established in
general. The repair is therefore stated, not supplied, and
`black-marlin.md` §14 records what supplying it would take.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Repair

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **BMP1, at most one candidate of a step is supported.** -/
def AtMostOneSupported (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B A C : BlockId), A ∈ suppCandidates U B → C ∈ suppCandidates U B → A = C

/-- **BMP2, the repair takes the supported candidate.** -/
def RepairPrefers (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B L : BlockId), descendSupp U B = some L → (suppCandidates U B).Nonempty →
    Supported U L (U.block L).round

/-- **BMP3, and is the original rule where there is none.** -/
def RepairRefines (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B : BlockId), ¬ (suppCandidates U B).Nonempty → descendSupp U B = descend U B

/-- **BMP4, the repair changes which block a step returns, never whether
it returns one nor at which round.** Stated of a step, not of a record:
a chain through a different block descends through a different cone, so
the rounds a record flushes at may differ downstream. -/
def NoStall (U : BlockUniverse Validator BlockId Payload) : Prop :=
  (∀ (B : BlockId), (descendSupp U B).isSome ↔ (descend U B).isSome) ∧
  (∀ (B L L' : BlockId), descendSupp U B = some L → descend U B = some L' →
    (U.block L).round = (U.block L').round)

/-- **BMP5, support-preferring records cannot part at a supported
round.** The whole content of the repair, and what the execution of
`black-marlin.md` §13 needed. -/
def Agrees (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (ρ : ℕ),
    SupportPreferring U f₁ → SupportPreferring U f₂ →
    (f₁.block ρ).isSome → (f₂.block ρ).isSome →
    (∃ A, IsAnchor U ρ A ∧ Supported U A ρ) →
    f₁.block ρ = f₂.block ρ

/-- **BMP6, liveness is untouched.** What the liveness results conclude
is `Committed`, which is a property of the commit rule and mentions no
part of the descent — so the repair leaves them
untouched, and the statement is the identity it looks like. -/
def LivenessUntouched (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L : BlockId) (ρ : ℕ),
    Committed U L ρ ↔ (IsAnchor U ρ L ∧ Supported U L ρ ∧ Linked U L ρ)

/-! ## The strengthened repair

`descendSupp` chooses among the candidates L21–L24 already offers, so it
helps only where the supported anchor is among them — and a step through
a block that cites a twin instead offers none. `descendS` drops the
tie-break: it descends to the highest-round **supported** anchor of the
cone and nowhere else. Four further claims. -/

/-- **BMP7, every boundary is supported.** So a round whose anchors carry
no quorum is not a boundary at all: where an anchor equivocates and
neither twin is supported, the strengthened descent makes no choice
there, and two records cannot part over one. -/
def StrongSupported (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B L : BlockId), descendS U B = some L → Supported U L (U.block L).round

/-- **BMP8, and no committed anchor is passed by.** A supported anchor
sits at every round the chain could land on above a committed one — the
committed anchor itself from two rounds up, and its linking anchor from
one, which the commit rule makes supported — and anchor uniqueness fixes
which block each of those is. -/
def StrongReaches (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B L : BlockId) (ρ : ℕ), B ∈ U.ids → Committed U L ρ → L ∈ strongOf U B →
    flushRecordS U B ρ = some L

/-- **BMP9, and agreement runs down from any meeting point.** With BMP8
this is what the refutation needed: two records whose tops are committed
anchors both reach the lower of the two — BM5 puts it in the higher's
cone — and so agree at every round below it. -/
def StrongAgrees (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B₁ B₂ M : BlockId) (σ ρ : ℕ), B₁ ∈ U.ids → B₂ ∈ U.ids →
    flushRecordS U B₁ σ = some M → flushRecordS U B₂ σ = some M → ρ ≤ σ →
    flushRecordS U B₁ ρ = flushRecordS U B₂ ρ

/-- **BMP10, and it does not stall.** A choice is made whenever the cone
holds a supported anchor, and it sits strictly lower, so the descent
terminates. Coarser segments deliver the same blocks: a round that is no
longer a boundary has its blocks come out inside the next segment
above. -/
def StrongNoStall (U : BlockUniverse Validator BlockId Payload) : Prop :=
  (∀ (B : BlockId), (suppAnchorsOf U (strongOf U B)).Nonempty → (descendS U B).isSome) ∧
  (∀ (B L : BlockId), B ∈ U.ids → descendS U B = some L →
    (U.block L).round < (U.block B).round)

variable (Validator BlockId Payload) in
/-- **BMP11, and no execution is stuck.** The recurrence of committed
rounds is a statement about `Committed` and the rotation, neither of
which the repair touches, so it holds of the repaired protocol word for
word: for every round the rotation names a later one that any
sufficiently grown covered DAG commits, and BML5 supplies the clause it
needs at every committee. -/
def NotStuck : Prop :=
  ∀ (T : Finset Validator) (R r : ℕ),
    quorumCard Validator ≤ T.card → Liveness.FairRun T 2 →
    ∃ r', r ≤ r' ∧ R ≤ r' ∧ Liveness.CommitsAtRound BlockId Payload T R r'

/-- The repaired descent, over every fault configuration, rotation and
block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    AtMostOneSupported U ∧ RepairPrefers U ∧ RepairRefines U ∧ NoStall U ∧
      Agrees U ∧ LivenessUntouched U ∧
      StrongSupported U ∧ StrongReaches U ∧ StrongAgrees U ∧ StrongNoStall U ∧
      NotStuck Validator BlockId Payload

end Repair

end BlackMarlin

end LeanDag
