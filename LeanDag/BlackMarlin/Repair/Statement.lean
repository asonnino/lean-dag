import LeanDag.BlackMarlin.Model.Repair

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
  alone, so BML1 and BMR2 hold of the repaired protocol word for word.

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

/-- The repaired descent, over every fault configuration, rotation and
block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    AtMostOneSupported U ∧ RepairPrefers U ∧ RepairRefines U ∧ NoStall U ∧
      Agrees U ∧ LivenessUntouched U

end Repair

end BlackMarlin

end LeanDag
