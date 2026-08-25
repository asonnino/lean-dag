import LeanDag.BlackMarlin.Agreement.Statement

/-!
# Black Marlin — liveness at a validator's view, stated

BML1–BML5 and BMR1–BMR6 conclude `Committed U L r`: the **universe**
admits a commit at that round. That is not what liveness asserts. A
validator delivers from its own view, and the universe is a device of
this model rather than an object anyone holds, so a liveness result has
to be read at a view or it is about the wrong thing
(`black-marlin.md` §15). Three claims:

* **BMV1, `NoValidatorStuck`** — above every round the rotation names a
  later one that **every reliable validator commits on its own view**,
  by an explicit time, in any sufficiently grown DAG under any pace.
  This is BML4 and BMP12 read where liveness lives;
* **BMV2, `NothingHeldBack`** — and what any view committed below is in
  what every reliable validator delivers there. BMA3 with its round
  hypothesis discharged;
* **BMV3, `ReadableAtReliableAnchor`** — at a reliably anchored round
  past coverage, a validator holding the reliable blocks of the round
  above can evaluate the support clause. No waiting is required, which
  is why BMV1 has a time in it.

## Where liveness holds, and where it stops

**It holds for the commit rule.** BMV3 is the reason: the rule's input
at a reliably anchored round is reliable blocks, and coverage delivers
those. BMV1 and BMV2 then follow with explicit times, so the protocol as
the paper states it is live at the view for the delivered **set**.

**It stops at the delivered order.** The descent reads `Supported` at
whichever anchor its chain lands on, and nothing constrains that
anchor's author. Where it is Byzantine, BMV3 has no counterpart and none
is available: coverage says nothing about a Byzantine validator's
blocks, and a committed anchor's quorum of `2f + 1` supporters need
contain only `f + 1` reliable ones. `LeanDagTest/BlackMarlin/Counting`
exhibits a view holding **every** reliable block, and everything those
reference, in which neither of an equivocator's twins is supported.

**So the repair of §14 has no live implementation.** A validator running
`descendS` either decides from what it holds, which can be too little
and selects the wrong block — safety fails — or waits for the quorum,
which the equivocator need never complete — liveness fails. The two
horns are `black-marlin.md` §14, and BMV3 is the line between them: on
its side the rule is readable, and past it the descent is not.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace ViewLiveness

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **What it means for a round to be committed by every reliable
validator on its own view.** Universe, growth and pace are quantified
inside, as `Liveness.CommitsAtRound` quantifies the universe and for the
same reason: the rotation names the round before any DAG is fixed, and
fixing one first would cap how far the rotation may reach. -/
def CommitsInViews (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    (T : Finset Validator) (R r : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ) (pc : Pace U T N),
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    pc.gst ≤ R → (∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n) →
    r + 2 ≤ N →
    ∃ L, IsAnchor U r L ∧ Committed U L r ∧
      ∀ v ∈ T, CommittedIn U
        (pc.toPaceCore.viewAt v (max (pc.latest (r + 1)) (pc.latest (r + 2)) + pc.delay))
        L r

variable (Validator BlockId Payload) in
/-- **BMV1, no reliable validator is stuck.** BML4 says a round recurs
that the universe admits a commit at; this says a round recurs that
every reliable validator commits at, on its own view and by a time the
pace names. -/
def NoValidatorStuck : Prop :=
  ∀ (T : Finset Validator) (R r : ℕ),
    quorumCard Validator ≤ T.card → Liveness.FairRun T 2 →
    ∃ r', r ≤ r' ∧ R ≤ r' ∧ CommitsInViews BlockId Payload T R r'

/-- **What it means for a round to deliver, at every reliable view, what
some view committed below.** -/
def DeliversInViews (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    (T : Finset Validator) (R ρ r : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ) (pc : Pace U T N)
    (V : View Validator BlockId Payload U) (A B : BlockId),
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    pc.gst ≤ R → (∀ n, R ≤ n → 2 * pc.delay + pc.proc ≤ pc.timeout n) →
    r + 2 ≤ N →
    CommittedIn U V A ρ → B ∈ history U A →
    ∃ L, IsAnchor U r L ∧ B ∈ history U L ∧
      ∀ v ∈ T, CommittedIn U
        (pc.toPaceCore.viewAt v (max (pc.latest (r + 1)) (pc.latest (r + 2)) + pc.delay))
        L r

variable (Validator BlockId Payload) in
/-- **BMV2, nothing one validator delivered is held back from another.**
BMA3 asks for a reliably anchored round above `ρ`; the rotation supplies
one, so the hypothesis becomes a conclusion. -/
def NothingHeldBack : Prop :=
  ∀ (T : Finset Validator) (R ρ : ℕ),
    quorumCard Validator ≤ T.card → Liveness.FairRun T 2 →
    ∃ r, ρ ≤ r ∧ R ≤ r ∧ DeliversInViews BlockId Payload T R ρ r

/-- **BMV3, the rule is readable at a reliable anchor.** Past the round
coverage takes hold, an anchor whose author is reliable is referenced by
every reliable block of the round above, so a view holding those sees
the quorum — the support clause needs no block a Byzantine validator
might withhold.

This is the boundary of the arc. Replace `Rot.anchor ρ ∈ T` by nothing
and the statement is false: coverage constrains only `T`-authored
blocks, and a committed anchor's `2f + 1` supporters need contain only
`f + 1` reliable ones. That is the case the descent meets and the repair
needs, and `black-marlin.md` §14 records what it costs. -/
def ReadableAtReliableAnchor (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (R ρ : ℕ) (V : View Validator BlockId Payload U) (L : BlockId),
    quorumCard Validator ≤ T.card →
    SynchronisedOn U T R → R ≤ ρ → PopulatedOn U T (ρ + 1) →
    Rot.anchor ρ ∈ T → IsAnchor U ρ L →
    (∀ b ∈ U.ids, (U.block b).creator ∈ T → (U.block b).round = ρ + 1 → b ∈ V.ids) →
    SupportedIn U V L ρ

/-- Liveness of the Black Marlin commit rule read at a validator's view,
over every fault configuration, rotation and block universe the model
admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Rotation Validator],
    NoValidatorStuck Validator BlockId Payload ∧
      NothingHeldBack Validator BlockId Payload ∧
      ∀ (U : BlockUniverse Validator BlockId Payload), ReadableAtReliableAnchor U

end ViewLiveness

end BlackMarlin

end LeanDag
