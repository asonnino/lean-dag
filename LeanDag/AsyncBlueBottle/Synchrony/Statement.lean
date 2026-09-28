import LeanDag.AsyncBlueBottle.Model.Unpredictable
import LeanDag.Mysticeti.Quantitative
/-!
# Partial synchrony, recovered — statement

Two claims keeping the arc usable under partial synchrony
(`async-bluebottle.md` §6): ABB10a derives a committed candidate from
`SynchronisedOn` at one round, and ABB10b derives the
unpredictable-leader clause itself from the core's `FairWithin` under
synchrony and population through the horizon. Mahi-Mahi's MM5 at the
three-round wave.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace AsyncBlueBottle

namespace Synchrony

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **ABB10a, a reliable leader is good under coverage at one round.** -/
def GoodOfSynchrony (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (R k : ℕ),
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the core's coverage hypothesis, in force at the slot's round
    SynchronisedOn U T R → R ≤ S.slotRound k →
    -- T populates the proposal round, the round above it, and the decision round
    PopulatedOn U T (S.slotRound k) → PopulatedOn U T (S.slotRound k + 1) →
    PopulatedOn U T ((asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k) →
    -- the slot's leader is reliable
    S.leader k ∈ T →
    -- then the leader is a committed candidate of its round
    S.leader k ∈ good U k

/-- **ABB10b, the clause is derived under synchrony.** -/
def ClauseOfSynchrony (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (c N : ℕ),
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- coverage from round 0 and population through the horizon
    SynchronisedOn U T 0 → (∀ n, n ≤ N → PopulatedOn U T n) →
    -- the core's rated fairness: a T-leader in every window of c slots
    FairWithin T c →
    -- then the single-hit clause holds with the same window
    UnpredictableWithin U c N

/-- Partial synchrony recovered, over every fault configuration, schedule
and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload),
    GoodOfSynchrony U ∧ ClauseOfSynchrony U

end Synchrony

end AsyncBlueBottle

end LeanDag
