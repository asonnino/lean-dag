import LeanDag.AsyncBlueBottle.Model.Unpredictable
import LeanDag.Mysticeti.ViewPace
/-!
# Liveness under the clause — statement

What the rule decides with no network hypothesis, under the
unpredictable-leader clause (`async-bluebottle.md` §6): ABB9a–ABB9d give
a good leader's commit, windowed and run-length liveness, and a local
commit from eventual delivery alone, each concluding on a view a
validator can hold; ABB9e says `good` depends only on blocks up to the
decision round. ABB9d needs every reliable decision-round block to vote
for the candidate, which the counting lemma supplies for the common-core
candidates.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace AsyncBlueBottle

namespace Liveness

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **ABB9a, a good leader commits** on any view caught up to the
decision round. -/
def GoodCommits (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (k : ℕ) (V : View Validator BlockId Payload U),
    -- the slot's leader is a committed candidate of its round
    S.leader k ∈ good U k →
    -- the view holds every block up to the decision round
    V.CoversUpto ((asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k) →
    -- then its block is a candidate, decided as committed on that view
    ∃ L, IsLeaderBlock U k L ∧ Decided U V k (some L)

/-- **ABB9b, commits within every window.** -/
def CommitsWithin (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (c N : ℕ) (V : View Validator BlockId Payload U),
    -- the single-hit clause, with window c below horizon N
    UnpredictableWithin U c N →
    -- on a view caught up to the horizon
    V.CoversUpto N →
    -- for every window below the horizon ...
    ∀ k, (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound (k + c) ≤ N →
      -- ... some slot of it commits
      ∃ k', k ≤ k' ∧ k' < k + c ∧
        ∃ L, IsLeaderBlock U k' L ∧ Decided U V k' (some L)

/-- **ABB9c, every slot below a run is decided.** -/
def AllDecidedBelow (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (c d N : ℕ) (V : View Validator BlockId Payload U),
    -- a run of d slots spans eligibility
    (asyncBlueBottleAnchored Validator BlockId Payload).SpansEligible d →
    -- the run form of the clause
    UnpredictableRunWithin U c d N →
    -- on a view caught up to the horizon
    V.CoversUpto N →
    -- for every window below the horizon ...
    ∀ k, (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound (k + c + d - 1) ≤ N →
      -- ... there is a slot b at or past k below which every slot is decided
      ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, Decided U V i v

/-- **ABB9d, local liveness.** -/
def LocalCommit (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (N : ℕ) (pc : PaceCore U T N),
    -- T is a quorum (its correctness is the pacing structure's own)
    quorumCard Validator ≤ T.card →
    ∀ (k : ℕ) (L : BlockId),
      -- L is slot k's candidate, and its decision round is within the horizon
      IsLeaderBlock U k L →
      (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k ≤ N →
      -- every reliable decision-round block votes for L
      (∀ u ∈ T, ∀ q ∈ U.ids, (U.block q).creator = u →
        (U.block q).round = (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k →
        MahiMahi.Votes U q L) →
      -- then every reliable validator commits L on its own view, by the time
      -- the decision round's reliable blocks have converged
      ∀ v ∈ T, Decided U
        (pc.viewAt v
          (max (pc.latest ((asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k))
            pc.gst + pc.delay))
        k (some L)

/-- **ABB9e, measurability of `good`.** -/
def GoodMeasurable : Prop :=
  ∀ (U₁ U₂ : BlockUniverse Validator BlockId Payload) (r : ℕ),
    -- the two universes agree up to the decision round ...
    MahiMahi.AgreeUpto U₁ U₂ (r + 2) →
    -- ... so they commit the same candidates there
    goodAt U₁ r = goodAt U₂ r

/-- Liveness under the clause, over every fault configuration, schedule
and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload),
    GoodCommits U ∧ CommitsWithin U ∧ AllDecidedBelow U ∧ LocalCommit U ∧
      GoodMeasurable (Validator := Validator) (BlockId := BlockId) (Payload := Payload)

end Liveness

end AsyncBlueBottle

end LeanDag
