import LeanDag.Steelhead.Model.Replay
import LeanDag.Steelhead.Model.Coin
import LeanDag.AsyncBlueBottle.Model.Good
/-!
# The `5f + 1` pair's replay — statement

How BlueBottle's pair's window reads the DAG: `BlueBottlePair.Replay.ofAnchor`
takes the anchor's causal history at the rounds the window retains and
marks a candidate committed, skipped or certified by the pair's support
within it, the decision-round votes themselves, Odontoceti's references
one round up at wave two and Async BlueBottle's cone votes two rounds up
otherwise, with `n − 3f` supporters the indirect threshold. This is the
paper's Algorithm 3 read through the support of its Lemmas 1 and 2, and
the implementation's `merged_certificates`. The selection and the
timings, which read only the evidence, are SH18 in
`Replay/Statement.lean`; this file holds what the window's reading gives.
Six claims:

* **SH-BB18c, the evidence is consistent** — in the window's evidence a
  committed candidate is certified, and a skipped one is not, at either
  wave: a quorum of supporters is at least `n − 3f` of them, and a
  skipped slot's candidate keeps at most `2f` supporters, the counting
  half of O2 and ABB2 restricted to the window;
* **SH-BB18d, the window's committed candidates** — Lemma 3's count at
  the pair: at a round of the window whose two rounds above a correct
  quorum has populated *within the window*, at least `n − 3f` authors are
  marked committed at wave three, the counting lemma ABB7 read on the
  anchor's causal history as a record of its own;
* **SH-BB18g, a window commit is a commit on the DAG** — a candidate the
  window marks committed is directly committed on the DAG by the wave's
  rule, so a probe's success is a support quorum the DAG holds: the
  adversary can suppress the probes' evidence of the synchronous rule,
  never manufacture it;
* **SH-BB18h, Algorithm 3 keeps the range** — SH18h on the pair's window:
  with candidates in `[1, K]`, the replay's selection answers a period in
  `[1, K]` at every anchor;
* **SH-BB18i, the replay's commit weight is the rule's commit
  probability** — at a round of the window, the share of the `n`
  candidates the window marks committed at wave three is the probability
  that a uniform coin names a directly committed leader on the anchor's
  causal history read as a record of its own, the paper's `c_r / n` at
  Async BlueBottle;
* **SH-BB18n, every candidate divides the period bound** — SH18n on the
  pair's window, at a power-of-two bound.

SH-BB18d asks the quorum's blocks to lie in the window, as SH-MM18d does,
and asks the quorum correct, as ABB7 does. SH-BB18i needs no wave
hypothesis: Async BlueBottle's decision round lies two rounds above the
candidate whatever the wave, so the supporters of a round the window
retains lie in the window.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Replay

open Steelhead.Replay (Config committedCount candidatesUpto)
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **SH-BB18c, the evidence is consistent.** -/
def EvidenceConsistent (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (A : BlockId) (I r w : ℕ) (a : Validator),
    -- a committed candidate is certified ...
    ((ofAnchor U A I).commits r w a = true → (ofAnchor U A I).certified r w a = true) ∧
      -- ... and a skipped one is not
      ((ofAnchor U A I).skips r w a = true → (ofAnchor U A I).certified r w a = false)

/-- **SH-BB18d, the window's committed candidates.** -/
def WindowCount (U : BlockUniverse Validator BlockId Payload) (I : ℕ) : Prop :=
  ∀ (A : BlockId) (hA : A ∈ U.ids) (T : Finset Validator) (r : ℕ),
    -- T is a correct quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the round lies in the window
    windowBottom U A I ≤ r →
    -- T's blocks at the two rounds above lie in the anchor's history
    PopulatedOn (U.historyView A hA).toRecord T (r + 1) →
    PopulatedOn (U.historyView A hA).toRecord T (r + 2) →
    -- then at least n − 3f authors are marked committed at the round and wave three
    Fintype.card Validator - 3 * F.f ≤ committedCount (ofAnchor U A I) r 3

/-- **SH-BB18g, a window commit is a commit on the DAG.** -/
def CommitsSound (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (A : BlockId) (I r w : ℕ) (a : Validator),
    (ofAnchor U A I).commits r w a = true →
    ∃ L ∈ blocksAt U r, (U.block L).creator = a ∧
      -- by Odontoceti at wave two, by Async BlueBottle at any other wave
      (w = 2 → Odontoceti.DirectCommit U L r) ∧ (w ≠ 2 → AsyncBlueBottle.DirectCommit U L r)

/-- **SH-BB18h, Algorithm 3 keeps the range.** -/
def UpdateInRange (U : BlockUniverse Validator BlockId Payload) (I : ℕ) : Prop :=
  ∀ (C : Config Validator) (candidates : List ℕ) (epsilon : ℚ) (K k : ℕ) (A : BlockId),
    -- the candidates lie in [1, K], as does the current period
    (∀ c ∈ candidates, 1 ≤ c ∧ c ≤ K) → 1 ≤ k → k ≤ K →
    -- then so does the selection's answer at any anchor
    1 ≤ anchorUpdate U I C candidates epsilon A k ∧ anchorUpdate U I C candidates epsilon A k ≤ K

/-- **SH-BB18i, the replay's commit weight is the rule's commit probability.** -/
def CommitWeightExact (U : BlockUniverse Validator BlockId Payload) (I : ℕ) : Prop :=
  ∀ (A : BlockId) (hA : A ∈ U.ids) (r : ℕ),
    -- the round lies in the window
    windowBottom U A I ≤ r →
    -- then the share of the candidates the window marks committed at wave three is the
    -- probability that the coin names a committed leader on the anchor's history read as a record
    (committedCount (ofAnchor U A I) r 3 : ℝ≥0∞) / Fintype.card Validator =
      commitProb (AsyncBlueBottle.goodAt (U.historyView A hA).toRecord) r

/-- **SH-BB18n, every candidate divides the period bound.** -/
def CandidatesDvd (U : BlockUniverse Validator BlockId Payload) (I : ℕ) : Prop :=
  ∀ (C : Config Validator) (epsilon : ℚ) (e K k : ℕ) (A : BlockId),
    -- the period bound is a power of two
    K = 2 ^ e →
    -- then every candidate divides it ...
    (∀ c ∈ candidatesUpto K, c ∣ K) ∧
    -- ... and Algorithm 3 answers a divisor of it from a divisor of it, at any anchor
    (k ∣ K → anchorUpdate U I C (candidatesUpto K) epsilon A k ∣ K)

/-- The `5f + 1` pair's replay, over every fault configuration, block universe and interval the
model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] (U : BlockUniverse Validator BlockId Payload)
    (I : ℕ),
    EvidenceConsistent U ∧ WindowCount U I ∧ CommitsSound U ∧ UpdateInRange U I ∧
      CommitWeightExact U I ∧ CandidatesDvd U I

end Replay

end BlueBottlePair

end Steelhead

end LeanDag
