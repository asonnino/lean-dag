import LeanDag.Steelhead.Model.Replay
import LeanDag.Steelhead.Model.Coin
import LeanDag.MahiMahi.Model.Good
/-!
# The `3f + 1` pair's replay — statement

How the Mysticeti and Mahi-Mahi pair's window reads the DAG: `ofAnchor`
takes the anchor's causal history at the rounds the window retains and
marks a candidate committed, skipped or certified by Mahi-Mahi's
certificates and blames within it. The selection and the timings, which
read only the evidence, are SH18 in `Replay/Statement.lean`; this file
holds what the window's reading gives. Six claims:

* **SH-MM18c, the evidence is consistent** — in the window's evidence a
  committed candidate is certified, and a skipped one is not, at any
  wave of two rounds or more: the direct predicates the replay reads are
  Mahi-Mahi's, restricted to the window;
* **SH-MM18d, the window's committed candidates** — Lemma 3's count: at a
  round of the window whose boost round and decision round a quorum has
  populated *within the window*, at least `n − f − b` authors are marked
  committed at wave `wa`, the counting lemma MM2 read on the anchor's
  causal history as a record of its own;
* **SH-MM18g, a window commit is a commit on the DAG** — a candidate the
  window marks committed is directly committed on the DAG, so a probe's
  success is a certificate quorum the DAG holds: the adversary can
  suppress the probes' evidence of the synchronous rule, never
  manufacture it. What this does not give is a bound on the synchronous
  term itself: the replay extends the probes' rate to the unprobed
  synchronous slots, and a scheduler that serves the canary rounds'
  leaders alone raises that estimate above what those slots hold;
* **SH-MM18h, Algorithm 3 keeps the range** — with candidates in `[1, K]`,
  the replay's selection answers a period in `[1, K]` at every anchor,
  whether it keeps the current period or picks a candidate: the range
  hypothesis SH10g, SH14b, SH14c and SH15 place on the update rule,
  discharged for the paper's rule; the failover's `1` is the scan's own
  (SH10e) and lies in the range too;
* **SH-MM18i, the replay's commit weight is the rule's commit
  probability** — the adaptive section's "exact in expectation", in the
  part that is a theorem: at a round of the window, the share of the `n`
  candidates the window marks committed is the probability that a
  uniform coin names a directly committed leader on the anchor's causal
  history read as a record of its own, `c_r / n`. The anchor's term is
  the approximation the paper admits, and not claimed;
* **SH-MM18n, every candidate divides the period bound** — the protocol
  section's "every candidate divides maxPeriod", at a power-of-two bound
  as the implementation's `max_period` is: the candidates are the powers
  of two up to it, and Algorithm 3 answers a divisor of the bound from
  one, the current period or a candidate (SH18a), which is what SH10o
  asks of an update rule.

SH-MM18d asks the quorum's blocks to lie in the window, not merely in the
DAG: the counting lemma counts certificates among the blocks a record
holds, and the replay reads the anchor's causal history, which holds a
quorum's worth of blocks at every round but not necessarily one quorum's
at two rounds. Under synchrony from below the window every reliable block
lies in every reliable cone, and the hypothesis holds; under asynchrony
it is what the paper's "populated" must mean for the lemma to apply to
the window (§7). SH-MM18i asks `1 ≤ wa`, so that a round's decision round
lies at or above it: the certificates of a round the window retains then
lie in the window. SH-MM18n asks a power-of-two bound, without which the
largest candidate need not divide it.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

namespace Replay

open Steelhead.Replay (Config ofAnchor committedCount anchorUpdate candidatesUpto)
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **SH-MM18c, the evidence is consistent.** -/
def EvidenceConsistent (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (A : BlockId) (I r w : ℕ) (a : Validator),
    2 ≤ w →
    -- a committed candidate is certified ...
    ((ofAnchor U A I).commits r w a = true → (ofAnchor U A I).certified r w a = true) ∧
      -- ... and a skipped one is not
      ((ofAnchor U A I).skips r w a = true → (ofAnchor U A I).certified r w a = false)

/-- **SH-MM18d, the window's committed candidates.** -/
def WindowCount (U : BlockUniverse Validator BlockId Payload) (wa I : ℕ) : Prop :=
  ∀ (A : BlockId) (hA : A ∈ U.ids) (T : Finset Validator) (r : ℕ),
    5 ≤ wa → quorumCard Validator ≤ T.card →
    -- the round lies in the window
    windowBottom U A I ≤ r →
    -- T's blocks at the boost round and at the decision round lie in the anchor's history
    PopulatedOn (U.historyView A hA).toRecord T (r + 3) →
    PopulatedOn (U.historyView A hA).toRecord T (MahiMahi.decisionRoundAt wa r) →
    -- then at least n − f − b authors are marked committed at the round and wave
    Fintype.card Validator - F.f - F.byzantine.card ≤ committedCount (ofAnchor U A I) r wa

/-- **SH-MM18g, a window commit is a commit on the DAG.** -/
def CommitsSound (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (A : BlockId) (I r w : ℕ) (a : Validator),
    (ofAnchor U A I).commits r w a = true →
    ∃ L ∈ blocksAt U r, (U.block L).creator = a ∧ MahiMahi.DirectCommit U w L r

/-- **SH-MM18h, Algorithm 3 keeps the range.** -/
def UpdateInRange (U : BlockUniverse Validator BlockId Payload) (I : ℕ) : Prop :=
  ∀ (C : Config Validator) (candidates : List ℕ) (epsilon : ℚ) (K k : ℕ) (A : BlockId),
    -- the candidates lie in [1, K], as does the current period
    (∀ c ∈ candidates, 1 ≤ c ∧ c ≤ K) → 1 ≤ k → k ≤ K →
    -- then so does the selection's answer at any anchor
    1 ≤ anchorUpdate U I C candidates epsilon A k ∧ anchorUpdate U I C candidates epsilon A k ≤ K

/-- **SH-MM18i, the replay's commit weight is the rule's commit probability.** -/
def CommitWeightExact (U : BlockUniverse Validator BlockId Payload) (wa I : ℕ) : Prop :=
  ∀ (A : BlockId) (hA : A ∈ U.ids) (r : ℕ),
    -- a wave of at least one round, and the round lies in the window
    1 ≤ wa → windowBottom U A I ≤ r →
    -- then the share of the candidates the window marks committed is the probability that the
    -- coin names a committed leader on the anchor's history read as a record
    (committedCount (ofAnchor U A I) r wa : ℝ≥0∞) / Fintype.card Validator =
      commitProb (MahiMahi.goodAt (U.historyView A hA).toRecord wa) r

/-- **SH-MM18n, every candidate divides the period bound.** -/
def CandidatesDvd (U : BlockUniverse Validator BlockId Payload) (I : ℕ) : Prop :=
  ∀ (C : Config Validator) (epsilon : ℚ) (e K k : ℕ) (A : BlockId),
    -- the period bound is a power of two
    K = 2 ^ e →
    -- then every candidate divides it ...
    (∀ c ∈ candidatesUpto K, c ∣ K) ∧
    -- ... and Algorithm 3 answers a divisor of it from a divisor of it, at any anchor
    (k ∣ K → anchorUpdate U I C (candidatesUpto K) epsilon A k ∣ K)

/-- The `3f + 1` pair's replay, over every fault configuration, block universe, asynchronous wave
and interval the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] (U : BlockUniverse Validator BlockId Payload)
    (wa I : ℕ),
    EvidenceConsistent U ∧ WindowCount U wa I ∧ CommitsSound U ∧ UpdateInRange U I ∧
      CommitWeightExact U wa I ∧ CandidatesDvd U I

end Replay

end MahiMahiPair

end Steelhead

end LeanDag
