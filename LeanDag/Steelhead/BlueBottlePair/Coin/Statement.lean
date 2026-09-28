import LeanDag.Steelhead.Model.Pair
import LeanDag.Steelhead.Model.Coin
import LeanDag.Steelhead.Model.Clauses
import LeanDag.Steelhead.Coin.Statement
import LeanDag.AsyncBlueBottle.Model.Good
/-!
# The `5f + 1` pair's coin — statement

The coin at BlueBottle's two variants, the good set Async BlueBottle's
`goodAt` and the counting lemma ABB7: on a reliable quorum populating the
two rounds above a round, at least `n − 3f` correct validators' blocks of
that round are directly committed. The generic statements of
`Coin/Statement.lean` read the pair through its laws, its good set and
that floor; this file states that the pair meets them, and the paper's
coin claims at the pair as the generic statements then give them. Five
claims:

* **SH-BB11, the pair meets the coin's hypotheses** — the pair is lawful,
  Async BlueBottle's good set commits, ABB7 is the floor `n − 3f`, which
  is positive and at most `n`, and the waves are two and three rounds;
* **SH-BB11a, the commit probability** — the paper's `p ≥ (n − 3f) / n`
  at the pair: on a round a reliable quorum has populated two rounds up,
  the coin names a committed leader with at least that probability;
* **SH-BB11j, the expected wait of the search at period one** — at most
  `(n / (n − 3f))^3` blocks of three coins, the paper's `1 / p^3`, and a
  view holding the first good block's decision rounds decides the slot;
* **SH-BB15a, the output is live but for a vanishing probability** —
  SH15a at the pair, the block bound at the floor `n − 3f` and blocks of
  `3 · K` rounds;
* **SH-BB15e, the slot is decided almost surely** — SH15e at the pair.

Odontoceti and Async BlueBottle are consumed read-only.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Coin

open Filter Topology MeasureTheory
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **The population ABB7 reads**: a reliable quorum, correct and of quorum size, populating the
two rounds above round `r`. -/
def Populated (U : BlockUniverse Validator BlockId Payload) (T : Finset Validator) (r : ℕ) :
    Prop :=
  T ⊆ (Correct : Finset Validator) ∧ quorumCard Validator ≤ T.card ∧
    PopulatedOn U T (r + 1) ∧ PopulatedOn U T (r + 2)

/-- **SH-BB11, the pair meets the coin's hypotheses.** -/
def CoinHypotheses (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [F : Faults5 Validator] [LinearOrder BlockId] : Prop :=
  -- the pair is lawful, and Async BlueBottle's good set commits
  (bbPair Validator BlockId Payload).Lawful ∧
    GoodCommits (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload)
      (fun U r => AsyncBlueBottle.goodAt U r) ∧
    -- ABB7 is the floor n − 3f, positive and at most n
    GoodFloor (fun (U : BlockUniverse Validator BlockId Payload) r => AsyncBlueBottle.goodAt U r)
      Populated (Fintype.card Validator - 3 * F.f) ∧
    0 < Fintype.card Validator - 3 * F.f ∧
    Fintype.card Validator - 3 * F.f ≤ Fintype.card Validator ∧
    -- the synchronous wave is no longer than the asynchronous one, three rounds long
    (bbPair Validator BlockId Payload).sync.waveAt 0 ≤
      (bbPair Validator BlockId Payload).async.waveAt 1 ∧
    (bbPair Validator BlockId Payload).async.waveAt 1 + 1 = 3

/-- **SH-BB11a, the commit probability.** -/
def CommitProbability (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- a reliable quorum populates the two rounds above round r
    Populated U T r →
    -- then the coin names a committed leader with probability at least (n − 3f) / n
    ((Fintype.card Validator - 3 * F.f : ℕ) : ℝ≥0∞) / Fintype.card Validator ≤
      commitProb (AsyncBlueBottle.goodAt U) r

/-- **SH-BB11j, the expected wait of the search at period one.** -/
def ExpectedWaitAtPeriodOne (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (d : Validator) (s b M : ℕ),
    -- the slot lies below the blocks, and a reliable quorum populates the two rounds above every
    -- round of the M blocks of three rounds from b
    s < b → (∀ (j : Fin M) (i : Fin 3), Populated U T (b + j * 3 + i)) →
    -- then the number of blocks the search waits for, the first good one included and capped at
    -- M, is in expectation at most (n / (n − 3f))^3 ...
    (∑ g : Fin M → Fin 3 → Validator, PMF.uniformOfFintype (Fin M → Fin 3 → Validator) g *
        ((firstGoodBlock (AsyncBlueBottle.goodAt U) 3 b g + 1 : ℕ) : ℝ≥0∞)) ≤
      ((Fintype.card Validator : ℝ≥0∞) /
        ((Fintype.card Validator - 3 * F.f : ℕ) : ℝ≥0∞)) ^ 3 ∧
    -- ... and once a view holds the decision rounds of the first good block, the pair decides the
    -- slot at period one on the chain schedule of those coins
    (∀ g : Fin M → Fin 3 → Validator, firstGoodBlock (AsyncBlueBottle.goodAt U) 3 b g < M →
      V.CoversUpto (b + (firstGoodBlock (AsyncBlueBottle.goodAt U) 3 b g + 1) * 3 - 1 + 2) →
      ∃ v, (blueBottlePairAnchored Validator BlockId Payload).Decided
        (S := chainSlots (coinOfBlocksFrom b g d)) U V s v)

/-- **SH-BB15a, the output is live but for a vanishing probability.** -/
def UndecidedTail (U : BlockUniverse Validator BlockId Payload) (I K : ℕ) [NeZero K] : Prop :=
  ∀ (T : Finset Validator) (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator)
    (d : Validator) (q s M : ℕ),
    -- the period bound and the asynchronous wave within an interval, blocks of 3 · K rounds that
    -- end before the next block opens, q intervals up, and a slot at round one or above
    K ≤ I → 3 ≤ I → 3 * K ≤ q * I → 1 ≤ s →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- a reliable quorum populates the two rounds above every round of the M blocks
    (∀ (j : Fin M) (i : Fin (3 * K)), Populated U T (blockRound I q (intervalOf I s) j i)) →
    -- then the slot stays undecided with probability at most twice the chance that each of M/2
    -- blocks holds a bad coin, at the floor n − 3f
    undecidedProb U (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload)
        (blueBottlePairAnchored Validator BlockId Payload) 3 I q K upd k₀ known d s M ≤
      2 * Steelhead.Coin.badBlockBoundAt Validator
        (Fintype.card Validator - 3 * F.f) (3 * K) ^ (M / 2)

/-- **SH-BB15e, the slot is decided almost surely.** -/
def DecidedAlmostSurely (I K : ℕ) [NeZero K] : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (U : ℕ → BlockUniverse Validator BlockId Payload) (T : Finset Validator)
    (upd : ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (q s : ℕ),
    -- the period bound and the asynchronous wave within an interval, blocks of 3 · K rounds that
    -- end before the next block opens, q intervals up, and a slot at round one or above
    K ≤ I → 3 ≤ I → 3 * K ≤ q * I → 1 ≤ s →
    -- the initial period lies in [1, K], and every update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K) →
    -- record m holds the waves of m blocks, a reliable quorum populating the two rounds above
    -- every round of them
    (∀ (m : ℕ) (j : Fin m) (i : Fin (3 * K)),
      Populated (U m) T (blockRound I q (intervalOf I s) j i)) →
    -- then for almost every coin some record decides s in every view holding its horizon, at
    -- every period sequence matching what the view derives
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (U m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q 3 K (intervalOf I s) m) →
        Matches I K (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload)
          (blueBottlePairAnchored Validator BlockId Payload) coin known (upd m) k₀ (U m) V per →
        Settles I K (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload)
          (blueBottlePairAnchored Validator BlockId Payload) coin known (upd m) k₀ (U m) V per s

/-- The `5f + 1` pair's coin, over every fault configuration, block universe, interval and positive
period bound the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId]
    (U : BlockUniverse Validator BlockId Payload) (I K : ℕ) [NeZero K],
    CoinHypotheses Validator BlockId Payload ∧ CommitProbability U ∧ ExpectedWaitAtPeriodOne U ∧
      UndecidedTail U I K ∧
      DecidedAlmostSurely (Validator := Validator) (BlockId := BlockId) (Payload := Payload) I K

end Coin

end BlueBottlePair

end Steelhead

end LeanDag
