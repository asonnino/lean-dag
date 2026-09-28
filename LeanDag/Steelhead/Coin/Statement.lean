import LeanDag.Steelhead.Model.Coin
import LeanDag.Steelhead.Model.Clauses
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# The coin at any pair of rules — statement

The probability half of liveness under asynchrony (`steelhead.md` §4),
the paper's Theorem 3 read through a uniform coin, at any pair of rules
and any good set. The asynchronous rule enters through its good set,
which commits (`GoodCommits`), and the counting lemma's floor
(`GoodFloor`): on the records a population hypothesis `Pop` holds of, the
good set of a round holds at least `floor` validators. The pair enters
through its laws (`RulePair.Lawful`) and the length `wa` of its
asynchronous wave. `MahiMahiPair/Coin/Statement.lean` states the claims at
the Mysticeti and Mahi-Mahi pair, where MM2 gives the floor `n − f − b` at
`wa ≥ 5` and one at `wa ≥ 4`; `BlueBottlePair/Coin/Statement.lean` at
BlueBottle's, where ABB7 gives `n − 3f`. Nineteen claims:

* **SH11a, the commit probability** — on a round the population
  hypothesis holds at, the coin names a good leader with probability at
  least `floor / n`;
* **SH11c, the coin names a Byzantine leader with probability `b / n`**,
  at most `f / n`;
* **SH11d, the run probability** — over `m` such rounds with independent
  coins, every coin is good with probability at least `(floor / n)^m`;
* **SH11e, a good coin commits the chain slot** — at any schedule whose
  slot is proposed at the coin's round and led by it, in every view
  holding the slot's decision round;
* **SH11f, the tail** — no coin of `m` such rounds is good with
  probability at most `((n − floor) / n)^m`;
* **SH11g, the tail vanishes** at a positive floor;
* **SH11h, the adaptive block bound** — the block bound for good sets
  that read the coins already drawn, as for a fixed family;
* **SH11i, the search under the coin** — at period one a slot below `M`
  blocks of `wa` coins stays undecided with probability at most the
  chance that every block holds a bad coin, `badBlockBoundAt floor wa`
  per block;
* **SH11j, the expected wait of the search at period one** — at most
  `(n / floor)^wa` blocks, and a view holding the first good block's
  decision rounds decides the slot;
* **SH11l, a scan's control slots all miss** with probability at most
  `((n − floor) / n)^c` at `c` slots;
* **SH11m, the expected number of scans before one anchors** — at most
  `1 / (1 − ((n − floor) / n)^c)`;
* **SH15a, the output is live but for a vanishing probability** — over
  the coins of `M` blocks of `wa · K` rounds above a slot, the slot stays
  undecided with probability at most twice `badBlockBoundAt floor (wa · K)`
  to the `M / 2`: a good block in each half decides it (SH14c);
* **SH15b, the tail against an adaptive adversary** — SH15a with the
  record the adversary's answer to the coins already drawn and a floor
  of good candidates the next draw cannot shrink;
* **SH15c, that tail vanishes** at a positive floor;
* **SH15e, the slot is decided almost surely** over a sequence of
  records, the coin a process;
* **SH15f, some interval is anchored almost surely**;
* **SH15g, almost surely against an adaptive adversary**;
* **SH15h, every slot is decided almost surely**;
* **SH15i, a matching sequence exists** at a lawful pair.

SH11i and SH11j ask of the pair only that both tie-breaks have a choice,
the drain being all they decide by. The Mahi-Mahi pair's SH-MM11b,
SH-MM11k and SH-MM15d are SH11a, SH11j and SH15a at a floor of one, and
have no generic statement of their own.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Coin

open Filter Topology MeasureTheory
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **The chance that a block of `K` coins holds a bad one at a floor of `c`**:
`(n^K − c^K) / n^K`, the bound SH11i and SH15 state their tails in. -/
noncomputable def badBlockBoundAt (Validator : Type) [Fintype Validator] (c K : ℕ) : ℝ≥0∞ :=
  ((Fintype.card Validator ^ K - c ^ K : ℕ) : ℝ≥0∞) / (Fintype.card Validator : ℝ≥0∞) ^ K

/-- **SH11a, the commit probability.** -/
def CommitProbability (U : BlockUniverse Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop) (floor : ℕ) :
    Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- the counting lemma's floor, at a round the population hypothesis holds at
    GoodFloor good Pop floor → Pop U T r →
    -- then the coin names a good leader with probability at least floor / n
    (floor : ℝ≥0∞) / Fintype.card Validator ≤ commitProb (good U) r

/-- **SH11c, the coin names a Byzantine leader with probability `b / n`.** -/
def ByzantineLeaderProbability : Prop :=
  -- the uniform coin lands among the Byzantine validators with their density ...
  (PMF.uniformOfFintype Validator).toOuterMeasure ↑F.byzantine =
      (F.byzantine.card : ℝ≥0∞) / Fintype.card Validator ∧
    -- ... which is at most f / n
    (PMF.uniformOfFintype Validator).toOuterMeasure ↑F.byzantine ≤
      (F.f : ℝ≥0∞) / Fintype.card Validator

/-- **SH11d, the run probability.** -/
def RunProbability (U : BlockUniverse Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop) (floor : ℕ) :
    Prop :=
  ∀ (T : Finset Validator) (r₀ m : ℕ),
    -- the counting lemma's floor, at each of the m rounds from r₀
    GoodFloor good Pop floor → (∀ i : Fin m, Pop U T (r₀ + i)) →
    -- then every one of those rounds names a good leader with probability at least (floor / n)^m
    ((floor : ℝ≥0∞) / Fintype.card Validator) ^ m ≤ runProb (good U) r₀ m

/-- **SH11e, a good coin commits the chain slot.** -/
def CommitOfCoin (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) : Prop :=
  ∀ (S' : Slots Validator) (coin : ℕ → Validator) (V : View Validator BlockId Payload U)
    (i r : ℕ),
    -- the rule's good set commits
    GoodCommits R good →
    -- slot i of the schedule is proposed at round r and led by that round's coin
    S'.slotRound i = r → S'.leader i = coin r →
    -- the coin of round r names a good leader
    coin r ∈ good U r →
    -- and the view holds the slot's decision round
    V.CoversUpto (r + R.waveAt (S'.kind i)) →
    -- then the slot commits its candidate in that view
    ∃ L, IsLeaderBlock (S := S') U i L ∧ R.Decided (S := S') U V i (some L)

/-- **SH11f, the tail.** -/
def NoCommitTail (U : BlockUniverse Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop) (floor : ℕ) :
    Prop :=
  ∀ (T : Finset Validator) (r₀ m : ℕ),
    -- the counting lemma's floor, at each of the m rounds from r₀
    GoodFloor good Pop floor → (∀ i : Fin m, Pop U T (r₀ + i)) →
    -- then no coin of those rounds is good with probability at most ((n − floor) / n)^m
    noCommitProb (good U) r₀ m ≤
      (((Fintype.card Validator - floor : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m

/-- **SH11g, the tail vanishes.** -/
def TailVanishes (floor : ℕ) : Prop :=
  0 < floor →
    Tendsto (fun m : ℕ =>
      (((Fintype.card Validator - floor : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m) atTop (𝓝 0)

/-- **SH11h, the adaptive block bound.** -/
def AdaptiveBlockBound (K : ℕ) : Prop :=
  ∀ (M c : ℕ) (H : Finset (Fin M))
    (G : (Fin M → Fin K → Validator) → Fin M → Fin K → Finset Validator),
    -- the good sets read only the coins drawn before their own round, those of the blocks below
    -- and of the block's earlier rounds ...
    (∀ g g' (j : Fin M) (i : Fin K), (∀ j' : Fin M, j' < j → g j' = g' j') →
      (∀ i' : Fin K, i' < i → g j i' = g' j i') → G g j i = G g' j i) →
    -- ... and each holds at least c validators
    (∀ g j i, c ≤ (G g j i).card) →
    -- then every block of H holds a bad coin with at most the fixed family's probability
    (PMF.uniformOfFintype (Fin M → Fin K → Validator)).toOuterMeasure
        {g | ∀ j ∈ H, ∃ i, g j i ∉ G g j i} ≤
      badBlockBoundAt Validator c K ^ H.card

/-- **SH15a, the output is live but for a vanishing probability.** -/
def UndecidedTail (U : BlockUniverse Validator BlockId Payload)
    (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop)
    (floor wa I K : ℕ) [NeZero K] : Prop :=
  ∀ (T : Finset Validator) (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator)
    (d : Validator) (q s M : ℕ),
    -- the pair is lawful, its asynchronous rule's good set commits, and the counting lemma's floor
    p.Lawful → GoodCommits p.async good → GoodFloor good Pop floor →
    -- the synchronous wave is no longer than the asynchronous one, whose length is wa
    p.sync.waveAt 0 ≤ p.async.waveAt 1 → p.async.waveAt 1 + 1 = wa →
    -- the period bound and the asynchronous wave within an interval, blocks of wa · K rounds that
    -- end before the next block opens, q intervals up, and a slot at round one or above
    K ≤ I → wa ≤ I → wa * K ≤ q * I → 1 ≤ s →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- the population hypothesis holds at every round of the M blocks
    (∀ (j : Fin M) (i : Fin (wa * K)), Pop U T (blockRound I q (intervalOf I s) j i)) →
    -- then the slot stays undecided with probability at most twice the chance that each of M/2
    -- blocks holds a bad coin
    undecidedProb U p.async (steelheadAt p) wa I q K upd k₀ known d s M ≤
      2 * badBlockBoundAt Validator floor (wa * K) ^ (M / 2)

/-- **SH15b, the tail against an adaptive adversary.** -/
def UndecidedTailAgainst (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (floor wa I K : ℕ) [NeZero K] : Prop :=
  ∀ (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (d : Validator) (q s M : ℕ)
    (σ : (Fin M → Fin (wa * K) → Validator) → BlockUniverse Validator BlockId Payload)
    (G : (Fin M → Fin (wa * K) → Validator) → Fin M → Fin (wa * K) → Finset Validator),
    -- the pair is lawful and its asynchronous rule's good set commits
    p.Lawful → GoodCommits p.async good →
    -- the waves, the period bound and the asynchronous wave within an interval, blocks of
    -- wa · K rounds that end before the next block opens, q intervals up, and a slot at round
    -- one or above
    p.sync.waveAt 0 ≤ p.async.waveAt 1 → p.async.waveAt 1 + 1 = wa →
    K ≤ I → wa ≤ I → wa * K ≤ q * I → 1 ≤ s →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- the adversary builds its record from the coins already drawn, with a floor of good
    -- candidates at every round of the blocks that the round's own coin cannot shrink ...
    NonAnticipating σ G good I q (intervalOf I s) →
    -- ... and the floor holds at least floor validators
    (∀ g j i, floor ≤ (G g j i).card) →
    -- then the slot stays undecided with the probability SH15a gives against a fixed record
    undecidedProbAgainst p.async (steelheadAt p) wa I q σ upd k₀ known d s ≤
      2 * badBlockBoundAt Validator floor (wa * K) ^ (M / 2)

/-- **SH15c, the tail vanishes.** -/
def UndecidedTailVanishes (floor K : ℕ) : Prop :=
  0 < floor →
    Tendsto (fun M : ℕ => 2 * badBlockBoundAt Validator floor K ^ (M / 2)) atTop (𝓝 0)

/-- **SH15e, the slot is decided almost surely.** -/
def DecidedAlmostSurely (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop)
    (floor wa I K : ℕ) [NeZero K] : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (U : ℕ → BlockUniverse Validator BlockId Payload) (T : Finset Validator)
    (upd : ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (q s : ℕ),
    -- the pair is lawful, its asynchronous rule's good set commits, and a positive floor
    p.Lawful → GoodCommits p.async good → GoodFloor good Pop floor → 0 < floor →
    -- the waves, the period bound and the asynchronous wave within an interval, blocks of
    -- wa · K rounds that end before the next block opens, q intervals up, and a slot at round
    -- one or above
    p.sync.waveAt 0 ≤ p.async.waveAt 1 → p.async.waveAt 1 + 1 = wa →
    K ≤ I → wa ≤ I → wa * K ≤ q * I → 1 ≤ s →
    -- the initial period lies in [1, K], and every update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K) →
    -- record m holds the waves of m blocks, the population hypothesis at every round of them
    (∀ (m : ℕ) (j : Fin m) (i : Fin (wa * K)),
      Pop (U m) T (blockRound I q (intervalOf I s) j i)) →
    -- then for almost every coin some record decides s in every view holding its horizon, at
    -- every period sequence matching what the view derives
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (U m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K p.async (steelheadAt p) coin known (upd m) k₀ (U m) V per →
        Settles I K p.async (steelheadAt p) coin known (upd m) k₀ (U m) V per s

/-- **SH15g, almost surely against an adaptive adversary.** -/
def DecidedAlmostSurelyAgainst (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (floor wa I K : ℕ) [NeZero K] : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (σ : ∀ m : ℕ, (Fin m → Fin (wa * K) → Validator) → BlockUniverse Validator BlockId Payload)
    (G : ∀ m : ℕ, (Fin m → Fin (wa * K) → Validator) → Fin m → Fin (wa * K) → Finset Validator)
    (upd : ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (q s : ℕ),
    -- the pair is lawful, its asynchronous rule's good set commits, and a positive floor
    p.Lawful → GoodCommits p.async good → 0 < floor →
    -- the waves, the period bound and the asynchronous wave within an interval, blocks of
    -- wa · K rounds that end before the next block opens, q intervals up, and a slot at round
    -- one or above
    p.sync.waveAt 0 ≤ p.async.waveAt 1 → p.async.waveAt 1 + 1 = wa →
    K ≤ I → wa ≤ I → wa * K ≤ q * I → 1 ≤ s →
    -- the initial period lies in [1, K], and every update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K) →
    -- every strategy of the sequence answers the draws already made, with its floor ...
    (∀ m, NonAnticipating (σ m) (G m) good I q (intervalOf I s)) →
    -- ... and every floor holds at least floor validators
    (∀ (m : ℕ) (g : Fin m → Fin (wa * K) → Validator) (j : Fin m) (i : Fin (wa * K)),
      floor ≤ (G m g j i).card) →
    -- then for almost every coin some strategy's own record decides s in every view holding its
    -- horizon, at every period sequence matching what the view derives
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload
          (σ m (blockCoins I q (intervalOf I s) m (wa * K) coin)))
        (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K p.async (steelheadAt p) coin known (upd m) k₀
          (σ m (blockCoins I q (intervalOf I s) m (wa * K) coin)) V per →
        Settles I K p.async (steelheadAt p) coin known (upd m) k₀
          (σ m (blockCoins I q (intervalOf I s) m (wa * K) coin)) V per s

/-- **SH15h, every slot is decided almost surely.** -/
def AllDecidedAlmostSurely (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop)
    (floor wa I K : ℕ) [NeZero K] : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (U : ℕ → ℕ → BlockUniverse Validator BlockId Payload) (T : Finset Validator)
    (upd : ℕ → ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (q : ℕ),
    -- the pair is lawful, its asynchronous rule's good set commits, and a positive floor
    p.Lawful → GoodCommits p.async good → GoodFloor good Pop floor → 0 < floor →
    -- the waves, the period bound and the asynchronous wave within an interval, and blocks of
    -- wa · K rounds that end before the next block opens, q intervals up
    p.sync.waveAt 0 ≤ p.async.waveAt 1 → p.async.waveAt 1 + 1 = wa →
    K ≤ I → wa ≤ I → wa * K ≤ q * I →
    -- the initial period lies in [1, K], and every update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ s m A k, 1 ≤ k → k ≤ K → 1 ≤ upd s m A k ∧ upd s m A k ≤ K) →
    -- for every slot, record m of the slot's sequence holds the waves of m blocks above the
    -- slot's interval, the population hypothesis at every round of them
    (∀ (s m : ℕ) (j : Fin m) (i : Fin (wa * K)),
      Pop (U s m) T (blockRound I q (intervalOf I s) j i)) →
    -- then for almost every coin, every slot at round one or above is decided by some record of
    -- its sequence, in every view holding that record's horizon
    ∀ᵐ coin ∂(coinMeasure Validator), ∀ s, 1 ≤ s → ∃ m,
      ∀ (V : View Validator BlockId Payload (U s m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K p.async (steelheadAt p) coin known (upd s m) k₀ (U s m) V per →
        Settles I K p.async (steelheadAt p) coin known (upd s m) k₀ (U s m) V per s

/-- **SH15f, some interval is anchored almost surely.** -/
def AnchoredAlmostSurely (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop)
    (floor wa I K : ℕ) [NeZero K] : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (U : ℕ → BlockUniverse Validator BlockId Payload) (T : Finset Validator)
    (upd : ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (q s : ℕ),
    -- the pair is lawful, its asynchronous rule's good set commits, and a positive floor
    p.Lawful → GoodCommits p.async good → GoodFloor good Pop floor → 0 < floor →
    -- the waves, the period bound and the asynchronous wave within an interval, blocks of
    -- wa · K rounds that end before the next block opens, q intervals up, and a slot at round
    -- one or above
    p.sync.waveAt 0 ≤ p.async.waveAt 1 → p.async.waveAt 1 + 1 = wa →
    K ≤ I → wa ≤ I → wa * K ≤ q * I → 1 ≤ s →
    -- the initial period lies in [1, K], and every update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K) →
    -- record m holds the waves of m blocks, the population hypothesis at every round of them
    (∀ (m : ℕ) (j : Fin m) (i : Fin (wa * K)),
      Pop (U m) T (blockRound I q (intervalOf I s) j i)) →
    -- then for almost every coin some record has, in every view holding its horizon and at every
    -- period sequence matching what the view derives, an anchored interval above the slot's
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (U m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K p.async (steelheadAt p) coin known (upd m) k₀ (U m) V per →
        Anchored I K p.async (steelheadAt p) coin known (upd m) k₀ (U m) V per s

/-- **SH11i, the search under the coin.** -/
def UndecidedAtPeriodOne (U : BlockUniverse Validator BlockId Payload)
    (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop)
    (floor wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (d : Validator) (s b M : ℕ),
    -- both rules have a tie-break choice, the asynchronous rule's good set commits, the counting
    -- lemma's floor, and the asynchronous wave is wa rounds long
    LeastLinked p.sync → LeastLinked p.async → GoodCommits p.async good →
    GoodFloor good Pop floor → p.async.waveAt 1 + 1 = wa →
    -- the slot lies below the blocks
    s < b →
    -- the population hypothesis holds at every round of the M blocks of wa rounds from b
    (∀ (j : Fin M) (i : Fin wa), Pop U T (b + j * wa + i)) →
    -- and the view holds the last block's decision rounds
    V.CoversUpto (b + M * wa - 1 + (wa - 1)) →
    -- then the slot stays undecided at period one, on the chain schedule of those coins, with
    -- probability at most the chance that every one of the M blocks holds a bad coin
    (PMF.uniformOfFintype (Fin M → Fin wa → Validator)).toOuterMeasure
        {g | ∀ v, ¬ (steelheadAt p).Decided (S := chainSlots (coinOfBlocksFrom b g d)) U V s v}
      ≤ badBlockBoundAt Validator floor wa ^ M

/-- **SH11j, the expected wait of the search at period one.** -/
def ExpectedWaitAtPeriodOne (U : BlockUniverse Validator BlockId Payload)
    (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop)
    (floor wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (d : Validator) (s b M : ℕ),
    -- both rules have a tie-break choice, the asynchronous rule's good set commits, the counting
    -- lemma's floor, no larger than the committee, and the asynchronous wave is wa rounds long
    LeastLinked p.sync → LeastLinked p.async → GoodCommits p.async good →
    GoodFloor good Pop floor → floor ≤ Fintype.card Validator → p.async.waveAt 1 + 1 = wa →
    -- the slot lies below the blocks
    s < b →
    -- the population hypothesis holds at every round of the M blocks of wa rounds from b
    (∀ (j : Fin M) (i : Fin wa), Pop U T (b + j * wa + i)) →
    -- then the number of blocks the search waits for, the first good one included and capped at
    -- M, is in expectation at most (n / floor)^wa, the paper's 1 / p^wa ...
    (∑ g : Fin M → Fin wa → Validator, PMF.uniformOfFintype (Fin M → Fin wa → Validator) g *
        ((firstGoodBlock (good U) wa b g + 1 : ℕ) : ℝ≥0∞)) ≤
      ((Fintype.card Validator : ℝ≥0∞) / (floor : ℝ≥0∞)) ^ wa ∧
    -- ... and once a view holds the decision rounds of the first good block, the slot is decided
    -- at period one on the chain schedule of those coins
    (∀ g : Fin M → Fin wa → Validator, firstGoodBlock (good U) wa b g < M →
      V.CoversUpto (b + (firstGoodBlock (good U) wa b g + 1) * wa - 1 + (wa - 1)) →
      ∃ v, (steelheadAt p).Decided (S := chainSlots (coinOfBlocksFrom b g d)) U V s v)

/-- **SH11l, a scan's control slots all miss.** -/
def NoCommitOnScan (U : BlockUniverse Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop) (floor : ℕ) :
    Prop :=
  ∀ (T : Finset Validator) (c : ℕ) (ρ : Fin c → ℕ),
    -- the counting lemma's floor, at every slot's round
    GoodFloor good Pop floor → (∀ i : Fin c, Pop U T (ρ i)) →
    -- then every slot of the scan misses with probability at most ((n − floor) / n)^c
    noCommitProbOn (good U) ρ ≤
      (((Fintype.card Validator - floor : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ c

/-- **SH11m, the expected number of scans before one anchors.** -/
def ExpectedIntervalsToAnchor (U : BlockUniverse Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop) (floor : ℕ) :
    Prop :=
  ∀ (T : Finset Validator) (M c : ℕ) (ρ : Fin M → Fin c → ℕ),
    -- the counting lemma's floor, at every slot's round
    GoodFloor good Pop floor → (∀ (j : Fin M) (i : Fin c), Pop U T (ρ j i)) →
    -- then the number of scans before one anchors, the anchoring scan included and capped at M,
    -- is in expectation at most 1 / (1 − ((n − floor) / n)^c)
    (∑ g : Fin M → Fin c → Validator, PMF.uniformOfFintype (Fin M → Fin c → Validator) g *
        ((firstGoodInterval (good U) ρ g + 1 : ℕ) : ℝ≥0∞)) ≤
      (1 - (((Fintype.card Validator - floor : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ c)⁻¹

/-- **SH15i, a matching sequence exists.** -/
def MatchesExists (U : BlockUniverse Validator BlockId Payload)
    (p : RulePair Validator BlockId Payload) (I K : ℕ) [NeZero K] : Prop :=
  ∀ (coin known : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U),
    -- the pair is lawful
    p.Lawful →
    -- then some period sequence is the one the view derives, at every interval it derives a
    -- state for
    ∃ per, Matches I K p.async (steelheadAt p) coin known upd k₀ U V per

/-- The coin, over every fault configuration, block universe, rule, pair of rules, good set,
population hypothesis, floor, asynchronous wave, interval and positive period bound the model
admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId]
    (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop)
    (floor wa I K : ℕ) [NeZero K],
    CommitProbability U good Pop floor ∧ ByzantineLeaderProbability (Validator := Validator) ∧
      RunProbability U good Pop floor ∧ CommitOfCoin U R good ∧ NoCommitTail U good Pop floor ∧
      TailVanishes (Validator := Validator) floor ∧
      AdaptiveBlockBound (Validator := Validator) K ∧
      UndecidedTail U p good Pop floor wa I K ∧ UndecidedTailAgainst p good floor wa I K ∧
      UndecidedTailVanishes (Validator := Validator) floor (wa * K) ∧
      DecidedAlmostSurely p good Pop floor wa I K ∧
      DecidedAlmostSurelyAgainst p good floor wa I K ∧
      UndecidedAtPeriodOne U p good Pop floor wa ∧ ExpectedWaitAtPeriodOne U p good Pop floor wa ∧
      NoCommitOnScan U good Pop floor ∧ ExpectedIntervalsToAnchor U good Pop floor ∧
      AllDecidedAlmostSurely p good Pop floor wa I K ∧
      AnchoredAlmostSurely p good Pop floor wa I K ∧ MatchesExists U p I K

end Coin

end Steelhead

end LeanDag
