import LeanDag.Steelhead.Model.Coin
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# The coin — statement

The probability half of liveness under asynchrony (`steelhead.md` §4),
the paper's Theorem 3 read through a uniform coin, and the
asynchronous-floor clause of its Theorem 2. Twenty-three claims:

* **SH11a, the commit probability** — on a wave a quorum has populated,
  the coin of round `r` names a directly committed leader with
  probability at least `(n − f − |byzantine|) / n`, hence at least
  `1/3`: MM2 at `wa ≥ 5` under a uniform draw;
* **SH11b, the commit probability at wave four**: at `wa ≥ 4` MM2
  promises one committed correct candidate, so the coin names a
  committed leader with probability at least `1/n`, the paper's
  wavelength-four trade-off;
* **SH11c, the coin names a Byzantine leader with probability `b / n`**:
  the protocol section's "an asynchronous slot whose Byzantine leader
  equivocates, probability at most `b / n`": the uniform coin lands among
  the `b` Byzantine validators with their density, at most `f / n`;
* **SH11d, the run probability** — the positive form the paper's
  Theorem 3 (ii) states: over `m` consecutive populated waves with
  independent coins, every round's coin names a directly committed
  leader with probability at least `((n − f − b) / n)^m`, which at
  `m = wa` is the run a window is asked to hold. The complementary
  bound is SH11f, and neither implies the other: SH11f bounds the
  chance that no round commits;
* **SH11e, a good coin commits the chain slot** — at any schedule
  whose slot is proposed at the coin's round and led by it, the coin
  schedule and every control schedule among them, in every view caught
  up to the decision round;
* **SH11f, the tail** — over `m` consecutive populated waves with
  independent coins, no round's coin names a directly committed leader
  with probability at most `((f + |byzantine|) / n)^m`;
* **SH11g, the tail vanishes** — that bound tends to zero, since
  `f + |byzantine| ≤ 2f < n`;
* **SH11h, the adaptive block bound** — the same bound for good sets
  that read the coins already drawn: if the good set of every round is
  fixed by the coins drawn before it, those of the blocks below and of
  the block's earlier rounds, and holds at least `c` validators, then
  every block of a set holds a bad coin with probability at most
  `((n^K − c^K) / n^K)` to the size of that set, as for a fixed family.
  The count peels the last block, whose bad set the earlier ones fix,
  and inside a block the last round, whose good set the earlier rounds
  fix, so the argument is a count over a finite type with no
  conditioning to state;
* **SH15a, the output is live but for a vanishing probability** —
  Theorem 3's "with probability `1`", in the form a finite record
  admits: over the uniform independent coins of `M` blocks of `wa · K`
  rounds, one opening every `q`-th interval from the second after a
  slot's at round one or above, where `wa · K ≤ q · I` so that a block
  ends before the next opens, under any update rule keeping the period
  in `[1, K]`, some view holding the horizon, at a period sequence
  matching what it derives, has not derived the state of the slot's
  interval or leaves the slot undecided, with probability at most
  `2 · ((n^(wa·K) − (n − f − b)^(wa·K)) / n^(wa·K))^(M/2)`. A good block
  holds `wa` consecutive multiples of `K`, the control slots every scan
  below it reads above its boundary, so it settles every scan below its
  interval (SH7a at each scan's schedule) and the states are derived up
  to it; its first `K` rounds cover the first control round of the
  interval it opens, at whatever period the view derived for it, so it
  anchors that interval; and its first `wa` rounds are a run at period
  `1`. Two good blocks in different halves then decide the slot (SH14c),
  and each half holds no good block with the probability the counting
  lemma bounds block by block. A scan that
  never reaches the slot's interval counts as a failure, and a slot
  counts as decided only under every completion of the derived periods;
* **SH15b, the tail against an adaptive adversary** — SH15a where the
  record is the adversary's own answer to the coins already drawn
  (`NonAnticipating`, `undecidedProbAgainst`): at every block map the
  event reads the record that map produced, and the bound is unchanged,
  by SH11h. The adversary names, at every round of the blocks, a floor
  of candidates its record commits directly, fixed by the coins drawn
  before that round and holding the counting lemma's `n − f − b`; it
  may commit more once the coin is out, and what it may not do is take a
  candidate out of the floor after the draw. The floor's size is a
  hypothesis: the counting lemma gives it for the record as built, and
  that the round's own coin leaves it is what A5's reveal timing
  supplies, which the model does not state;
* **SH15c, that tail vanishes** — the bound tends to zero as the number
  of blocks grows, since `n − f − b ≥ 1`;
* **SH15d, the tail at wave four** — SH15a at `4 ≤ wa`, the wave the
  implementation also accepts for the Mysticeti/Mahi-Mahi pair: the
  counting lemma's weaker form promises one committed correct candidate
  per populated round (SH11b), so a block of `wa · K` coins holds a bad
  one with probability at most `(n^(wa·K) − 1) / n^(wa·K)`, and the same
  two-halves argument bounds the failure by twice that to the `M/2`,
  which tends to zero as well;
* **SH15e, the slot is decided almost surely** — Theorem 3's "with
  probability `1`" itself, over a sequence of finite records, the `m`-th
  holding the waves of `m` blocks, and the coin drawn as a process
  (`coinMeasure`, the infinite product of the uniform distribution): for
  almost every coin some record settles the slot in every view holding
  its horizon, in SH15a's sense (`Matches`, `Settles`). The coins under which no record decides
  it lie, for every `m`, among those under which the `m`-th leaves it
  undecided, a set of measure at most SH15a's bound, which vanishes
  (SH15c); so they are null. The records are any sequence, the prefixes
  of one execution among them, since the argument reads each on its own;
* **SH11i, the search under the coin** — Theorem 2's asynchronous-floor
  clause in the form that holds: at period one a slot below a block of
  `wa` coin rounds naming committed candidates is decided, by the drain
  (SH9a), so over `M` consecutive blocks of `wa` coins above the slot it
  stays undecided with probability at most
  `((n^wa − (n − f − b)^wa) / n^wa)^M`, the chance that every block holds
  a bad coin, the paper's `(1 − p^{wa})^M` after `M` attempts. No bound
  per hop of the anchor search holds: a landing of the search is not a
  function of the coins below it, since the coin that commits an anchor
  above a pending slot both skips that slot and leads the next landing,
  and `LeanDagTest/Steelhead/Counterexamples/HopBound.lean` exhibits two landings led by
  the one Byzantine validator with probability above `(b/n)^2`;
* **SH11j, the expected wait of the search at period one** — Theorem
  2's expectation above an asynchronous floor, in the form SH11i admits:
  the search waits for the first good block among `M` blocks of `wa`
  coins, the good one included, so for `firstGoodBlock + 1` blocks, and
  that count is in expectation at most `(n / (n − f − b))^wa`, the
  paper's `1 / p^wa`, whatever the horizon `M`; a view holding the good
  block's decision rounds decides the slot by the drain. The expectation
  is the sum over `m` of the chance that the first `m` blocks are all
  bad, at most `(1 − p^wa)^m` each (SH11i's count), whose sum is
  `1 / p^wa`. In rounds, `wa` per block, that is the paper's
  `wa / p^wa`, the decision falling within a wave of the good block;
* **SH11k, the expected wait at wave four** — SH11j at `4 ≤ wa`, where
  the counting lemma's weaker form promises one committed candidate per
  populated round (SH11b): the wait is at most `n^wa` blocks in
  expectation, the paper's `1 / p^wa` at its `p = 1/n`;
* **SH11l, a scan's control slots all miss** — the chance that no slot
  of a scan names a committed candidate is at most `((f + b) / n)^c` at
  `c` slots, SH11f at a schedule rather than a stretch, since control
  slots sit at multiples of the period;
* **SH11m, the expected number of scans before one anchors** — the
  asynchronous section's `1 / (1 − (1 − p)^c)` intervals. The scans'
  misses are independent across intervals, so the wait is a geometric
  series in SH11l's bound, and the sum is the inverse of an anchoring
  scan's chance. The slot count `c` is the paper's `I / period`, which
  the statement takes as given rather than deriving from the schedule;
* **SH15f, some interval is anchored almost surely** — Theorem 3 (i)'s
  "with probability `1` some scan finds its anchor": SH15e's argument
  read at the anchor rather than the decision, since the earlier of the
  two good blocks a failure lacks is what anchors its own interval;
* **SH15g, almost surely against an adaptive adversary** — SH15e where
  the `m`-th record is a strategy's own answer to the coins of its `m`
  blocks: for almost every coin some strategy's record settles the slot,
  by SH15b at each `m`;
* **SH15h, every slot is decided almost surely** — SH15e for all slots
  at once, Theorem 3's "every slot is decided": each slot has its own
  sequence of records, and the slots are countably many, so the null
  sets of SH15e add up to one. What one execution supplies is a prefix
  for every slot and every `m`;
* **SH15i, a matching sequence exists** — SH15a, SH15e, SH15b and SH15g
  quantify over the period sequences matching what a view derives, and
  one always does: the sequence built interval by interval from the
  states the view derives at the sequence built so far, since the state
  of an interval reads the sequence below that interval only (the
  congruence behind SH10b). So none of those claims is empty for want of
  a sequence.

The blocks' coins are drawn after the record is fixed, as SH11f's are,
and the records of SH15e before the process: the adversary that shapes
the DAG does not see them, which is the coin's unpredictability. SH11h,
SH15b and SH15g weaken that to what the argument needs, an adversary
that answers the draws already made and keeps a floor of committed
candidates the next draw cannot shrink. What SH15a leaves to the network
is what SH14c asks of it, that the waves of the blocks be populated; what
SH15b and SH15g leave to it is the floor's size.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Coin

open Filter Topology MeasureTheory
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **SH11a, the commit probability.** -/
def CommitProbability (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- five rounds, a quorum, and the wave populated where MM2 reads it
    5 ≤ wa → quorumCard Validator ≤ T.card →
    PopulatedOn U T (r + 3) → PopulatedOn U T (MahiMahi.decisionRoundAt wa r) →
    -- then the coin names a committed leader with probability at least (n − f − b) / n ...
    ((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator ≤
      commitProb U wa r ∧
    -- ... and so at least 1/3
    (3 : ℝ≥0∞)⁻¹ ≤ commitProb U wa r

/-- **SH11b, the commit probability at wave four.** -/
def CommitProbabilityFour (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r : ℕ),
    -- four rounds, a quorum, and the wave populated where MM2's weaker form reads it
    4 ≤ wa → quorumCard Validator ≤ T.card →
    PopulatedOn U T (r + 2) → PopulatedOn U T (MahiMahi.decisionRoundAt wa r) →
    -- then the coin names a committed leader with probability at least 1 / n
    (Fintype.card Validator : ℝ≥0∞)⁻¹ ≤ commitProb U wa r

/-- **SH11c, the coin names a Byzantine leader with probability `b / n`.** -/
def ByzantineLeaderProbability : Prop :=
  -- the uniform coin lands among the Byzantine validators with their density ...
  (PMF.uniformOfFintype Validator).toOuterMeasure ↑F.byzantine =
      (F.byzantine.card : ℝ≥0∞) / Fintype.card Validator ∧
    -- ... which is at most f / n
    (PMF.uniformOfFintype Validator).toOuterMeasure ↑F.byzantine ≤
      (F.f : ℝ≥0∞) / Fintype.card Validator

/-- **SH11d, the run probability.** -/
def RunProbability (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r₀ m : ℕ),
    -- five rounds, a quorum, and each of the m waves from r₀ populated where MM2 reads it
    5 ≤ wa → quorumCard Validator ≤ T.card →
    (∀ i : Fin m, PopulatedOn U T (r₀ + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (r₀ + i))) →
    -- then every one of those rounds names a committed leader with probability at least
    -- ((n − f − b) / n)^m, which at m = wa is the run the paper asks a window for
    ((((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞) /
      Fintype.card Validator) ^ m) ≤ runProb U wa r₀ m

/-- **SH11e, a good coin commits the chain slot.** -/
def CommitOfCoin (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (S' : Slots Validator) (coin : ℕ → Validator) (V : View Validator BlockId Payload U)
    (i r : ℕ),
    -- slot i of the schedule is proposed at round r and led by that round's coin
    S'.slotRound i = r → S'.leader i = coin r →
    -- the coin of round r names a committed leader
    coin r ∈ MahiMahi.goodAt U wa r →
    -- and the view holds the decision round
    V.CoversUpto (MahiMahi.decisionRoundAt wa r) →
    -- then the slot commits its candidate in that view
    ∃ L, IsLeaderBlock (S := S') U i L ∧ MahiMahi.Decided (S := S') wa U V i (some L)

/-- **SH11f, the tail.** -/
def NoCommitTail (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (r₀ m : ℕ),
    5 ≤ wa → quorumCard Validator ≤ T.card →
    -- each of the m waves from r₀ is populated where MM2 reads it
    (∀ i : Fin m, PopulatedOn U T (r₀ + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (r₀ + i))) →
    -- then no chain slot of those rounds commits with probability at most ((f + b) / n)^m
    noCommitProb U wa r₀ m ≤
      (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m

/-- **SH11g, the tail vanishes.** -/
def TailVanishes : Prop :=
  Tendsto (fun m : ℕ => (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m)
    atTop (𝓝 0)

/-- **The chance that a block of `K` coins holds a bad one**: `(n^K − (n − f − b)^K) / n^K`, the
bound SH15 states its tail in. -/
noncomputable def badBlockBound (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] (K : ℕ) : ℝ≥0∞ :=
  ((Fintype.card Validator ^ K - (Fintype.card Validator - F.f - F.byzantine.card) ^ K : ℕ) :
    ℝ≥0∞) / (Fintype.card Validator : ℝ≥0∞) ^ K

/-- **The chance that a block of `K` coins holds a bad one at wave four**: `(n^K − 1) / n^K`,
the bound SH15d states its tail in, where the counting lemma promises one committed candidate
per round rather than `n − f − b`. -/
noncomputable def badBlockBoundOne (Validator : Type) [Fintype Validator] (K : ℕ) : ℝ≥0∞ :=
  ((Fintype.card Validator ^ K - 1 : ℕ) : ℝ≥0∞) / (Fintype.card Validator : ℝ≥0∞) ^ K

/-- **SH15a, the output is live but for a vanishing probability.** -/
def UndecidedTail (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (T : Finset Validator) (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator)
    (d : Validator) (q s M : ℕ),
    -- the waves, a quorum, the period bound and the asynchronous wave within an interval, and
    -- blocks of wa · K rounds that end before the next block opens, q intervals up
    2 ≤ ws → ws ≤ wa → 5 ≤ wa → K ≤ I → wa ≤ I → wa * K ≤ q * I →
    quorumCard Validator ≤ T.card →
    -- the slot lies at round one or above
    1 ≤ s →
    -- the initial period lies in [1, K], and the update rule keeps a period there, so that a
    -- block from an interval's first round covers its first control round
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- the waves of the M blocks are populated where MM2 reads them
    (∀ (j : Fin M) (i : Fin (wa * K)), PopulatedOn U T (blockRound I q (intervalOf I s) j i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (blockRound I q (intervalOf I s) j i))) →
    -- then the slot stays undecided with probability at most twice the chance that each of M/2
    -- blocks holds a bad coin
    undecidedProb U ws wa I q K upd k₀ known d s M ≤
      2 * badBlockBound Validator (wa * K) ^ (M / 2)

/-- **SH11i, the search under the coin.** Theorem 2's asynchronous-floor clause at period one. -/
def UndecidedAtPeriodOne (U : BlockUniverse Validator BlockId Payload) (ws wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (d : Validator) (s b M : ℕ),
    -- five rounds, a quorum, and the slot below the blocks
    5 ≤ wa → quorumCard Validator ≤ T.card → s < b →
    -- the waves of the M blocks of wa rounds from b are populated where MM2 reads them
    (∀ (j : Fin M) (i : Fin wa), PopulatedOn U T (b + j * wa + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (b + j * wa + i))) →
    -- and the view holds the last block's decision rounds
    V.CoversUpto (MahiMahi.decisionRoundAt wa (b + M * wa - 1)) →
    -- then the slot stays undecided at period one, on the chain schedule of those coins, every
    -- slot of the asynchronous kind, with probability at most the chance that every one of the M
    -- blocks holds a bad coin
    (PMF.uniformOfFintype (Fin M → Fin wa → Validator)).toOuterMeasure
        {g | ∀ v, ¬ Decided (S := chainSlots (coinOfBlocksFrom b g d)) (wavelength ws wa) U V s v}
      ≤ badBlockBound Validator wa ^ M

/-- **SH11j, the expected wait of the search at period one.** Theorem 2's expectation above an
asynchronous floor, in blocks of `wa` rounds. -/
def ExpectedWaitAtPeriodOne (U : BlockUniverse Validator BlockId Payload) (ws wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (d : Validator) (s b M : ℕ),
    -- five rounds, a quorum, and the slot below the blocks
    5 ≤ wa → quorumCard Validator ≤ T.card → s < b →
    -- the waves of the M blocks of wa rounds from b are populated where MM2 reads them
    (∀ (j : Fin M) (i : Fin wa), PopulatedOn U T (b + j * wa + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (b + j * wa + i))) →
    -- then the number of blocks the search waits for, the first good one included and capped at
    -- M, is in expectation at most (n / (n − f − b))^wa, the paper's 1 / p^wa ...
    (∑ g : Fin M → Fin wa → Validator, PMF.uniformOfFintype (Fin M → Fin wa → Validator) g *
        ((firstGoodBlock U wa b g + 1 : ℕ) : ℝ≥0∞)) ≤
      ((Fintype.card Validator : ℝ≥0∞) /
        ((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞)) ^ wa ∧
    -- ... and once a view holds the decision rounds of the first good block, the slot is decided
    -- at period one on the chain schedule of those coins
    (∀ g : Fin M → Fin wa → Validator, firstGoodBlock U wa b g < M →
      V.CoversUpto (MahiMahi.decisionRoundAt wa (b + (firstGoodBlock U wa b g + 1) * wa - 1)) →
      ∃ v, Decided (S := chainSlots (coinOfBlocksFrom b g d)) (wavelength ws wa) U V s v)

/-- **SH11l, a scan's control slots all miss.** The chance that no slot of a scan names a
committed candidate, the slots at any strictly increasing schedule of rounds. -/
def NoCommitOnScan (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (c : ℕ) (ρ : Fin c → ℕ),
    -- five rounds, a quorum, and the scan's slots at distinct rounds, increasing
    5 ≤ wa → quorumCard Validator ≤ T.card → StrictMono ρ →
    -- each slot's wave populated where MM2 reads it
    (∀ i : Fin c, PopulatedOn U T (ρ i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (ρ i))) →
    -- then every slot of the scan misses with probability at most ((f + b) / n)^c
    noCommitProbOn U wa ρ ≤
      (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ c

/-- **SH11m, the expected number of scans before one anchors.** The paper's
`1 / (1 − (1 − p)^c)` intervals, at `c` control slots each. -/
def ExpectedIntervalsToAnchor (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) : Prop :=
  ∀ (T : Finset Validator) (M c : ℕ) (ρ : Fin M → Fin c → ℕ),
    -- five rounds, a quorum, and each scan's slots at distinct rounds, increasing
    5 ≤ wa → quorumCard Validator ≤ T.card → (∀ j : Fin M, StrictMono (ρ j)) →
    -- every slot's wave populated where MM2 reads it
    (∀ (j : Fin M) (i : Fin c), PopulatedOn U T (ρ j i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (ρ j i))) →
    -- then the number of scans before one anchors, the anchoring scan included and capped at M,
    -- is in expectation at most 1 / (1 − ((f + b) / n)^c)
    (∑ g : Fin M → Fin c → Validator, PMF.uniformOfFintype (Fin M → Fin c → Validator) g *
        ((firstGoodInterval U wa ρ g + 1 : ℕ) : ℝ≥0∞)) ≤
      (1 - (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ c)⁻¹

/-- **SH11k, the expected wait of the search at period one, at wave four.** SH11j at `4 ≤ wa`,
where the counting lemma's weaker form promises one committed candidate per populated round. -/
def ExpectedWaitAtPeriodOneFour (U : BlockUniverse Validator BlockId Payload) (ws wa : ℕ) :
    Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (d : Validator) (s b M : ℕ),
    -- four rounds, a quorum, and the slot below the blocks
    4 ≤ wa → quorumCard Validator ≤ T.card → s < b →
    -- the waves of the M blocks of wa rounds from b are populated where MM2's weaker form reads
    -- them
    (∀ (j : Fin M) (i : Fin wa), PopulatedOn U T (b + j * wa + i + 2) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (b + j * wa + i))) →
    -- then the number of blocks the search waits for, the first good one included and capped at
    -- M, is in expectation at most n^wa, the paper's 1 / p^wa at p = 1 / n ...
    (∑ g : Fin M → Fin wa → Validator, PMF.uniformOfFintype (Fin M → Fin wa → Validator) g *
        ((firstGoodBlock U wa b g + 1 : ℕ) : ℝ≥0∞)) ≤ (Fintype.card Validator : ℝ≥0∞) ^ wa ∧
    -- ... and once a view holds the decision rounds of the first good block, the slot is decided
    -- at period one on the chain schedule of those coins
    (∀ g : Fin M → Fin wa → Validator, firstGoodBlock U wa b g < M →
      V.CoversUpto (MahiMahi.decisionRoundAt wa (b + (firstGoodBlock U wa b g + 1) * wa - 1)) →
      ∃ v, Decided (S := chainSlots (coinOfBlocksFrom b g d)) (wavelength ws wa) U V s v)

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
      ((((Fintype.card Validator ^ K - c ^ K : ℕ) : ℝ≥0∞) /
        (Fintype.card Validator : ℝ≥0∞) ^ K) ^ H.card)

/-- **SH15b, the tail against an adaptive adversary.** -/
def UndecidedTailAgainst (ws wa I K : ℕ) [NeZero K] : Prop :=
  ∀ (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (d : Validator) (q s M : ℕ)
    (σ : (Fin M → Fin (wa * K) → Validator) → BlockUniverse Validator BlockId Payload)
    (G : (Fin M → Fin (wa * K) → Validator) → Fin M → Fin (wa * K) → Finset Validator),
    -- the waves, the period bound and the asynchronous wave within an interval, blocks of
    -- wa · K rounds that end before the next block opens, q intervals up, and a slot at round
    -- one or above
    2 ≤ ws → ws ≤ wa → 5 ≤ wa → K ≤ I → wa ≤ I → wa * K ≤ q * I → 1 ≤ s →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- the adversary builds its record from the coins already drawn, with a floor of committed
    -- candidates at every round of the blocks that the round's own coin cannot shrink ...
    NonAnticipating σ G wa I q (intervalOf I s) →
    -- ... and the floor holds at least n − f − b validators, the counting lemma's share
    (∀ g j i, Fintype.card Validator - F.f - F.byzantine.card ≤ (G g j i).card) →
    -- then the slot stays undecided with the probability SH15a gives against a fixed record
    undecidedProbAgainst ws wa I q σ upd k₀ known d s ≤
      2 * badBlockBound Validator (wa * K) ^ (M / 2)

/-- **SH15c, the tail vanishes.** -/
def UndecidedTailVanishes (K : ℕ) : Prop :=
  Tendsto (fun M : ℕ => 2 * badBlockBound Validator K ^ (M / 2)) atTop (𝓝 0)

/-- **SH15d, the tail at wave four.** SH15a at `4 ≤ wa`, where the counting lemma's weaker form
promises one committed candidate per populated round: the same argument, with the block bound
read at a floor of one. -/
def UndecidedTailFour (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (T : Finset Validator) (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator)
    (d : Validator) (q s M : ℕ),
    -- the waves, a quorum, the period bound and the asynchronous wave within an interval, and
    -- blocks of wa · K rounds that end before the next block opens, q intervals up
    2 ≤ ws → ws ≤ wa → 4 ≤ wa → K ≤ I → wa ≤ I → wa * K ≤ q * I →
    quorumCard Validator ≤ T.card →
    -- the slot lies at round one or above
    1 ≤ s →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- the waves of the M blocks are populated where MM2's weaker form reads them
    (∀ (j : Fin M) (i : Fin (wa * K)), PopulatedOn U T (blockRound I q (intervalOf I s) j i + 2) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (blockRound I q (intervalOf I s) j i))) →
    -- then the slot stays undecided with probability at most twice the chance that each of M/2
    -- blocks names no committed candidate at some round
    undecidedProb U ws wa I q K upd k₀ known d s M ≤
      2 * badBlockBoundOne Validator (wa * K) ^ (M / 2)

/-- **SH15d, the tail at wave four vanishes.** -/
def UndecidedTailFourVanishes (K : ℕ) : Prop :=
  Tendsto (fun M : ℕ => 2 * badBlockBoundOne Validator K ^ (M / 2)) atTop (𝓝 0)

/-- **SH15e, the slot is decided almost surely.** -/
def DecidedAlmostSurely (ws wa I K : ℕ) [NeZero K] : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (U : ℕ → BlockUniverse Validator BlockId Payload) (T : Finset Validator)
    (upd : ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (q s : ℕ),
    -- the waves, a quorum, the period bound and the asynchronous wave within an interval, and
    -- blocks of wa · K rounds that end before the next block opens, q intervals up
    2 ≤ ws → ws ≤ wa → 5 ≤ wa → K ≤ I → wa ≤ I → wa * K ≤ q * I →
    quorumCard Validator ≤ T.card →
    -- the slot lies at round one or above
    1 ≤ s →
    -- the initial period lies in [1, K], and every update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K) →
    -- record m holds the waves of m blocks, populated where MM2 reads them
    (∀ (m : ℕ) (j : Fin m) (i : Fin (wa * K)),
      PopulatedOn (U m) T (blockRound I q (intervalOf I s) j i + 3) ∧
      PopulatedOn (U m) T (MahiMahi.decisionRoundAt wa (blockRound I q (intervalOf I s) j i))) →
    -- then for almost every coin some record decides s in every view holding its horizon, at
    -- every period sequence matching what the view derives
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (U m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K wa coin known (upd m) k₀ ws (U m) V per →
        Settles I K wa coin known (upd m) k₀ ws (U m) V per s

/-- **SH15g, almost surely against an adaptive adversary.** -/
def DecidedAlmostSurelyAgainst (ws wa I K : ℕ) [NeZero K] : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (σ : ∀ m : ℕ, (Fin m → Fin (wa * K) → Validator) → BlockUniverse Validator BlockId Payload)
    (G : ∀ m : ℕ, (Fin m → Fin (wa * K) → Validator) → Fin m → Fin (wa * K) → Finset Validator)
    (upd : ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (q s : ℕ),
    -- the waves, the period bound and the asynchronous wave within an interval, blocks of
    -- wa · K rounds that end before the next block opens, q intervals up, and a slot at round
    -- one or above
    2 ≤ ws → ws ≤ wa → 5 ≤ wa → K ≤ I → wa ≤ I → wa * K ≤ q * I → 1 ≤ s →
    -- the initial period lies in [1, K], and every update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K) →
    -- every strategy of the sequence answers the draws already made, with its floor ...
    (∀ m, NonAnticipating (σ m) (G m) wa I q (intervalOf I s)) →
    -- ... and every floor holds at least n − f − b validators
    (∀ (m : ℕ) (g : Fin m → Fin (wa * K) → Validator) (j : Fin m) (i : Fin (wa * K)),
      Fintype.card Validator - F.f - F.byzantine.card ≤ (G m g j i).card) →
    -- then for almost every coin some strategy's own record decides s in every view holding its
    -- horizon, at every period sequence matching what the view derives
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload
          (σ m (blockCoins I q (intervalOf I s) m (wa * K) coin)))
        (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K wa coin known (upd m) k₀ ws
          (σ m (blockCoins I q (intervalOf I s) m (wa * K) coin)) V per →
        Settles I K wa coin known (upd m) k₀ ws
          (σ m (blockCoins I q (intervalOf I s) m (wa * K) coin)) V per s

/-- **SH15h, every slot is decided almost surely.** -/
def AllDecidedAlmostSurely (ws wa I K : ℕ) [NeZero K] : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (U : ℕ → ℕ → BlockUniverse Validator BlockId Payload) (T : Finset Validator)
    (upd : ℕ → ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (q : ℕ),
    -- the waves, a quorum, the period bound and the asynchronous wave within an interval, and
    -- blocks of wa · K rounds that end before the next block opens, q intervals up
    2 ≤ ws → ws ≤ wa → 5 ≤ wa → K ≤ I → wa ≤ I → wa * K ≤ q * I →
    quorumCard Validator ≤ T.card →
    -- the initial period lies in [1, K], and every update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ s m A k, 1 ≤ k → k ≤ K → 1 ≤ upd s m A k ∧ upd s m A k ≤ K) →
    -- for every slot, record m of the slot's sequence holds the waves of m blocks above the
    -- slot's interval, populated where MM2 reads them
    (∀ (s m : ℕ) (j : Fin m) (i : Fin (wa * K)),
      PopulatedOn (U s m) T (blockRound I q (intervalOf I s) j i + 3) ∧
      PopulatedOn (U s m) T (MahiMahi.decisionRoundAt wa (blockRound I q (intervalOf I s) j i))) →
    -- then for almost every coin, every slot at round one or above is decided by some record of
    -- its sequence, in every view holding that record's horizon
    ∀ᵐ coin ∂(coinMeasure Validator), ∀ s, 1 ≤ s → ∃ m,
      ∀ (V : View Validator BlockId Payload (U s m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K wa coin known (upd s m) k₀ ws (U s m) V per →
        Settles I K wa coin known (upd s m) k₀ ws (U s m) V per s

/-- **SH15f, some interval is anchored almost surely.** Theorem 3 (i)'s "with probability `1`
some scan finds its anchor": SH15e with the anchor in place of the decision. -/
def AnchoredAlmostSurely (ws wa I K : ℕ) [NeZero K] : Prop :=
  ∀ [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    (U : ℕ → BlockUniverse Validator BlockId Payload) (T : Finset Validator)
    (upd : ℕ → UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (q s : ℕ),
    -- the waves, a quorum, the period bound and the asynchronous wave within an interval, and
    -- blocks of wa · K rounds that end before the next block opens, q intervals up
    2 ≤ ws → ws ≤ wa → 5 ≤ wa → K ≤ I → wa ≤ I → wa * K ≤ q * I →
    quorumCard Validator ≤ T.card →
    -- the slot lies at round one or above
    1 ≤ s →
    -- the initial period lies in [1, K], and every update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K) →
    -- record m holds the waves of m blocks, populated where MM2 reads them
    (∀ (m : ℕ) (j : Fin m) (i : Fin (wa * K)),
      PopulatedOn (U m) T (blockRound I q (intervalOf I s) j i + 3) ∧
      PopulatedOn (U m) T (MahiMahi.decisionRoundAt wa (blockRound I q (intervalOf I s) j i))) →
    -- then for almost every coin some record has, in every view holding its horizon and at every
    -- period sequence matching what the view derives, an anchored interval above the slot's
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (U m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K wa coin known (upd m) k₀ ws (U m) V per →
        Anchored I K wa coin known (upd m) k₀ ws (U m) V per s

/-- **SH15i, a matching sequence exists.** -/
def MatchesExists (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin known : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U),
    2 ≤ ws → 3 ≤ wa →
    -- then some period sequence is the one the view derives, at every interval it derives a
    -- state for
    ∃ per, Matches I K wa coin known upd k₀ ws U V per

/-- The coin, over every fault configuration, block universe, asynchronous wave, interval and
positive period bound the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId]
    (U : BlockUniverse Validator BlockId Payload) (ws wa I K : ℕ) [NeZero K],
    CommitProbability U wa ∧ CommitProbabilityFour U wa ∧
      ByzantineLeaderProbability (Validator := Validator) ∧ RunProbability U wa ∧
      CommitOfCoin U wa ∧
      NoCommitTail U wa ∧ TailVanishes (Validator := Validator) ∧
      AdaptiveBlockBound (Validator := Validator) K ∧
      UndecidedTail U ws wa I K ∧
      UndecidedTailAgainst (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
        ws wa I K ∧
      UndecidedTailVanishes (Validator := Validator) (wa * K) ∧
      UndecidedTailFour U ws wa I K ∧
      UndecidedTailFourVanishes (Validator := Validator) (wa * K) ∧
      DecidedAlmostSurely (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
        ws wa I K ∧
      DecidedAlmostSurelyAgainst (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
        ws wa I K ∧
      UndecidedAtPeriodOne U ws wa ∧ ExpectedWaitAtPeriodOne U ws wa ∧
      ExpectedWaitAtPeriodOneFour U ws wa ∧
      NoCommitOnScan U wa ∧ ExpectedIntervalsToAnchor U wa ∧
      AllDecidedAlmostSurely (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
        ws wa I K ∧
      AnchoredAlmostSurely (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
        ws wa I K ∧
      MatchesExists U ws wa I K

end Coin

end Steelhead

end LeanDag
