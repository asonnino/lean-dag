import LeanDag.Steelhead.Model.Period
import LeanDag.MahiMahi.Model.Good
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProductMeasure
/-!
# Steelhead — the coin

The coin of an asynchronous round, modelled as a distribution rather
than by its effect (`steelhead.md` §4): uniform over the validators,
and independent across rounds, which is the uniform distribution over
the leader maps of `m` rounds. Events on finitely many rounds are read
through `PMF.toOuterMeasure`, so no measurable structure on the
validators is assumed; the coin as a process over every round
(`coinMeasure`) is the infinite product of the uniform distribution, on
whatever discrete measurable structure the validators carry. The chain
slot of round `r` commits directly exactly when the coin lands in
`goodAt U wa r`, the validators whose round-`r` block the DAG directly
commits; the quantities below are the probabilities the counting lemma
bounds in `Coin/Statement.lean`: of one good coin, of `m` bad ones in a
row, of a slot below `M` consecutive blocks of `wa` coins staying
undecided at period one, and of a slot of the adaptive output staying
undecided over the coins of `M` blocks of `wa · K` rounds, one block
opening every `q`-th interval from the second after the slot's, the
first whose anchor's window lies wholly above the slot, with `q` large
enough that a block ends before the next opens. A block of `wa · K`
rounds holds `wa` consecutive multiples of `K`, the control slots every
scan below it reads above its boundary, and its first `K` rounds hold
the first control round of the interval it opens at every period up to
`K`.

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- The fault model has at least one validator, which a uniform coin needs. Scoped to the arc: it
is a fact about `Faults` rather than a Steelhead notion, and a global instance would install it
library-wide from here. -/
scoped instance nonempty_of_faults : Nonempty Validator :=
  Fintype.card_pos_iff.mp (by have := F.card_validators; omega)

/-- **The probability that the coin of round `r` names a committed leader**: the measure of
`goodAt U wa r` under the uniform coin. -/
noncomputable def commitProb (U : BlockUniverse Validator BlockId Payload) (wa r : ℕ) : ℝ≥0∞ :=
  (PMF.uniformOfFintype Validator).toOuterMeasure ↑(MahiMahi.goodAt U wa r)

/-- **The probability that every coin of the `m` rounds from `r₀` names a committed leader**, the
coins independent: the measure, under the uniform distribution over the leader maps, of the maps
that hit every round's committed set. The run of consecutive commits a wave asks for. -/
noncomputable def runProb (U : BlockUniverse Validator BlockId Payload) (wa r₀ m : ℕ) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure
    {coins | ∀ i : Fin m, coins i ∈ MahiMahi.goodAt U wa (r₀ + i)}

/-- **The probability that no coin of the `m` rounds from `r₀` names a committed leader**, the
coins independent: the measure, under the uniform distribution over the leader maps, of the maps
that miss every round's committed set. -/
noncomputable def noCommitProb (U : BlockUniverse Validator BlockId Payload) (wa r₀ m : ℕ) :
    ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin m → Validator)).toOuterMeasure
    {coins | ∀ i : Fin m, coins i ∉ MahiMahi.goodAt U wa (r₀ + i)}

/-- **The coins of `K` rounds read as a coin map**: round `r` below `K` draws `g r`, every round
at or above `K` the fixed `d`, which no event below reads. -/
def coinOfRounds {K : ℕ} (g : Fin K → Validator) (d : Validator) : ℕ → Validator :=
  fun r => if h : r < K then g ⟨r, h⟩ else d

/-- **The coins of `M` blocks of `K` rounds from round `b`**, read as a coin map: round
`b + j·K + i` draws `g j i`, and every round outside the blocks draws `d`, which no event below
reads. The consecutive blocks over which the search's tail is measured (SH11i). -/
def coinOfBlocksFrom {M K : ℕ} (b : ℕ) (g : Fin M → Fin K → Validator) (d : Validator) :
    ℕ → Validator :=
  fun r =>
    if h : b ≤ r ∧ (r - b) / K < M ∧ (r - b) % K < K then
      g ⟨(r - b) / K, h.2.1⟩ ⟨(r - b) % K, h.2.2⟩
    else d

/-- **The good blocks** of `M` blocks of `wa` coins from round `b`, drawn as `g`: those whose
every coin names a directly committed leader of its round, so that the block is a run of `wa`
direct commits at period one. -/
noncomputable def goodBlocks (U : BlockUniverse Validator BlockId Payload) (wa b : ℕ) {M : ℕ}
    (g : Fin M → Fin wa → Validator) : Finset (Fin M) :=
  open Classical in
  Finset.univ.filter fun j => ∀ i : Fin wa, g j i ∈ MahiMahi.goodAt U wa (b + j * wa + i)

/-- **The first good block**, or `M` when none of the `M` blocks is good: the search at period
one waits for `firstGoodBlock … g + 1` blocks of `wa` rounds, the good one included, and decides
the slot below them by the drain (SH11i). -/
noncomputable def firstGoodBlock (U : BlockUniverse Validator BlockId Payload) (wa b : ℕ)
    {M : ℕ} (g : Fin M → Fin wa → Validator) : ℕ :=
  open Classical in
  if h : (goodBlocks U wa b g).Nonempty then ((goodBlocks U wa b g).min' h : ℕ) else M

/-- **The probability that no control slot of a scan names a committed leader**, the coins
independent: the measure, under the uniform distribution over the leader maps, of the maps that
miss the committed set at every one of the scan's slots. The scan's rounds are given as a
schedule `ρ` rather than a stretch, since control slots sit at multiples of the period. -/
noncomputable def noCommitProbOn (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) {c : ℕ}
    (ρ : Fin c → ℕ) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin c → Validator)).toOuterMeasure
    {coins | ∀ i : Fin c, coins i ∉ MahiMahi.goodAt U wa (ρ i)}

/-- **The intervals whose scan finds an anchor** among `M` scans of `c` control slots each, the
slots at the rounds `ρ j i` and the coins drawn as `g`: those at one of whose slots the coin names
a directly committed leader. An interval retains its period when all of its control slots are
skipped, so these are the scans that can hand the next interval a period. -/
noncomputable def goodIntervals (U : BlockUniverse Validator BlockId Payload) (wa : ℕ) {M c : ℕ}
    (ρ : Fin M → Fin c → ℕ) (g : Fin M → Fin c → Validator) : Finset (Fin M) :=
  open Classical in
  Finset.univ.filter fun j => ∃ i : Fin c, g j i ∈ MahiMahi.goodAt U wa (ρ j i)

/-- **The first interval whose scan finds an anchor**, or `M` when none of the `M` does: a scan
waits for `firstGoodInterval … g + 1` intervals, the one that anchors included. -/
noncomputable def firstGoodInterval (U : BlockUniverse Validator BlockId Payload) (wa : ℕ)
    {M c : ℕ} (ρ : Fin M → Fin c → ℕ) (g : Fin M → Fin c → Validator) : ℕ :=
  open Classical in
  if h : (goodIntervals U wa ρ g).Nonempty then ((goodIntervals U wa ρ g).min' h : ℕ) else M

/-- **Round `i` of block `j`**: block `j` opens interval `j₀ + 2 + q · j`, so its round `i` is the
`(i + 1)`-th round of that interval. The blocks start two intervals past `j₀`, so that the window
of an anchor in any of them lies wholly above interval `j₀`, and open every `q`-th interval, so
that a block of `wa · K` rounds ends before the next one opens once `wa · K ≤ q · I`. -/
def blockRound (I q j₀ j i : ℕ) : ℕ := (j₀ + 2 + q * j) * I + 1 + i

/-- **The coins of `M` blocks of `K` rounds**, block `j` opening interval `j₀ + 2 + q · j`, read as
a coin map: round `i` of block `j` draws `g j i`, and every other round draws `d`, which no event
below reads. At `K ≤ q · I` the blocks are disjoint and the map reads them back exactly. -/
def coinOfBlocks {M K : ℕ} (I q j₀ : ℕ) (g : Fin M → Fin K → Validator) (d : Validator) :
    ℕ → Validator :=
  fun r =>
    if h : (j₀ + 2) * I + 1 ≤ r ∧ (r - ((j₀ + 2) * I + 1)) / (q * I) < M ∧
        (r - ((j₀ + 2) * I + 1)) % (q * I) < K then
      g ⟨(r - ((j₀ + 2) * I + 1)) / (q * I), h.2.1⟩ ⟨(r - ((j₀ + 2) * I + 1)) % (q * I), h.2.2⟩
    else d

/-- **The coins of `M` blocks of `K` rounds**, read from a coin map: the inverse of
`coinOfBlocks` on the blocks' own rounds. -/
def blockCoins (I q j₀ M K : ℕ) (coin : ℕ → Validator) : Fin M → Fin K → Validator :=
  fun j i => coin (blockRound I q j₀ j i)

/-- **The horizon the blocks need**: the decision round of the last block's last round, the
blocks being `wa · K` rounds long and the last one opening interval `j₀ + 2 + q · (M − 1)`. -/
def blocksHorizon (I q wa K j₀ M : ℕ) : ℕ :=
  MahiMahi.decisionRoundAt wa ((j₀ + 2 + q * (M - 1)) * I + wa * K)

/-- **A period sequence matches what a view derives**: at every interval the view derives a state
for, reading its agreed output on the schedule the sequence names, whose kinds are the
sequence's own, the sequence's period is the state's. Arbitrary where the scan has stalled. -/
def Matches (I K wa : ℕ) [NeZero K] (coin known : ℕ → Validator) (upd : UpdateRule BlockId)
    (k₀ ws : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) : Prop :=
  ∀ j st, PeriodAt (S := adaptiveSlots coin known I per) I K
      (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa) coin upd k₀ U V
    (steelheadAnchored Validator BlockId Payload (wavelength ws wa)) j st → per j = st.period

/-- **A view settles a slot at a matching sequence**: it derives the state of the slot's interval,
and decides the slot on the sequence's schedule. -/
def Settles (I K wa : ℕ) [NeZero K] (coin known : ℕ → Validator) (upd : UpdateRule BlockId)
    (k₀ ws : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s : ℕ) : Prop :=
  (∃ st, PeriodAt (S := adaptiveSlots coin known I per) I K
      (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa) coin upd k₀ U V
    (steelheadAnchored Validator BlockId Payload (wavelength ws wa)) (intervalOf I s) st) ∧
  ∃ v, Decided (S := adaptiveSlots coin known I per) (wavelength ws wa) U V s v

/-- **A view has anchored an interval above a slot's**, at a matching sequence: some interval past
the slot's has a derived state and, at its period, an anchor. The event Theorem 3 (i) names when
it says that some scan finds its anchor. -/
def Anchored (I K wa : ℕ) [NeZero K] (coin known : ℕ → Validator) (upd : UpdateRule BlockId)
    (k₀ ws : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s : ℕ) : Prop :=
  ∃ j st i A, intervalOf I s < j ∧
    PeriodAt (S := adaptiveSlots coin known I per) I K
        (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa) coin upd k₀ U V
        (steelheadAnchored Validator BlockId Payload (wavelength ws wa)) j st ∧
    IntervalAnchor I K (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa) coin U V j st.period
        i A

/-- **The probability that slot `s` stays undecided**, over the uniform independent coins of `M`
blocks of `wa · K` rounds opening every `q`-th interval from the second after the slot's: the
measure of the coin maps under which some view holding the horizon, at some period sequence
matching what it derives, either has not derived the state of the slot's interval or leaves `s`
undecided at that sequence's wavelength and schedule. A sequence matching what the view derives
is arbitrary where the scan has stalled, so a slot that counts as decided is decided under every
such completion, from derived periods alone, and a scan that never reaches the slot's interval
counts as a failure. The coins outside the blocks draw `d`. -/
noncomputable def undecidedProb (U : BlockUniverse Validator BlockId Payload) (ws wa I q K : ℕ)
    [NeZero K] (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (d : Validator)
    (s M : ℕ) : ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin M → Fin (wa * K) → Validator)).toOuterMeasure
    {g | ¬ ∀ (V : View Validator BlockId Payload U) (per : ℕ → ℕ),
      V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) M) →
      Matches I K wa (coinOfBlocks I q (intervalOf I s) g d) known upd k₀ ws U V per →
      Settles I K wa (coinOfBlocks I q (intervalOf I s) g d) known upd k₀ ws U V per s}

/-- **A non-anticipating strategy, with the floor `G`**: a record built from the coins of `M`
blocks of `K` rounds, and at every round of a block a set of candidates the record commits
directly, fixed by the coins drawn before that round, those of the blocks below and of the
block's own earlier rounds. The adversary may shape the whole DAG from the draws already
revealed, and may commit more candidates once a round's coin is out, as Byzantine certifiers
that learn it from the honest shares can; what it may not do is take a candidate out of the
floor after the draw. The claims below read the floor's size and nothing else of the record, so
what "the adversary does not see the coin before it is used" means on a DAG is a floor of the
counting lemma's size that the coin cannot shrink. -/
def NonAnticipating {M K : ℕ}
    (σ : (Fin M → Fin K → Validator) → BlockUniverse Validator BlockId Payload)
    (G : (Fin M → Fin K → Validator) → Fin M → Fin K → Finset Validator) (wa I q j₀ : ℕ) :
    Prop :=
  (∀ g (j : Fin M) (i : Fin K), G g j i ⊆ MahiMahi.goodAt (σ g) wa (blockRound I q j₀ j i)) ∧
    ∀ g g' (j : Fin M) (i : Fin K), (∀ j' : Fin M, j' < j → g j' = g' j') →
      (∀ i' : Fin K, i' < i → g j i' = g' j i') → G g j i = G g' j i

/-- **The probability that slot `s` stays undecided against a strategy**: `undecidedProb` with
the record the adversary builds from the coins in place of a fixed one. The event reads the
strategy's own record at each block map, so the blocks' committed sets move with the draw. -/
noncomputable def undecidedProbAgainst (ws wa I q : ℕ) {M K : ℕ} [NeZero K]
    (σ : (Fin M → Fin (wa * K) → Validator) → BlockUniverse Validator BlockId Payload)
    (upd : UpdateRule BlockId) (k₀ : ℕ) (known : ℕ → Validator) (d : Validator) (s : ℕ) :
    ℝ≥0∞ :=
  (PMF.uniformOfFintype (Fin M → Fin (wa * K) → Validator)).toOuterMeasure
    {g | ¬ ∀ (V : View Validator BlockId Payload (σ g)) (per : ℕ → ℕ),
      V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) M) →
      Matches I K wa (coinOfBlocks I q (intervalOf I s) g d) known upd k₀ ws (σ g) V per →
      Settles I K wa (coinOfBlocks I q (intervalOf I s) g d) known upd k₀ ws (σ g) V per s}

/-- **The coin as a process**: an independent uniform draw at every round, the infinite product
of the uniform distribution over the validators on the measurable structure they carry. The
measure the almost-sure claim (SH15e) reads its events through; on finitely many rounds it agrees
with the uniform distribution over the leader maps of those rounds. -/
noncomputable def coinMeasure (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [MeasurableSpace Validator] : MeasureTheory.Measure (ℕ → Validator) :=
  MeasureTheory.Measure.infinitePi fun _ : ℕ => (PMF.uniformOfFintype Validator).toMeasure

end Steelhead

end LeanDag
