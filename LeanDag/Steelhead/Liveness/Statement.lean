import LeanDag.Steelhead.Model.Clauses
import LeanDag.Steelhead.Model.Chain
import LeanDag.Steelhead.Model.Wavelength
import LeanDag.Mysticeti.ViewPace
/-!
# Liveness at any lawful rule — statement

The paper's Theorem 2 for any rule of its interface: after GST a reliably
led slot commits, a slot whose leader has no block is skipped, and the
anchor search descends from a commit above to every slot below
(`steelhead.md` §4–6). Every claim here quantifies over an anchored rule
`R` and reads it only through its laws and the clauses of
`Model/Clauses.lean`; the two pairs the paper instantiates are the
instances, the Mysticeti and Mahi-Mahi pair in `MahiMahiPair/Liveness/`
and BlueBottle's in `BlueBottlePair/Liveness/`. Twenty-one claims:

* **SH6a, the direct commit under synchrony composes** — if every rule of
  a family commits a reliably led slot once a reliable quorum has
  synchronised and populated the rounds up to its decision round, so
  does their composite, whose decision round and direct commit at a slot
  are the slot's own rule's. Clause A4 is therefore asked of each rule
  alone;
* **SH6b, everything below a fair run is decided** — the core's L10 at the
  rule: past any slot the schedule offers a run of reliably led slots,
  and once the DAG is covered through the run's decision rounds every
  slot below the run is decided. The run commits by the clause and the
  descent reads the rule's tie-break;
* **SH6c, the skip of a silent leader composes** — SH6a's argument for
  `SkipsSilent`: the composite's direct skip at a slot is the slot's
  rule's, so a family whose rules each skip a leader with no block skips
  it too;
* **SH6e, a reliable slot above the floor decides the slot** — the anchor
  clause as the rule has it: under synchrony a slot is decided once every
  slot from its floor up to some reliably led slot is decided, whatever
  led them. The reliably led slot commits (the clause), so the least
  commit at or above the floor is the anchor, and every slot between,
  decided and not committed, is a skip the search passes over;
* **SH6f, the floor chain decides** — hop from a slot to the first slot
  past its floor that the view does not skip, and again from there; if
  the chain reaches a reliably led landing in `h` hops, the slot it
  started from is decided;
* **SH6g, the round-robin schedule offers a reliable run** — a property
  of the schedule alone: at `leader r = r mod n`, a window of `c`
  consecutive `T`-led rounds recurs once `c · (n − |T|) < n`, and a
  `T`-led round lies within `n − |T|` rounds of any round;
* **SH6h, the floor chain reaches a reliably led landing** — at the
  round-robin schedule and a rule reading one wave `ws` at every slot,
  one of the chain's first `n − |T|` landings is reliably led once
  `ws · (n − |T|) < n`. A reliably led round commits, and a lawful rule
  decides a slot one way, so it is never a skip the hop passes over;
  counting the rounds the hops leave free bounds the landings;
* **SH6i, within `b` hops** — SH6h once every validator outside `T` that
  is not Byzantine has crashed: a crashed leader's slot is skipped
  (`SkipsSilent`), so a landing led from outside `T` is Byzantine-led, and
  the Byzantine validators hold only `b` of the landings' residues;
* **SH6j, the floor chain decides within `(b + 1) · (ws + f)` rounds** —
  SH6f, SH6g and SH6i together: a view holding `(b + 1) · (ws + (n − |T|))`
  rounds above an unskipped slot decides it;
* **SH6l, a reliable leader commits under the timed discipline** — a
  `ViewPace` whose timeout grows at a rate that clears the delay
  synchronises the reliable set, and the clause commits from there;
* **SH6m, a committed landing decides the chain's start** — the descent
  alone: no quorum, no synchrony and no horizon, only the rule's
  tie-break;
* **SH6n, the periodic round robin offers a reliable synchronous round** —
  a property of the schedule alone, SH6g's second half at a period;
* **SH6o, the floor chain reaches a reliably led or committed landing at
  a period** — SH6h at the paper's dial: every asynchronous slot above
  the chain's start is decided (the coin's business), a landing there is
  committed, and the count loses the coin's rounds,
  `ws · (n − |T|) + ws · ⌈n / p⌉ < n` with `ws` the wave the rule reads
  at the synchronous kind;
* **SH6p, the floor chain decides within `(b + 1) · (ws + W)` rounds at a
  period** — SH6j at the dial, `W` the wait for a reliably led
  synchronous round and `wa` the wave the rule reads at the asynchronous
  kind;
* **SH7a, chain liveness** — at any schedule whose rounds strictly
  increase, the coin schedule and every control schedule among them, the
  run form of clause A5 decides every verdict of the asynchronous rule
  below a run, in every view caught up to the horizon: `wa` consecutive
  slots lie at least `wa` rounds apart, which spans the wave;
* **SH7b, the chain under synchrony** — at such a schedule, past any slot
  the schedule names reliable leaders at `wa` consecutive slots, and once
  the DAG is covered through that run's decision rounds every verdict
  below it is settled, the run committing by clause A4;
* **SH7c, one run settles the chain below it** — `wa` consecutive rounds
  whose coins name good candidates settle every chain verdict below the
  first, in any view holding their decision rounds;
* **SH8, the stall** — at a pair and a period `k` at least the
  synchronous wave, if no synchronous candidate is ever directly
  committed or linked and no synchronous slot is directly skipped, then no
  slot at a round `≡ k − 1 (mod k)` is ever decided: an asynchronous
  anchor above such a slot leaves the slot one period up between, which
  is the claim again;
* **SH9a, the drain** — `wa` consecutive committed slots decide every slot
  below them, at one slot per round, once no slot's wave exceeds `wa`;
* **SH9b, at period one every slot is decided** — with every slot of the
  asynchronous kind, the run form of clause A5 at the output schedule
  decides every slot below a run, since at one kind the pair's composite
  decides as its asynchronous rule (SH4);
* **SH9c, the cost of an asynchronous slot** — at a period, an
  asynchronous slot decides `wa − ws` rounds later than a synchronous
  slot would, and the synchronous slot `i` rounds above it at most
  `max(0, wa − ws − i)` rounds before it.

SH6d (partial dissemination) and SH6k (the reactive discipline) read a
rule's votes and certificates, which no clause names, so they are stated
per pair. The wave bounds of the instances (`3 ≤ w κ` at the Mahi-Mahi
pair) are not asked here: a hop of the floor chain clears the slot's
decision round by definition, and the arithmetic reads the rule's own
wave offset.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Liveness

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH6a, the direct commit under synchrony composes.** -/
def CommitsUnderSyncComposes (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ rules : ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct,
    -- every rule of the family commits a reliably led slot under synchrony ...
    (∀ κ, CommitsUnderSync (rules κ) U) →
    -- ... so the composite does
    CommitsUnderSync (compose rules) U

/-- **SH6b, everything below a fair run is decided.** The run is named by the schedule alone,
before any DAG is mentioned, so the horizon cannot cap how far fairness reaches. -/
def AllDecidedBelowOfSynchrony (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) :
    Prop :=
  ∀ (T : Finset Validator) (c : ℕ),
    -- the rule's tie-break has a choice, and it commits a reliably led slot on every DAG
    LeastLinked R → (∀ U, CommitsUnderSync R U) →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- a run of c slots spans eligibility, and past any slot the schedule offers c consecutive
    -- T-led slots
    R.SpansEligible c → FairRunOn T c →
    -- then past any slot k and any round R₀ there is a slot b ...
    ∀ (R₀ k : ℕ), ∃ b, k ≤ b ∧ R₀ ≤ S.slotRound b ∧
      -- ... below which every slot is decided, on any DAG T has synchronised from R₀ and
      -- populated through the run's decision rounds, in any view covering them
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N → (∀ j, j < b + c → R.decisionRound j ≤ N) →
        ∀ i, i < b → ∃ v, R.Decided U V i v

/-- **SH6c, the skip of a silent leader composes.** -/
def SkipsSilentComposes (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ rules : ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct,
    -- every rule of the family skips a slot whose leader has no block ...
    (∀ κ, SkipsSilent (rules κ) U) →
    -- ... so the composite does
    SkipsSilent (compose rules) U

/-- **SH6e, a reliable slot above the floor decides the slot.** -/
def DecidedOfReliableAboveFloor (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R₀ N k a : ℕ),
    -- the rule's tie-break has a choice, and it commits a reliably led slot under synchrony
    LeastLinked R → CommitsUnderSync R U →
    -- one slot per round
    (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R₀ and populates every round from R₀ to the horizon N
    SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) →
    -- the slot lies at or past R₀
    R₀ ≤ k →
    -- slot a lies past k's decision round, read at k's kind, and is reliably led
    k + R.waveAt (S.kind k) + 1 ≤ a → S.leader a ∈ T →
    -- every slot from the floor up to a is decided in V
    (∀ j, k + R.waveAt (S.kind k) + 1 ≤ j → j < a → ∃ v, R.Decided U V j v) →
    -- a decides at or below N, which the view holds
    R.decisionRound a ≤ N → V.CoversUpto N →
    -- then the slot is decided in V
    ∃ v, R.Decided U V k v

/-- **SH6f, the floor chain decides.** -/
def FloorChainDecides (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R₀ N h : ℕ) (x : ℕ → ℕ),
    LeastLinked R → CommitsUnderSync R U →
    -- one slot per round, as Theorem 2 reads the chain
    (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R₀ and populates every round from R₀ to the horizon N
    SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) →
    -- the chain starts at or past R₀ and hops h times, each to the first slot past the
    -- landing's floor that the view does not skip
    R₀ ≤ x 0 → (∀ i, i < h → FloorHopOf R U V (x i) (x (i + 1))) →
    -- its last landing is reliably led and decides at or below N, which the view holds
    S.leader (x h) ∈ T → R.decisionRound (x h) ≤ N → V.CoversUpto N →
    -- then the slot the chain started from is decided
    ∃ v, R.Decided U V (x 0) v

/-- **SH6g, the round-robin schedule offers a reliable run.** -/
def RoundRobinFairRun : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (T : Finset (Fin n)),
    -- past every round the schedule leads c consecutive rounds from T, once the validators
    -- outside T, which spoil at most c windows each, cannot spoil all n windows of a cycle
    (∀ c, c * (n - T.card) < n →
      FairRunOn (S := Slots.identity fun r => (⟨r % n, Nat.mod_lt r hn⟩ : Fin n)) T c) ∧
    -- and at or above every round it leads one within n − |T| rounds
    (T.Nonempty → ∀ r, ∃ a, r ≤ a ∧ a ≤ r + (n - T.card) ∧
      (⟨a % n, Nat.mod_lt a hn⟩ : Fin n) ∈ T)

/-- **SH6h, the floor chain reaches a reliably led landing.** -/
def FloorChainReachesReliable (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R₀ N ws n : ℕ) (hn : 0 < n)
    (lead : Fin n → Validator) (x : ℕ → ℕ),
    -- the rule is lawful and commits a reliably led slot under synchrony
    R.Laws → CommitsUnderSync R U →
    -- it reads one wave at every slot, and there is one slot per round
    (∀ t, R.waveAt (S.kind t) + 1 = ws) → (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R₀ and populates every round from R₀ to the horizon N
    SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    -- the schedule is the implementation's, one validator a round in rotation
    Function.Bijective lead → (∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    -- the validators outside T are few enough for the wave
    ws * (n - T.card) < n →
    -- the chain starts at or past R₀, hops that many times, and decides at or below the horizon
    R₀ ≤ x 0 → (∀ i, i < n - T.card → FloorHopOf R U V (x i) (x (i + 1))) →
    (∀ j, j ≤ x (n - T.card) → R.decisionRound j ≤ N) →
    -- then one of those landings is reliably led, so the chain reaches one within n − |T| hops
    ∃ i, i ≤ n - T.card ∧ S.leader (x i) ∈ T

/-- **SH6i, the floor chain reaches a reliably led landing within `b` hops.** -/
def FloorChainReachesReliableWithinByzantine (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R₀ N ws n : ℕ) (hn : 0 < n)
    (lead : Fin n → Validator) (x : ℕ → ℕ),
    -- the rule is lawful, commits a reliably led slot and skips a silent one
    R.Laws → CommitsUnderSync R U → SkipsSilent R U →
    -- it reads one wave at every slot, and there is one slot per round
    (∀ t, R.waveAt (S.kind t) + 1 = ws) → (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R₀ and populates every round from R₀ to the horizon N
    SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    -- every validator outside T that is not Byzantine has crashed: it has no block from R₀ on
    (∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R₀ ≤ (U.block L).round → (U.block L).creator ≠ v) →
    -- the schedule is the implementation's, one validator a round in rotation
    Function.Bijective lead → (∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    -- the validators outside T are few enough for the wave
    ws * (n - T.card) < n →
    -- the chain starts at or past R₀ at a slot the view does not skip, hops once per Byzantine
    -- validator, and decides at or below the horizon
    R₀ ≤ x 0 → ¬ R.Decided U V (x 0) none →
    (∀ i, i < F.byzantine.card → FloorHopOf R U V (x i) (x (i + 1))) →
    (∀ j, j ≤ x F.byzantine.card → R.decisionRound j ≤ N) →
    -- then one of those landings is reliably led, so the chain reaches one within b hops
    ∃ i, i ≤ F.byzantine.card ∧ S.leader (x i) ∈ T

/-- **SH6j, the floor chain decides within `(b + 1) · (ws + f)` rounds.** -/
def FloorChainDecidesWithinRounds (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R₀ N ws n : ℕ) (hn : 0 < n)
    (lead : Fin n → Validator) (k : ℕ),
    -- the rule is lawful, its tie-break has a choice, and it commits a reliably led slot and
    -- skips a silent one
    R.Laws → LeastLinked R → CommitsUnderSync R U → SkipsSilent R U →
    -- it reads one wave at every slot, and there is one slot per round
    (∀ t, R.waveAt (S.kind t) + 1 = ws) → (∀ t, S.slotRound t = t) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R₀ and populates every round from R₀ to the horizon N
    SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    -- every validator outside T that is not Byzantine has crashed: it has no block from R₀ on
    (∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R₀ ≤ (U.block L).round → (U.block L).creator ≠ v) →
    -- the schedule is the implementation's, one validator a round in rotation
    Function.Bijective lead → (∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    -- the validators outside T are few enough for the wave
    ws * (n - T.card) < n →
    -- the slot lies at or past R₀, the view does not skip it, and the horizon reaches
    -- (b + 1) · (ws + (n − |T|)) rounds above it
    R₀ ≤ k → ¬ R.Decided U V k none →
    k + (F.byzantine.card + 1) * (ws + (n - T.card)) ≤ N →
    -- then the slot is decided
    ∃ v, R.Decided U V k v

/-- **SH6l, a reliable leader commits under the timed discipline.** -/
def CommitsOfViewPace (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (N k : ℕ)
    (vp : ViewPace U T N),
    CommitsUnderSync R U →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the timeout grows at a rate that clears the delay, which is what the core's Q3 asks
    Rated vp.timeout →
    -- the slot lies at or past the round the rate names, and decides below the horizon N'
    ∀ N' : ℕ, max (2 * vp.delay + vp.proc) vp.gst ≤ S.slotRound k →
      (∀ r, max (2 * vp.delay + vp.proc) vp.gst ≤ r → r ≤ N' → PopulatedOn U T r) →
      R.decisionRound k ≤ N' → V.CoversUpto N' → S.leader k ∈ T →
      ∃ L, IsLeaderBlock U k L ∧ R.Decided U V k (some L)

/-- **SH6m, a committed landing decides the chain's start.** -/
def FloorChainDecidesFromCommit (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (h : ℕ) (x : ℕ → ℕ),
    -- the rule's tie-break has a choice
    LeastLinked R →
    -- one slot per round, as Theorem 2 reads the chain
    (∀ t, S.slotRound t = t) →
    -- the chain hops h times and its last landing is committed, whoever led it
    (∀ i, i < h → FloorHopOf R U V (x i) (x (i + 1))) →
    (∃ A, R.Decided U V (x h) (some A)) →
    -- then the slot the chain started from is decided
    ∃ v, R.Decided U V (x 0) v

/-- **SH6n, the periodic round robin offers a reliable synchronous round.** -/
def PeriodicRoundRobinReliableSync : Prop :=
  ∀ (n p : ℕ) (hn : 0 < n) (T : Finset (Fin n)),
    -- the coin's rounds are too few to hide every reliable residue
    0 < p → (n + p - 1) / p < T.card →
    -- past every round the schedule leads a synchronous round from T within n − 1 rounds
    ∀ r, ∃ a, r ≤ a ∧ a ≤ r + (n - 1) ∧ periodicKind p a ≠ 1 ∧
      (⟨a % n, Nat.mod_lt a hn⟩ : Fin n) ∈ T

/-- **SH6o, the floor chain reaches a reliably led or committed landing at a period.** -/
def FloorChainReachesAtPeriod (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R₀ N ws p n : ℕ)
    (hn : 0 < n) (lead : Fin n → Validator) (x : ℕ → ℕ),
    -- the rule is lawful and commits a reliably led slot under synchrony
    R.Laws → CommitsUnderSync R U →
    -- the synchronous kind reads the wave ws, and the period is positive
    R.waveAt 0 + 1 = ws → 0 < p →
    -- one slot per round, of the paper's periodic kind, led by the round robin at the rounds
    -- whose leader is known
    (∀ t, S.slotRound t = t) → (∀ t, S.kind t = periodicKind p t) →
    (∀ t, S.kind t = 0 → S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R₀ and populates every round from R₀ to the horizon N
    SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    Function.Bijective lead →
    -- the validators outside T are few enough for the synchronous wave once the coin's rounds
    -- are deducted: at most `⌈n / p⌉` of every `n` rounds carry one
    ws * (n - T.card) + ws * ((n + p - 1) / p) < n →
    -- every asynchronous slot at or above the chain's start is decided, which is the coin's
    -- business and not the schedule's
    (∀ t, x 0 ≤ t → S.kind t = 1 → ∃ v, R.Decided U V t v) →
    -- the chain starts at or past R₀ at a slot the view does not skip, hops that many times,
    -- and decides at or below the horizon
    R₀ ≤ x 0 → ¬ R.Decided U V (x 0) none →
    (∀ i, i < n - T.card → FloorHopOf R U V (x i) (x (i + 1))) →
    (∀ j, j ≤ x (n - T.card) → R.decisionRound j ≤ N) →
    -- then one of those landings is reliably led, or committed outright
    ∃ i, i ≤ n - T.card ∧ (S.leader (x i) ∈ T ∨ ∃ A, R.Decided U V (x i) (some A))

/-- **SH6p, the floor chain decides within `(b + 1) · (ws + W)` rounds at a period.** -/
def FloorChainDecidesWithinRoundsAtPeriod (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R₀ N ws wa p n W : ℕ)
    (hn : 0 < n) (lead : Fin n → Validator) (k : ℕ),
    -- the rule is lawful, its tie-break has a choice, and it commits a reliably led slot and
    -- skips a silent one
    R.Laws → LeastLinked R → CommitsUnderSync R U → SkipsSilent R U →
    -- the synchronous kind reads the wave ws and the asynchronous one wa, the period positive
    R.waveAt 0 + 1 = ws → R.waveAt 1 + 1 = wa → 0 < p →
    -- one slot per round, of the paper's periodic kind, led by the round robin where known
    (∀ t, S.slotRound t = t) → (∀ t, S.kind t = periodicKind p t) →
    (∀ t, S.kind t = 0 → S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) →
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R₀ and populates every round from R₀ to the horizon N
    SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) → V.CoversUpto N →
    -- every validator outside T that is not Byzantine has crashed: it has no block from R₀ on
    (∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R₀ ≤ (U.block L).round → (U.block L).creator ≠ v) →
    Function.Bijective lead →
    -- the count that bounds the chain, with the coin's rounds deducted
    ws * (n - T.card) + ws * ((n + p - 1) / p) < n →
    -- past every round the schedule leads a synchronous round from T within W rounds
    (∀ r, ∃ a, r ≤ a ∧ a ≤ r + W ∧ S.kind a = 0 ∧ S.leader a ∈ T) →
    -- every asynchronous slot at or above the slot is decided
    (∀ t, k ≤ t → S.kind t = 1 → ∃ v, R.Decided U V t v) →
    -- the slot lies at or past R₀, the view does not skip it, and the horizon reaches
    -- (b + 1) · (ws + W) rounds above it, plus the one asynchronous wave a decision round in
    -- that range may carry
    R₀ ≤ k → ¬ R.Decided U V k none →
    k + (F.byzantine.card + 1) * (ws + W) + wa ≤ N →
    -- then the slot is decided
    ∃ v, R.Decided U V k v

/-- **SH7a, chain liveness.** -/
def ChainAllDecidedBelow (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) : Prop :=
  ∀ (S' : Slots Validator) (V : View Validator BlockId Payload U) (c N wa : ℕ),
    -- the rule's tie-break has a choice, its good sets commit, and no kind's wave reaches wa
    LeastLinked R → GoodCommits R good → (∀ κ, R.waveAt κ + 1 ≤ wa) →
    -- the schedule's rounds strictly increase
    StrictMono S'.slotRound →
    -- the run form of the clause at that schedule, with runs of wa slots
    RunWithin (S := S') R good U c wa N →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- then past every slot k whose window decides below the horizon ...
    ∀ k, S'.slotRound (k + c + wa - 1) + (wa - 1) ≤ N →
      -- ... there is a slot b at or past k below which every verdict is settled
      ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, R.Decided (S := S') U V i v

/-- **SH7b, the chain under synchrony.** The run is named by the schedule alone, so the horizon
cannot cap how far it reaches. -/
def ChainAllDecidedBelowOfSynchrony
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (S' : Slots Validator) (T : Finset Validator) (wa : ℕ),
    -- the rule's tie-break has a choice, it commits a reliably led slot of the schedule on every
    -- DAG, and no kind's wave reaches wa
    LeastLinked R → (∀ U, CommitsUnderSync (S := S') R U) → (∀ κ, R.waveAt κ + 1 ≤ wa) →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- the schedule's rounds strictly increase, and past any slot it names T-leaders at wa
    -- consecutive slots
    StrictMono S'.slotRound → FairRunOn (S := S') T wa →
    -- then past any slot k and any round R₀ there is a slot b ...
    ∀ (R₀ k : ℕ), ∃ b, k ≤ b ∧ R₀ ≤ S'.slotRound b ∧
      -- ... below which every verdict is settled, on any DAG T has synchronised from R₀ and
      -- populated through the run's decision round
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N → S'.slotRound (b + wa - 1) + (wa - 1) ≤ N →
        ∀ i, i < b → ∃ v, R.Decided (S := S') U V i v

/-- **SH7c, one run settles the chain below it.** -/
def ChainAllDecidedBelowOfRun (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) : Prop :=
  ∀ (coin : ℕ → Validator) (V : View Validator BlockId Payload U) (b wa : ℕ),
    LeastLinked R → GoodCommits R good → (∀ κ, R.waveAt κ + 1 ≤ wa) →
    -- wa consecutive rounds from b whose coins name good candidates ...
    (∀ i, i < wa → coin (b + i) ∈ good U (b + i)) →
    -- ... in a view holding their decision rounds
    V.CoversUpto (b + wa - 1 + (wa - 1)) →
    -- then every chain verdict below b is settled
    ∀ i, i < b → ∃ v, ChainDecided R coin U V i v

/-- **SH8, the stall.** -/
def Stall (U : BlockUniverse Validator BlockId Payload) (p : RulePair Validator BlockId Payload) :
    Prop :=
  ∀ (V : View Validator BlockId Payload U) (ws k : ℕ),
    -- the synchronous kind reads the wave ws, of at least two rounds and no longer than the period
    p.sync.waveAt 0 + 1 = ws → 2 ≤ ws → ws ≤ k →
    -- one slot per round, of the kind the period assigns its round
    (∀ s, S.slotRound s = s) → (∀ s, S.kind s = periodicKind k s) →
    -- no synchronous candidate is ever directly committed or linked ...
    (∀ (j : ℕ) (L : BlockId), S.kind j = 0 → IsLeaderBlock U j L →
      (∀ V' : View Validator BlockId Payload U, ¬ p.sync.Commit U V' L j 0) ∧
        ∀ (i : ℕ) (A : BlockId), ¬ p.sync.Link i U A L S j) →
    -- ... and no synchronous slot is directly skipped in V
    (∀ j, S.kind j = 0 → ¬ p.sync.Skip U V S j) →
    -- then no slot at a round ≡ k − 1 (mod k) is ever decided in V
    ∀ i, i % k = k - 1 → ∀ v, ¬ (steelheadAt p).Decided U V i v

/-- **SH9a, the drain.** -/
def AllDecidedBelowOfRun (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (wa : ℕ) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (b : ℕ),
    -- the rule's tie-break has a choice, and no slot's wave exceeds wa
    LeastLinked R → (∀ s, R.waveAt (S.kind s) + 1 ≤ wa) →
    -- one slot per round
    (∀ s, S.slotRound s = s) →
    -- wa consecutive slots from b are committed in V
    (∀ i, i < wa → ∃ L, R.Decided U V (b + i) (some L)) →
    -- then every slot below b is decided in V
    ∀ i, i < b → ∃ v, R.Decided U V i v

/-- **SH9b, at period one every slot is decided.** -/
def AllDecidedBelowAtPeriodOne (U : BlockUniverse Validator BlockId Payload)
    (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (c N wa : ℕ),
    -- the asynchronous rule's tie-break has a choice, its good sets commit, and its wave is wa
    LeastLinked p.async → GoodCommits p.async good → p.async.waveAt 1 + 1 = wa →
    -- one slot per round, every slot of the asynchronous kind, as period one has it
    (∀ s, S.slotRound s = s) → (∀ s, S.kind s = 1) →
    -- the run form of the clause at the output schedule, with runs of wa slots
    RunWithin p.async good U c wa N →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- then past every round r whose window decides below the horizon ...
    ∀ r, r + c + wa - 1 + (wa - 1) ≤ N →
      -- ... there is a slot b at or past r below which every slot is decided at period 1
      ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, (steelheadAt p).Decided U V i v

/-- **SH9c, the cost of an asynchronous slot.** -/
def AsyncSlotCost (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (ws wa k : ℕ) : Prop :=
  -- one slot per round, of the kind the period assigns its round, the synchronous kind reading
  -- the wave ws and the asynchronous one wa, the first no longer than the second
  (∀ s, S.slotRound s = s) → (∀ s, S.kind s = periodicKind k s) →
  R.waveAt 0 + 1 = ws → R.waveAt 1 + 1 = wa → ws ≤ wa →
  ∀ r, S.kind r = 1 →
    -- the asynchronous slot decides wa − ws rounds later than a synchronous slot there would ...
    R.decisionRound r = r + (ws - 1) + (wa - ws) ∧
    -- ... and the synchronous slot i rounds above it is decided at most max(0, wa − ws − i)
    -- rounds before it, so waits that long for it and no longer; the bound is nonincreasing in i
    ∀ i, 1 ≤ i → i < k → R.decisionRound r ≤ R.decisionRound (r + i) + (wa - ws - i)

/-- Liveness at any rule, over every fault configuration, schedule, block universe, anchored
rule, pair of rules, good set, wave and period the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) (ws wa k : ℕ),
    CommitsUnderSyncComposes U ∧ AllDecidedBelowOfSynchrony R ∧ SkipsSilentComposes U ∧
      DecidedOfReliableAboveFloor U R ∧ FloorChainDecides U R ∧ RoundRobinFairRun ∧
      FloorChainReachesReliable U R ∧ FloorChainReachesReliableWithinByzantine U R ∧
      FloorChainDecidesWithinRounds U R ∧ CommitsOfViewPace U R ∧
      FloorChainDecidesFromCommit U R ∧ PeriodicRoundRobinReliableSync ∧
      FloorChainReachesAtPeriod U R ∧ FloorChainDecidesWithinRoundsAtPeriod U R ∧
      ChainAllDecidedBelow U R good ∧ ChainAllDecidedBelowOfSynchrony R ∧
      ChainAllDecidedBelowOfRun U R good ∧ Stall U p ∧
      AllDecidedBelowOfRun U R wa ∧ AllDecidedBelowAtPeriodOne U p good ∧ AsyncSlotCost R ws wa k

end Liveness

end Steelhead

end LeanDag
