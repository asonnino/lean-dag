import LeanDag.Steelhead.Model.Period
import LeanDag.Steelhead.Model.Clauses
/-!
# The period sequence at any rules — statement

What the adaptive protocol's period does across views and over time
(`steelhead.md` §5), at any rule `Ra` the control verdicts are read by and
any rule `R` the agreed output is read by; the output's liveness at any
pair of rules, `Ra` the pair's asynchronous rule and `R` its composite
(`steelheadAt`). The rules enter through the anchored relation's laws and
the clauses of `Model/Clauses.lean` only, so that each claim holds at both
pairs the paper instantiates; `MahiMahiPair/Period/Statement.lean` states
them at the Mysticeti and Mahi-Mahi pair. Twenty claims:

* **SH10a, agreement of the period** — Theorem 4: two views that derive
  a state for interval `j` derive the same one, period, agreed output
  and last commit alike, under any update rule and any output rule, once
  the control rule is lawful. Induction on the interval: the periods
  agree, so the scans read one control schedule, whose verdicts agree
  (SH10l), so the anchors agree, and the next state is a function of the
  anchor's history;
* **SH10b, agreement of the output under the adaptive kinds** — the
  consequence the paper draws: two validators running a lawful output
  rule at their own derived period sequences, each on the schedule its
  own sequence names (`adaptiveSlots`), derive the same sequence and
  never disagree on a slot, below a round the record does not reach past.
  The output rule's verdicts must be witnessed in their views, so that
  the state of an interval reads the sequence below that interval only;
* **SH10c, the scan ends** — once every control slot of an interval, at
  the interval's period, has a verdict in a view, that view derives the
  next interval's state, the output rule's verdicts witnessed in their
  views, so that some slot above the anchor is undecided in its history;
* **SH10d, the period advances under the clause** — Theorem 3 (i): under
  the run form of clause A5 at every control schedule the period can
  name, a view caught up to the horizon derives a state for every
  interval whose control slots lie far enough below it, by SH7a at the
  interval's own schedule and SH10c;
* **SH10e, the failover**: Theorem 3 (i)'s last clause: an interval that
  finds an anchor below which the agreed output committed nothing within
  `I` rounds hands the next interval period `1`;
* **SH10f, two asynchronous rounds per interval**: at any period `k ≥ 1`
  with `2 k ≤ I`, every interval holds two asynchronous rounds;
* **SH10g, the period stays in range**: if the initial period lies in
  `[1, K]` and the update rule keeps a period there, so does every
  derived period;
* **SH10h, the agreed output is a prefix of the output**: every slot the
  agreed output consumed is decided in the view that derived it, the
  control rule's commits witnessed in their views and the output rule's
  monotone in the view;
* **SH10i, the output stalls below an undecided slot**: a slot the view
  leaves undecided is never consumed, so the agreed output's cursor and
  last commit stay at or below it;
* **SH10j, a window resolves an asynchronous slot of every candidate**:
  at `I ≥ K + wa − 2`, the window of an anchor above round `I` holds, for
  every period in `[1, K]`, an asynchronous round whose decision round it
  retains;
* **SH10k, the control schedule enumerates the control rounds**;
* **SH10l, control verdicts agree per scan**: SH2 at one scan's
  schedule, the control rule lawful;
* **SH10m, the first interval keeps its period**: at an anchor of
  interval `0` the next interval runs at the initial period;
* **SH10n, every window holds two asynchronous rounds** at `I ≥ 2k`;
* **SH10o, the period stays a divisor of the bound**;
* **SH10p, the control slots carry a coin**: at a period sequence whose
  every period divides `K`, every control slot of a scan in its interval
  or above it is an asynchronous round of the adaptive schedule, led by
  the coin;
* **SH10q, the gating rule**: a state for interval `j + 1` carries a
  state for interval `j` whose scan has ended;
* **SH14a, output liveness under the failover**: Theorem 3 (ii) at a
  pair. With the coin leading every round the derived period makes
  asynchronous, if some interval at least two past a slot's finds an
  anchor under the period the view derived for it and above that
  interval the coin names a good validator at `wa` consecutive rounds,
  the slot is decided once the view holds the run's decision rounds;
* **SH14b, every slot is decided under the clause**: SH14a with its two
  events read off clause A5 at every control schedule the period can
  name;
* **SH14c, output liveness from a good coin and a good run**: SH14a with
  its two events named by the coin alone.

The rule hypotheses: SH10a and SH10l ask the control rule's laws; SH10b
both rules' laws and the output rule's `ViewLaws`; SH10c the output
rule's `ViewLaws`; SH10d the control rule's tie-break choice, its good set
committing (`GoodCommits`) and its wave below `wa`, and SH10c's; SH10h and
SH10i the control rule's `CommitLaws` and the output rule's laws; SH14a
to SH14c both rules' laws and tie-break choices, the asynchronous rule's
`CommitLaws` and good set, and the synchronous wave at most the
asynchronous one, `wa` the asynchronous wave's length. SH10e, SH10g,
SH10m, SH10o and SH10q ask nothing of either rule, and SH10f, SH10j,
SH10k, SH10n and SH10p read no rule. The remaining hypotheses are the
Mahi-Mahi pair's (`MahiMahiPair/Period/Statement.lean`).

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Period

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH10a, agreement of the period.** -/
def PeriodAgreement (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V₁ V₂ : View Validator BlockId Payload U) (j : ℕ) (st₁ st₂ : ScanState),
    -- the control rule is lawful
    Ra.Laws →
    PeriodAt I K Ra coin upd k₀ U V₁ R j st₁ → PeriodAt I K Ra coin upd k₀ U V₂ R j st₂ →
    st₁ = st₂

/-- **SH10b, agreement of the output under the adaptive kinds.** -/
def AdaptiveAgreement (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin known : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ N : ℕ)
    (V₁ V₂ : View Validator BlockId Payload U) (per₁ per₂ : ℕ → ℕ) (k : ℕ)
    (v₁ v₂ : Option BlockId),
    -- both rules are lawful, and the output rule's verdicts are witnessed in their views
    Ra.Laws → R.Laws → ViewLaws R →
    -- the record reaches no higher than round N, and the slot is proposed at or below it
    (∀ b ∈ U.ids, (U.block b).round ≤ N) → k ≤ N →
    -- each view derived the state of every interval those rounds fall in, reading its agreed
    -- output on its own adaptive schedule
    (∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt (S := adaptiveSlots coin known I per₁) I K Ra coin upd k₀ U V₁ R j st ∧
        per₁ j = st.period) →
    (∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt (S := adaptiveSlots coin known I per₂) I K Ra coin upd k₀ U V₂ R j st ∧
        per₂ j = st.period) →
    -- and decided slot k on its own adaptive schedule
    R.Decided (S := adaptiveSlots coin known I per₁) U V₁ k v₁ →
    R.Decided (S := adaptiveSlots coin known I per₂) U V₂ k v₂ →
    -- then the two derived sequences agree on those intervals, and so do the verdicts
    (∀ j, j ≤ intervalOf I N → per₁ j = per₂ j) ∧ v₁ = v₂

/-- **SH10c, the scan ends.** -/
def ScanEnds (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (j : ℕ) (st : ScanState),
    -- the output rule's verdicts are witnessed in their views
    ViewLaws R →
    PeriodAt I K Ra coin upd k₀ U V R j st →
    -- every scanned control slot of the interval, at the interval's period, has a verdict in V
    (∀ i, 1 ≤ controlRound I K j st.period i → intervalOf I (controlRound I K j st.period i) = j →
      ∃ v, ControlDecided I K Ra coin j st.period U V i v) →
    -- then V derives the next interval's state
    ∃ st', PeriodAt I K Ra coin upd k₀ U V R (j + 1) st'

/-- **SH10d, the period advances under the clause.** -/
def PeriodOfClause (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) (I K wa : ℕ)
    [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (c N : ℕ),
    -- the control rule has a tie-break choice, its good set commits, and a run of wa control
    -- slots spans its wave; the output rule's verdicts are witnessed in their views
    LeastLinked Ra → GoodCommits Ra good → Ra.waveAt 1 + 1 ≤ wa → ViewLaws R →
    -- a positive interval
    0 < I →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- the run form of the clause at every control schedule a period in range names: in every
    -- window of c control slots below the horizon, wa consecutive ones whose coins are good
    (∀ j k, 1 ≤ k → k ≤ K → RunWithin (S := controlSlots coin I K j k) Ra good U c wa N) →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- for every interval whose control slots, and the window above them, decide below the
    -- horizon ...
    ∀ j, (j + 1) * I + (c + wa) * K + (wa - 1) ≤ N →
      -- ... the view derives the next interval's state
      ∃ st, PeriodAt I K Ra coin upd k₀ U V R (j + 1) st

/-- **SH10e, the failover.** -/
def PeriodOne (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (j i next' last' : ℕ) (st : ScanState)
    (A : BlockId) (hA : A ∈ U.ids),
    -- interval j runs at st, V finds it an anchor at control slot i, and the agreed output
    -- advanced over the anchor's history committed nothing within I rounds below the anchor ...
    PeriodAt I K Ra coin upd k₀ U V R j st → IntervalAnchor I K Ra coin U V j st.period i A →
    AgreedAdvance U R A hA st.next next' st.lastCommit last' →
    last' + I < controlRound I K j st.period i →
    -- ... then interval j + 1 runs at period 1
    PeriodAt I K Ra coin upd k₀ U V R (j + 1) ⟨1, next', last'⟩

/-- **SH10f, every interval holds two asynchronous rounds.** -/
def TwoAsyncRounds (I : ℕ) : Prop :=
  ∀ j k, 1 ≤ k → 2 * k ≤ I →
    ∃ r₁ r₂, r₁ < r₂ ∧ intervalOf I r₁ = j ∧ IsAsync k r₁ ∧ intervalOf I r₂ = j ∧ IsAsync k r₂

/-- **SH10g, the period stays in range.** -/
def PeriodInRange (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (j : ℕ) (st : ScanState),
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K →
    (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- then so does every derived period
    PeriodAt I K Ra coin upd k₀ U V R j st → 1 ≤ st.period ∧ st.period ≤ K

/-- **SH10h, the agreed output is a prefix of the output.** -/
def AgreedPrefix (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (j : ℕ) (st : ScanState),
    -- the control rule's commits are witnessed in their views, and the output rule is lawful
    CommitLaws Ra → R.Laws →
    PeriodAt I K Ra coin upd k₀ U V R j st →
    -- every slot the agreed output consumed is decided in V
    ∀ s, 1 ≤ s → s < st.next → ∃ v, R.Decided U V s v

/-- **SH10i, the output stalls below an undecided slot.** -/
def StalledBelowUndecided (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (j s : ℕ) (st : ScanState),
    -- the control rule's commits are witnessed in their views, and the output rule is lawful
    CommitLaws Ra → R.Laws →
    -- one slot per round
    (∀ t, S.slotRound t = t) →
    PeriodAt I K Ra coin upd k₀ U V R j st →
    -- a slot at round one or above that V leaves undecided ...
    1 ≤ s → (∀ v, ¬ R.Decided U V s v) →
    -- ... is never consumed, and the last commit lies at or below it
    st.next ≤ s ∧ st.lastCommit ≤ s

/-- **SH10j, a window resolves an asynchronous slot of every candidate.** -/
def WindowResolves (I wa K : ℕ) : Prop :=
  ∀ k top, 1 ≤ k → k ≤ K → 1 ≤ wa → K + wa - 2 ≤ I →
    -- the anchor lies above round I, so its window holds the full I + 1 rounds
    I < top →
    -- then the window, from max 1 (top − I) to top as `windowBottom` has it, holds an
    -- asynchronous round of period k whose decision round it retains
    ∃ r, max 1 (top - I) ≤ r ∧ r + wa - 1 ≤ top ∧ IsAsync k r

/-- **SH10k, the control schedule enumerates the control rounds.** -/
def ControlRounds (I K : ℕ) : Prop :=
  ∀ j k r, (∃ i, controlRound I K j k i = r) ↔
    (r ≤ (j + 1) * I ∧ r % k = 0) ∨ ((j + 1) * I < r ∧ r % K = 0)

/-- **SH10l, control verdicts agree per scan.** -/
def ControlAgreement (U : BlockUniverse Validator BlockId Payload)
    (Ra : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (j k : ℕ) (V₁ V₂ : View Validator BlockId Payload U) (i : ℕ)
    (v₁ v₂ : Option BlockId),
    -- the control rule is lawful
    Ra.Laws →
    ControlDecided I K Ra coin j k U V₁ i v₁ → ControlDecided I K Ra coin j k U V₂ i v₂ →
    v₁ = v₂

/-- **SH10m, the first interval keeps its period.** -/
def WarmUp (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (i next' last' : ℕ) (st : ScanState)
    (A : BlockId) (hA : A ∈ U.ids),
    -- the interval is positive, interval 0 runs at st, V finds it an anchor at control slot i, and
    -- the agreed output advances over the anchor's history ...
    0 < I →
    PeriodAt I K Ra coin upd k₀ U V R 0 st → IntervalAnchor I K Ra coin U V 0 st.period i A →
    AgreedAdvance U R A hA st.next next' st.lastCommit last' →
    -- ... then interval 1 runs at the same period, the output advanced
    PeriodAt I K Ra coin upd k₀ U V R 1 ⟨st.period, next', last'⟩

/-- **SH10n, every window holds two asynchronous rounds.** -/
def TwoAsyncRoundsInWindow (I : ℕ) : Prop :=
  ∀ k top, 1 ≤ k → 2 * k ≤ I →
    -- the anchor lies at round I or above, so its window holds I rounds or more
    I ≤ top →
    -- then the window, from max 1 (top − I) to top as `windowBottom` has it, holds two
    -- asynchronous rounds of period k
    ∃ r₁ r₂, r₁ < r₂ ∧ max 1 (top - I) ≤ r₁ ∧ r₂ ≤ top ∧ IsAsync k r₁ ∧ IsAsync k r₂

/-- **SH10o, the period stays a divisor of the bound.** -/
def PeriodDvd (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (j : ℕ) (st : ScanState),
    -- the initial period divides K, and the update rule keeps a period a divisor of K
    k₀ ∣ K → (∀ A k, k ∣ K → upd A k ∣ K) →
    -- then so does every derived period
    PeriodAt I K Ra coin upd k₀ U V R j st → st.period ∣ K

/-- **SH10p, the control slots carry a coin.** -/
def ControlSlotsAsync (I K : ℕ) [NeZero K] : Prop :=
  ∀ (coin known : ℕ → Validator) (per : ℕ → ℕ) (j i : ℕ),
    -- a positive interval, and every period the sequence names divides the bound
    0 < I → (∀ j', per j' ∣ K) →
    -- a control slot of the scan of interval j, at the interval's period, that lies in the
    -- interval or above it ...
    j ≤ intervalOf I (controlRound I K j (per j) i) →
    -- ... is an asynchronous round of the adaptive schedule, led by the coin
    (adaptiveSlots coin known I per).kind (controlRound I K j (per j) i) = 1 ∧
      (adaptiveSlots coin known I per).leader (controlRound I K j (per j) i) =
        coin (controlRound I K j (per j) i)

/-- **SH10q, an interval is evaluated only once the preceding scan has ended.** -/
def GatedByScan (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (j : ℕ) (st' : ScanState),
    -- a state derived for interval j + 1 ...
    PeriodAt I K Ra coin upd k₀ U V R (j + 1) st' →
    -- ... carries a state for interval j, and the scan of j at that state's period has ended,
    -- with an anchor or with none
    ∃ st, PeriodAt I K Ra coin upd k₀ U V R j st ∧
      ((∃ i A, IntervalAnchor I K Ra coin U V j st.period i A) ∨
        NoAnchor I K Ra coin U V j st.period)

/-- **SH14a, output liveness under the failover.** -/
def OutputLiveness (U : BlockUniverse Validator BlockId Payload)
    (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) (wa I K : ℕ)
    [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s j₁ i₁ b : ℕ) (A : BlockId),
    -- both rules are lawful and have a tie-break choice, the asynchronous rule's commits are
    -- witnessed in their views and its good set commits
    p.sync.Laws → p.async.Laws → LeastLinked p.sync → LeastLinked p.async → CommitLaws p.async →
    GoodCommits p.async good →
    -- the synchronous wave is no longer than the asynchronous one, whose length is wa
    p.sync.waveAt 0 ≤ p.async.waveAt 1 → p.async.waveAt 1 + 1 = wa →
    -- one slot per round, of the kind the derived period assigns it, and a positive interval
    (∀ t, S.slotRound t = t) → (∀ t, S.kind t = adaptiveKind I per t) → 0 < I →
    -- V derived the state of every interval up to the run's last round, reading its agreed
    -- output on the schedule it runs
    (∀ j, j ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I K p.async coin upd k₀ U V (steelheadAt p) j st ∧ per j = st.period) →
    -- the coin leads every asynchronous slot
    (∀ r, S.kind r = 1 → S.leader r = coin r) →
    -- the slot lies at round one or above, and an interval at least two past its own finds an
    -- anchor in V under the period the view derived for it ...
    1 ≤ s → intervalOf I s + 1 < j₁ → IntervalAnchor I K p.async coin U V j₁ (per j₁) i₁ A →
    -- ... and above that interval the coin names a good validator at wa consecutive rounds, in a
    -- view holding their decision rounds
    (j₁ + 1) * I < b → (∀ i, i < wa → coin (b + i) ∈ good U (b + i)) →
    V.CoversUpto (b + wa - 1 + (wa - 1)) →
    -- then the slot is decided in V
    ∃ v, (steelheadAt p).Decided U V s v

/-- **SH14b, every slot is decided under the clause.** -/
def AllDecided (U : BlockUniverse Validator BlockId Payload)
    (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) (wa I K : ℕ)
    [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (c N : ℕ),
    p.sync.Laws → p.async.Laws → LeastLinked p.sync → LeastLinked p.async → CommitLaws p.async →
    GoodCommits p.async good →
    p.sync.waveAt 0 ≤ p.async.waveAt 1 → p.async.waveAt 1 + 1 = wa →
    (∀ t, S.slotRound t = t) → (∀ t, S.kind t = adaptiveKind I per t) → 0 < I →
    -- the coin leads every asynchronous slot
    (∀ r, S.kind r = 1 → S.leader r = coin r) →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- a window of c control slots plus a run of wa fit in an interval at every period up to K
    (c + wa) * K ≤ I →
    -- the run form of the clause at every control schedule a period in range names
    (∀ j k, 1 ≤ k → k ≤ K → RunWithin (S := controlSlots coin I K j k) p.async good U c wa N) →
    -- the view holds every block up to the horizon and derived every state below it, reading
    -- its agreed output on the schedule it runs
    V.CoversUpto N →
    (∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I K p.async coin upd k₀ U V (steelheadAt p) j st ∧ per j = st.period) →
    -- then every slot at round one or above and three intervals and a window below the horizon
    -- is decided
    ∀ s, 1 ≤ s → (intervalOf I s + 3) * I + c + wa + (wa - 1) ≤ N →
      ∃ v, (steelheadAt p).Decided U V s v

/-- **SH14c, output liveness from a good coin and a good run.** -/
def OutputLivenessOfRuns (U : BlockUniverse Validator BlockId Payload)
    (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) (wa I K : ℕ)
    [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (s j b : ℕ),
    p.sync.Laws → p.async.Laws → LeastLinked p.sync → LeastLinked p.async → CommitLaws p.async →
    GoodCommits p.async good →
    p.sync.waveAt 0 ≤ p.async.waveAt 1 → p.async.waveAt 1 + 1 = wa →
    (∀ t, S.slotRound t = t) → (∀ t, S.kind t = adaptiveKind I per t) → 0 < I →
    -- the coin leads every asynchronous slot
    (∀ r, S.kind r = 1 → S.leader r = coin r) →
    -- V derived the state of every interval up to the run's last round, reading its agreed
    -- output on the schedule it runs
    (∀ j', j' ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I K p.async coin upd k₀ U V (steelheadAt p) j' st ∧ per j' = st.period) →
    -- the slot lies at round one or above; at least two intervals past its own, interval j
    -- runs at a period that puts its first control round inside it, and the coin there is
    -- good ...
    1 ≤ s → intervalOf I s + 1 < j → 1 ≤ per j → per j ≤ I →
    coin (firstControlRound I j (per j)) ∈ good U (firstControlRound I j (per j)) →
    -- ... and above interval j the coin names a good validator at wa consecutive rounds, in a
    -- view holding their decision rounds
    (j + 1) * I < b → (∀ i, i < wa → coin (b + i) ∈ good U (b + i)) →
    V.CoversUpto (b + wa - 1 + (wa - 1)) →
    -- then the slot is decided in V
    ∃ v, (steelheadAt p).Decided U V s v

/-- The period sequence, over every fault configuration, schedule, block universe, pair of
rules, good set, interval, run length and positive period bound the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload)
    (Ra R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (p : RulePair Validator BlockId Payload)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) (wa I K : ℕ)
    [NeZero K],
    PeriodAgreement U Ra R I K ∧ AdaptiveAgreement U Ra R I K ∧ ScanEnds U Ra R I K ∧
      PeriodOfClause U Ra R good I K wa ∧ PeriodOne U Ra R I K ∧ TwoAsyncRounds I ∧
      PeriodInRange U Ra R I K ∧ AgreedPrefix U Ra R I K ∧ StalledBelowUndecided U Ra R I K ∧
      WindowResolves I wa K ∧ ControlRounds I K ∧ ControlAgreement U Ra I K ∧
      WarmUp U Ra R I K ∧ TwoAsyncRoundsInWindow I ∧ PeriodDvd U Ra R I K ∧
      ControlSlotsAsync (Validator := Validator) I K ∧ GatedByScan U Ra R I K ∧
      OutputLiveness U p good wa I K ∧ AllDecided U p good wa I K ∧
      OutputLivenessOfRuns U p good wa I K

end Period

end Steelhead

end LeanDag
