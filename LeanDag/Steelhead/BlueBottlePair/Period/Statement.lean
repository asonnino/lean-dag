import LeanDag.Steelhead.Model.Pair
import LeanDag.Steelhead.Model.Period
import LeanDag.Steelhead.Model.Clauses
import LeanDag.AsyncBlueBottle.Model.Unpredictable
/-!
# The `5f + 1` pair's period sequence — statement

The period sequence at BlueBottle's two variants: the control verdicts
read by Async BlueBottle, the agreed output by the pair's composite
`blueBottlePairAnchored`, which is `steelheadAt bbPair`. The generic
statements of `Period/Statement.lean` read the rules through their laws
and the clauses of `Model/Clauses.lean`; this file states that the pair
meets them, and Theorems 3 and 4 at the pair as the generic statements
then give them. Four claims:

* **SH-BB10, the pair meets the period sequence's hypotheses** — Async
  BlueBottle is lawful, its commits are witnessed in their views, a vote
  quorum or a weak link reaching the candidate, its tie-break has a
  choice, its good set (`goodAt`) commits, and its wave is two rounds;
  Odontoceti is lawful, its tie-break has a choice, and its wave is one
  round; the composite is lawful and its verdicts are witnessed in their
  views, a direct skip resting on blames one or two rounds up;
* **SH-BB10a, agreement of the period** — Theorem 4 at the pair: SH10a,
  Async BlueBottle being lawful;
* **SH-BB10d, the period advances under the clause** — Theorem 3 (i) at
  the pair: SH10d with ABB9c's run clause at every control schedule, runs
  of three slots;
* **SH-BB14b, every slot is decided under the clause** — Theorem 3 (ii)
  at the pair: SH14b at `bbPair`, the good set Async BlueBottle's and
  runs of three slots.

The remaining claims of `Period/Statement.lean` either ask nothing of the
rules or ask what SH-BB10 supplies. Odontoceti and Async BlueBottle are
consumed read-only.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Period

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

omit S in
/-- **SH-BB10, the pair meets the period sequence's hypotheses.** -/
def PeriodHypotheses (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults5 Validator] [LinearOrder BlockId] : Prop :=
  -- Async BlueBottle is lawful, its commits are witnessed in their views, its tie-break has a
  -- choice, its good set commits, and a run of three slots spans its wave
  (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).Laws ∧
    CommitLaws (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) ∧
    LeastLinked (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) ∧
    GoodCommits (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload)
      (fun U r => AsyncBlueBottle.goodAt U r) ∧
    (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).waveAt 1 + 1 = 3 ∧
    -- Odontoceti is lawful, its tie-break has a choice, and its wave is no longer
    (Odontoceti.odontocetiAnchored Validator BlockId Payload).Laws ∧
    LeastLinked (Odontoceti.odontocetiAnchored Validator BlockId Payload) ∧
    (Odontoceti.odontocetiAnchored Validator BlockId Payload).waveAt 0 ≤
      (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).waveAt 1 ∧
    -- the composite is lawful, and its verdicts are witnessed in their views
    (blueBottlePairAnchored Validator BlockId Payload).Laws ∧
    ViewLaws (blueBottlePairAnchored Validator BlockId Payload)

/-- **SH-BB10a, agreement of the period.** -/
def PeriodAgreement (U : BlockUniverse Validator BlockId Payload) (I K : ℕ) [NeZero K] :
    Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V₁ V₂ : View Validator BlockId Payload U) (j : ℕ) (st₁ st₂ : ScanState),
    PeriodAt I K (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) coin upd k₀ U
        V₁ (blueBottlePairAnchored Validator BlockId Payload) j st₁ →
      PeriodAt I K (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) coin upd k₀
        U V₂ (blueBottlePairAnchored Validator BlockId Payload) j st₂ →
      st₁ = st₂

/-- **SH-BB10d, the period advances under the clause.** -/
def PeriodOfClause (U : BlockUniverse Validator BlockId Payload) (I K : ℕ) [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (c N : ℕ),
    -- a positive interval
    0 < I →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- ABB9c's run form of the clause at every control schedule a period in range names: in every
    -- window of c control slots below the horizon, three consecutive ones whose coins are good
    (∀ j k, 1 ≤ k → k ≤ K →
      AsyncBlueBottle.UnpredictableRunWithin (S := controlSlots coin I K j k) U c 3 N) →
    -- the view holds every block up to the horizon
    V.CoversUpto N →
    -- for every interval whose control slots, and the window above them, decide below the
    -- horizon ...
    ∀ j, (j + 1) * I + (c + 3) * K + 2 ≤ N →
      -- ... the view derives the next interval's state
      ∃ st, PeriodAt I K (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) coin
        upd k₀ U V (blueBottlePairAnchored Validator BlockId Payload) (j + 1) st

/-- **SH-BB14b, every slot is decided under the clause.** -/
def AllDecided (U : BlockUniverse Validator BlockId Payload) (I K : ℕ) [NeZero K] : Prop :=
  ∀ (coin : ℕ → Validator) (upd : UpdateRule BlockId) (k₀ : ℕ)
    (V : View Validator BlockId Payload U) (per : ℕ → ℕ) (c N : ℕ),
    -- one slot per round, of the kind the derived period assigns it, and a positive interval
    (∀ t, S.slotRound t = t) → (∀ t, S.kind t = adaptiveKind I per t) → 0 < I →
    -- the coin leads every asynchronous slot
    (∀ r, S.kind r = 1 → S.leader r = coin r) →
    -- the initial period lies in [1, K], and the update rule keeps a period there
    1 ≤ k₀ → k₀ ≤ K → (∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K) →
    -- a window of c control slots plus a run of three fit in an interval at every period up to K
    (c + 3) * K ≤ I →
    -- ABB9c's run form of the clause at every control schedule a period in range names
    (∀ j k, 1 ≤ k → k ≤ K →
      AsyncBlueBottle.UnpredictableRunWithin (S := controlSlots coin I K j k) U c 3 N) →
    -- the view holds every block up to the horizon and derived every state below it, reading
    -- its agreed output on the schedule it runs
    V.CoversUpto N →
    (∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I K (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) coin upd k₀
          U V (blueBottlePairAnchored Validator BlockId Payload) j st ∧ per j = st.period) →
    -- then every slot at round one or above and three intervals and a window below the horizon
    -- is decided
    ∀ s, 1 ≤ s → (intervalOf I s + 3) * I + c + 3 + 2 ≤ N →
      ∃ v, (blueBottlePairAnchored Validator BlockId Payload).Decided U V s v

/-- The `5f + 1` pair's period sequence, over every fault configuration, schedule, block universe,
interval and positive period bound the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (I K : ℕ) [NeZero K],
    PeriodHypotheses Validator BlockId Payload ∧ PeriodAgreement U I K ∧ PeriodOfClause U I K ∧
      AllDecided U I K

end Period

end BlueBottlePair

end Steelhead

end LeanDag
