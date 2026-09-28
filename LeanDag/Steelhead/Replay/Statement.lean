import LeanDag.Steelhead.Model.Replay
/-!
# The replay — statement

What Algorithm 3's replay and selection do (`steelhead.md` §5), on any
window's evidence. Ten claims:

* **SH18a, the selection stays among the candidates** — Algorithm 3
  answers a candidate period whenever the current period is one, so the
  period stays in the candidate set (SH10g's premise for it);
* **SH18b, the selection never worsens the score** — the period chosen
  scores no worse than the current one on the window, whatever the
  hysteresis;
* **SH18e, the timings are bounded** — every round's expected decision
  lies at or above the round, its expected commit at or above its
  decision, and both at or below the window's top, so the window's top
  is the penalty an unresolved outcome pays and no more;
* **SH18f, the asynchronous term is bounded by the committed count** —
  Lemma 3's second sentence in the form that is a theorem: at an
  asynchronous round of the window whose committed candidates are not
  skipped, the replay's commit term is at most the mean over the `n`
  candidates of the decision round for the `c_r` committed ones and the
  window's top for the rest; with SH-MM18d, `c_r ≥ n − f − b` bounds the
  term under any scheduling. The bound charges every candidate without
  a direct commit the window's top; the asynchronous rule's own latency
  on the same data is not modelled, and no comparison with it is
  claimed;
* **SH18h, Algorithm 3 keeps the range** — with candidates in `[1, K]`,
  the replay's selection answers a period in `[1, K]` on any window's
  evidence, whether it keeps the current period or picks a candidate: the
  range hypothesis SH10g, SH14b, SH14c and SH15 place on the update rule,
  discharged for the paper's rule; the failover's `1` is the scan's own
  (SH10e) and lies in the range too;
* **SH18j, a probe exists** — the protocol section's "setting the canary
  odd ensures it is coprime to candidate periods, guaranteeing periodic
  probes": at a canary spacing coprime to a candidate period of at
  least two, a window holding two canary rounds whose decision round it
  retains holds a probe for that candidate, since two consecutive
  multiples of the spacing cannot both be multiples of the period;
* **SH18k, the hysteresis** — the adaptive section's "it keeps the
  current period unless the best candidate improves on it by a factor
  of `1 − ε`": the selection leaves the current period, a candidate
  itself, only for a candidate whose score is below `1 − ε` times the
  current period's, and takes the best candidate whenever that one's is;
* **SH18l, ties keep the current period and otherwise favour the larger
  candidate** — the adaptive section's tie rule: the best candidate
  scores no worse than the current period and than every candidate, is
  the current period whenever that scores as well, and is otherwise the
  largest of the candidates that tie for its score, whatever the order
  the candidates are listed in;
* **SH18m, an odd canary probes every candidate** — the protocol
  section's sentence itself: at an odd canary spacing, SH18j's window
  holds a probe for every candidate of at least two, the candidates
  being powers of two, to which an odd number is coprime;
* **SH18n, every candidate divides the period bound** — the protocol
  section's "every candidate divides maxPeriod", at a power-of-two bound
  as the implementation's `max_period` is: the candidates are the powers
  of two up to it, and Algorithm 3 answers a divisor of the bound from
  one on any window's evidence, the current period or a candidate
  (SH18a), which is what SH10o asks of an update rule.

None of these reads the DAG: they hold of any `Evidence`, whichever rule
pair's window filled it, and at either place of the blame round
(`Config.merged`). How a window's evidence is read from the DAG is the
pair's: the Mysticeti and Mahi-Mahi pair's window (`ofAnchor`) reads
Mahi-Mahi's certificates and blames, and BlueBottle's
(`BlueBottlePair.Replay.ofAnchor`) the decision-round votes themselves,
Odontoceti's at wave two and Async BlueBottle's otherwise. What each
reading gives, the paper's Lemma 3 among it, is SH-MM18 in
`MahiMahiPair/Replay/Statement.lean` and SH-BB18 in
`BlueBottlePair/Replay/Statement.lean`.

SH18e and SH18f ask `2 ≤ ws` and `ws < wa`, the waves of the `3f + 1`
pair, so that a round's decision round lies at or above it and an
asynchronous round is not read as an unprobed synchronous one. SH18j asks
`1 ≤ ws`, so that a probe's decision round lies in the range the window
resolves. SH18k asks the current period to be a candidate, as SH18a
does, since the fold answers its winner outright otherwise; SH18m asks
SH18j's window; SH18n a power-of-two bound, without which the largest
candidate need not divide it.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Replay

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]

/-- **SH18a, the selection stays among the candidates.** -/
def SelectionValid : Prop :=
  ∀ (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ) (epsilon : ℚ),
    current ∈ candidates → select candidates scores current epsilon ∈ candidates

/-- **SH18b, the selection never worsens the score.** -/
def SelectionNonIncreasing : Prop :=
  ∀ (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ) (epsilon : ℚ),
    scores (select candidates scores current epsilon) ≤ scores current

/-- **SH18e, the timings are bounded.** -/
def TimingBounded : Prop :=
  ∀ (E : Evidence Validator) (C : Config Validator) (period r : ℕ),
    2 ≤ C.ws → 2 ≤ C.wa → r ≤ E.top →
    -- a round's expected decision lies at or above the round, its expected commit at or above
    -- its decision, and both at or below the window's top
    (r : ℚ) ≤ (timingAt E C period (probeRate E C period) r).decision ∧
      (timingAt E C period (probeRate E C period) r).decision ≤
        (timingAt E C period (probeRate E C period) r).commit ∧
      (timingAt E C period (probeRate E C period) r).commit ≤ E.top

/-- **SH18f, the asynchronous term is at most the rule's own value.** -/
def AsyncTermBound : Prop :=
  ∀ (E : Evidence Validator) (C : Config Validator) (period r : ℕ),
    2 ≤ C.ws → C.ws < C.wa →
    -- an asynchronous round of the window under the candidate period, decided inside the window
    E.bottom ≤ r → r % period = 0 → r + C.wa - 1 ≤ E.top →
    -- whose committed candidates are not skipped, as the window's are (SH-MM18c)
    (∀ a, E.commits r C.wa a = true → E.skips r C.wa a = false) →
    -- then the replay's commit term at r is at most the mean over the n candidates of the
    -- decision round for the committed ones and the window's top for the rest
    (timingAt E C period (probeRate E C period) r).commit ≤
      ((committedCount E r C.wa * (r + C.wa - 1) +
        (Fintype.card Validator - committedCount E r C.wa) * E.top : ℕ) : ℚ) /
        Fintype.card Validator

/-- **SH18h, Algorithm 3 keeps the range.** -/
def UpdateInRange : Prop :=
  ∀ (E : Evidence Validator) (C : Config Validator) (candidates : List ℕ) (epsilon : ℚ) (K k : ℕ),
    -- the candidates lie in [1, K], as does the current period
    (∀ c ∈ candidates, 1 ≤ c ∧ c ≤ K) → 1 ≤ k → k ≤ K →
    -- then so does the selection's answer on the window's evidence
    1 ≤ update E C candidates k epsilon ∧ update E C candidates k epsilon ≤ K

/-- **SH18j, a probe exists.** -/
def ProbeExists : Prop :=
  ∀ (E : Evidence Validator) (C : Config Validator) (canary period : ℕ),
    -- the canary is on, and its spacing is coprime to the candidate period, which is at least two
    C.canary = some canary → Nat.Coprime canary period → 2 ≤ period → 1 ≤ C.ws →
    -- and the window holds two canary rounds whose decision round it retains
    E.bottom + 2 * canary + C.ws ≤ E.top + 2 →
    -- then the candidate has a probe
    0 < (probeRate E C period).2

/-- **SH18k, the hysteresis.** -/
def Hysteresis : Prop :=
  ∀ (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ) (epsilon : ℚ),
    -- the current period is a candidate
    current ∈ candidates →
    -- then the selection leaves the current period only for a candidate that improves on it by
    -- the factor 1 − ε ...
    (select candidates scores current epsilon ≠ current →
      scores (select candidates scores current epsilon) < (1 - epsilon) * scores current) ∧
    -- ... and takes the best candidate whenever that one does
    (scores (best candidates scores current) < (1 - epsilon) * scores current →
      select candidates scores current epsilon = best candidates scores current)

/-- **SH18l, ties keep the current period and otherwise favour the larger candidate.** -/
def TieRule : Prop :=
  ∀ (candidates : List ℕ) (scores : ℕ → ℚ) (current : ℕ),
    -- the best candidate scores no worse than the current period and than every candidate ...
    scores (best candidates scores current) ≤ scores current ∧
    (∀ k ∈ candidates, scores (best candidates scores current) ≤ scores k) ∧
    -- ... it is the current period whenever that scores as well ...
    (scores (best candidates scores current) = scores current →
      best candidates scores current = current) ∧
    -- ... and otherwise the largest of the candidates that tie for its score
    (best candidates scores current ≠ current →
      ∀ k ∈ candidates, scores k = scores (best candidates scores current) →
        k ≤ best candidates scores current)

/-- **SH18m, an odd canary probes every candidate.** -/
def OddCanaryProbes : Prop :=
  ∀ (E : Evidence Validator) (C : Config Validator) (canary K period : ℕ),
    -- the canary is on and its spacing odd, and the period is a candidate of at least two
    C.canary = some canary → Odd canary → period ∈ candidatesUpto K → 2 ≤ period → 1 ≤ C.ws →
    -- and the window holds two canary rounds whose decision round it retains
    E.bottom + 2 * canary + C.ws ≤ E.top + 2 →
    -- then the candidate has a probe
    0 < (probeRate E C period).2

/-- **SH18n, every candidate divides the period bound.** -/
def CandidatesDvd : Prop :=
  ∀ (E : Evidence Validator) (C : Config Validator) (epsilon : ℚ) (e K k : ℕ),
    -- the period bound is a power of two
    K = 2 ^ e →
    -- then every candidate divides it ...
    (∀ c ∈ candidatesUpto K, c ∣ K) ∧
    -- ... and Algorithm 3 answers a divisor of it from a divisor of it, on the window's evidence
    (k ∣ K → update E C (candidatesUpto K) k epsilon ∣ K)

/-- The replay, over every fault configuration the model admits and every window's evidence. -/
def Statement : Prop :=
  ∀ (Validator : Type) [Fintype Validator] [DecidableEq Validator] [Faults Validator],
    SelectionValid ∧ SelectionNonIncreasing ∧ TimingBounded (Validator := Validator) ∧
      AsyncTermBound (Validator := Validator) ∧ UpdateInRange (Validator := Validator) ∧
      ProbeExists (Validator := Validator) ∧ Hysteresis ∧ TieRule ∧
      OddCanaryProbes (Validator := Validator) ∧ CandidatesDvd (Validator := Validator)

end Replay

end Steelhead

end LeanDag
