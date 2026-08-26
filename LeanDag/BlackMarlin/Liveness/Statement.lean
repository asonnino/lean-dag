import LeanDag.BlackMarlin.Model.Decision
import LeanDag.Liveness

/-!
# Black Marlin — liveness, stated

What the commit rule admits once the DAG is populated and coverage has
taken hold (`black-marlin.md` §8). Five claims:

* **BML1, `CommitStep`** — a run of **two** consecutive reliable anchors,
  over three populated rounds, is committed;
* **BML2, `FullViewSound`** — a validator holding the whole DAG commits
  exactly what the rule commits, so BML1 is a statement about a verdict
  actually reached;
* **BML3, `Inclusion`** — every reliable validator's block lies in the
  causal history of every block two rounds above it, hence of every
  committed anchor there. The paper's Lemma 8, and its Validity property
  for reliable authors;
* **BML4, `Recurrence`** — under a recurring run of two the rotation
  names, for every round, a later round that any sufficiently grown
  covered DAG commits;
* **BML5, `RotationFair`** — round-robin supplies the run of two, at
  every committee and every fault configuration. Not an assumption: a
  theorem.

Not among the hypotheses: a timeout, a message delay, a global
stabilisation time, or a probability. The paper reaches liveness through
§5.2's timing argument — Lemma 7's `3∆` round bound, Lemma 10 on the
timeout not firing with honest anchors, Lemma 11 on the expected number
of rounds to a correct anchor. This development states liveness above
the structural condition instead (`liveness.md`), so those are replaced
rather than transcribed, and Lemma 11 has no counterpart: BML5 makes the
recurring run deterministic.

**Why two rounds, and where each is used.** The rule reads three rounds
— support for the anchor at `r + 1`, and support for the anchor above it
at `r + 2` — so BML1 asks for population at `r`, `r + 1` and `r + 2`.
The link itself costs nothing beyond that: coverage already makes every
reliable round-`(r+1)` block reference the round-`r` anchor, and the
round-`(r+1)` anchor is one of them. So the whole premise is that the
rotation names reliable validators at two consecutive rounds, which is
`FairRun T 2`.

**Why BML5 is a theorem here and an assumption in the core.** The core's
`FairRunOn` needs runs of three, and its docstring records the
pigeonhole for per-slot rotation as prose rather than proving it;
`WaveRobin.lean` supplies runs of three by rotating in waves instead.
Black Marlin needs runs of two, and that case is short: if no two
cyclically adjacent anchors were reliable, the successor map would
inject the reliable set into the Byzantine one, giving `2f + 1 ≤ f`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Liveness

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **The fairness clause**: the rotation puts `c` consecutive
`T`-anchored rounds arbitrarily far out.

The round-indexed counterpart of the core's `FairRunOn`, which is stated
over slots. Like it, this is a property of the rotation alone — no DAG
occurs in it — which is what lets BML4 name a round before any universe
is fixed. Unlike it, BML5 discharges this one. -/
def FairRun (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ r, ∃ r', r ≤ r' ∧ ∀ i, i < c → Rot.anchor (r' + i) ∈ T

/-- **BML1, the commit step.** Two consecutive reliable anchors over
three populated rounds are committed.

`R` is the round from which coverage holds. Support for the anchor comes
from the round above it and support for its linking anchor from the
round above that, which is why three rounds are asked for and why the
run is of length two. -/
def CommitStep (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (R r : ℕ),
    -- a quorum of reliable validators
    quorumCard Validator ≤ T.card →
    -- coverage among them from round `R` on, and the anchor is at or above it
    SynchronisedOn U T R → R ≤ r →
    -- the three rounds the rule reads are populated by them
    PopulatedOn U T r → PopulatedOn U T (r + 1) → PopulatedOn U T (r + 2) →
    -- and the rotation names reliable validators at two consecutive rounds
    Rot.anchor r ∈ T → Rot.anchor (r + 1) ∈ T →
    -- then round `r` has a committed anchor
    ∃ L, IsAnchor U r L ∧ Committed U L r

/-- **BML2, the full view commits what the rule commits.** The converse
of BM4 at the view that holds everything, so a universe-level `Committed`
is a verdict some validator can actually reach. -/
def FullViewSound (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L : BlockId) (r : ℕ), CommittedIn U (View.full U) L r ↔ Committed U L r

/-- **BML3, inclusion** (the paper's Lemma 8): a reliable validator's
block lies in the causal history of every block two rounds above it.

The delivery half of atomic broadcast, for reliable authors: a committed
anchor at round `ρ + 2` or above delivers `past` of itself, so the block
is delivered when that anchor commits. The proof is coverage giving the
block a support quorum and BM2 carrying it upward, so no clause of the
commit rule is consumed — inclusion does not depend on which anchors the
rule admits, only on one being admitted above. -/
def Inclusion (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (R ρ : ℕ) (b c : BlockId),
    -- a quorum of reliable validators, covering from `R` on
    quorumCard Validator ≤ T.card → SynchronisedOn U T R → R ≤ ρ →
    -- the round above `b` is populated by them
    PopulatedOn U T (ρ + 1) →
    -- `b` is a reliable validator's block at round `ρ`
    b ∈ U.ids → (U.block b).round = ρ → (U.block b).creator ∈ T →
    -- and `c` is any block two rounds above it or higher
    c ∈ U.ids → ρ + 2 ≤ (U.block c).round →
    -- then `b` is in what committing `c` delivers
    b ∈ history U c

/-- **What it means for a round to commit in every grown covered DAG.**

The universe is quantified **inside**, as the core's `CommitsAt` is and
for the same reason: the rotation names the round, and any DAG grown two
rounds past it and covered from `R` commits it. Fixing a universe first
would cap how far the rotation may reach. -/
def CommitsAtRound (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    (T : Finset Validator) (R r : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
    (∀ n, R ≤ n → n ≤ N → PopulatedOn U T n) → SynchronisedOn U T R →
    r + 2 ≤ N →
    ∃ L, IsAnchor U r L ∧ Committed U L r

variable (Validator BlockId Payload) in
/-- **BML4, recurrence.** Under a recurring run of two, no round is the
last one a DAG can be grown far enough to commit above. -/
def Recurrence : Prop :=
  ∀ (T : Finset Validator) (R r : ℕ),
    quorumCard Validator ≤ T.card → FairRun T 2 →
    ∃ r', r ≤ r' ∧ R ≤ r' ∧ CommitsAtRound BlockId Payload T R r'

/-- **Round-robin rotation** on `Fin n`: round `r` anchored by `r % n`.
The rotation Black Marlin deploys, written as an instance of the arc's
one-field class. -/
@[reducible]
def roundRobin (n : ℕ) (hn : 0 < n) : Rotation (Fin n) where
  anchor r := ⟨r % n, Nat.mod_lt _ hn⟩

/-- **BML5, the fairness clause is a theorem.** Round-robin puts two
consecutive reliable anchors arbitrarily far out, at every committee and
whichever validators are Byzantine.

The core's corresponding fact is an assumption discharged by a
wave-aligned witness, because it needs runs of three. Two is the case a
counting argument settles outright. -/
def RotationFair : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults (Fin n)],
    FairRun (Rot := roundRobin n hn) (Correct : Finset (Fin n)) 2

/-- Liveness of the Black Marlin commit rule, over every fault
configuration, anchor rotation and block universe the model admits, plus
the satisfiability of the one clause it assumes. -/
def Statement : Prop :=
  (∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [DecidableEq BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    CommitStep U ∧ FullViewSound U ∧ Inclusion U ∧
      Recurrence Validator BlockId Payload) ∧
  RotationFair

end Liveness

end BlackMarlin

end LeanDag
