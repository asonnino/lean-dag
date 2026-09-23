import LeanDag.Steelhead.Model.Timeout
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# The `3f + 1` pair's mistimed leader timeout — statement

The arithmetic of the paper's appendix on a leader timeout smaller than the
link delay (`steelhead.md` §10), at the Mysticeti and Mahi-Mahi pair, whose
direct commit counts certificates. Two claims:

* **SH-MM20a, the certificate probability at the top of the vote round** — with
  minimum-quorum references a certificate forms with probability `1` when
  every block of the vote round voted, and `f / n` when exactly one did not.
  The second is what makes the two-layer rule an all-or-nothing filter: the
  appendix's own numbers, the `0.001` the `v = n − 1` term contributes at
  `n = 10` and the approximation `P₂ ≈ Pr[V = n]` that follows from it, hold
  at `f / n` and not at `(n − f) / n`;
* **SH-MM20b, the wait for the next direct commit** — the appendix's `1 / P₂`.
  At a per-round direct-commit probability `p`, with the rounds independent,
  no commit falls in the first `m` rounds with probability `(1 − p)^m`, and
  the layer cake `∑ₘ P(T > m)` of those chances is `1 / p`.

SH-MM20b is the series, not an expectation over a process the model carries:
nothing here builds the rounds as random variables, so what is checked is that
the layer cake of the appendix's own tail probabilities sums to its `1 / P₂`.
The reference pattern, the uniform arrival order and the independence between
validators' orders are the appendix's assumptions and are not modelled; the
appendix states the last of them as its one optimistic step. The BlueBottle
pair has no certificate stage, so the all-or-nothing filter SH-MM20a finds
has no counterpart there, and none is stated.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

namespace Timeout

/-- **SH-MM20a, the certificate probability at a full and a nearly full vote round.** -/
def CertProbEdges : Prop :=
  ∀ n f : ℕ,
    -- a non-empty committee whose fault bound leaves a quorum
    0 < n → f ≤ n →
    -- a unanimous vote round always certifies, and one abstention leaves f / n
    certProb n f n = 1 ∧ certProb n f (n - 1) = (f : ℚ) / n

/-- **SH-MM20b, the wait for the next direct commit.** -/
def ExpectedRoundsToCommit : Prop :=
  ∀ p : ENNReal,
    -- a positive commit probability
    0 < p → p ≤ 1 →
    -- the layer cake of the tail probabilities is the appendix's 1 / P₂
    ∑' m : ℕ, (1 - p) ^ m = p⁻¹

/-- The appendix's arithmetic, over every committee size and fault bound the
model admits. -/
def Statement : Prop :=
  CertProbEdges ∧ ExpectedRoundsToCommit

end Timeout

end MahiMahiPair

end Steelhead

end LeanDag
