import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
/-!
# Steelhead — the mistimed leader timeout

The paper's appendix on the two partially synchronous rules when the leader
timeout `T` is smaller than the link delay `D` (`steelhead.md` §10). With
every link delayed past the timeout, the timer fires before any block of the
round arrives, so a validator proposes the instant its threshold clock reaches
`n − f` blocks and its block carries **minimum-quorum references**: exactly
`n − f` blocks of the previous round, the earliest to arrive, and never more.

Under that reference pattern a certifier holds exactly `n − f` references, so
all of them must be votes for a certificate to form. Reading the arrival order
as uniform, the chance of that is hypergeometric in the number of votes the
round carries, which is `certProb` below. The two ends of it decide the
appendix: it is `1` when every block voted, and `f / n` when exactly one did
not, which is small enough that a two-layer rule commits directly only when
the vote round was unanimous.

This appendix carries no DAG and no consensus: the arrival order is an
assumption about the network, not a property of the model, and the independence
the appendix assumes between validators' orders is stated there as the one
optimistic step. Only the arithmetic is here.

**Definitions only.** The claims are in `Timeout/Statement.lean` and proved in
its `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

/-- **The certificate probability** `π(v)`: with minimum-quorum references a
certifier's `n − f` references are all votes, out of a round carrying `v`
votes, with probability `(v choose (n − f)) / (n choose (n − f))`. -/
noncomputable def certProb (n f v : ℕ) : ℚ :=
  (v.choose (n - f) : ℚ) / (n.choose (n - f) : ℚ)

end Steelhead

end LeanDag
