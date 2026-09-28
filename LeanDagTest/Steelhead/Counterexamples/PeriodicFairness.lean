import LeanDag.Steelhead.Liveness.Proof
/-!
# Steelhead counterexample: the fairness count at a mixed period

SH6h bounds the floor chain by counting, over a span of whole round-robin
cycles, the rounds the schedule leads from the reliable set `T`: at least
`|T|` a cycle, each of which has to fit in the `ws − 1` rounds a hop
leaves free, which forces `ws · (n − |T|) < n`. At a period that count
loses the coin's rounds, since a round the coin leads is led by nobody
the schedule names, and the bound becomes
`ws · (n − |T|) + ws · ⌈n / p⌉ < n` (SH6o, SH6p).

The extra term is never zero: `⌈n / p⌉ ≥ 1` for every committee and every
period. So at `ws = 3` on the tight committee `n = 3f + 1` with a bare
reliable quorum `|T| = n − f`, where the original bound holds with
exactly one round of slack, the new one fails for **every** period. The
chain there is bounded by the coin and not by the schedule, which is
what SH6o's decidedness hypothesis asks for.

It is not a limit of the period but of the committee's slack: the bound
holds as soon as fewer than `f` validators lie outside `T`, or the
committee is larger, and the witnesses below exhibit both.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead

/-- Every committee and period leave at least one coin round in a cycle. -/
theorem one_le_coin_rounds {n p : ℕ} (hn : 1 ≤ n) (hp : 0 < p) : 1 ≤ (n + p - 1) / p :=
  (Nat.one_le_div_iff hp).mpr (by omega)

/-- **The constant-wave count is tight at `n = 3f + 1`**: with the reliable set a bare quorum it
holds with exactly one round to spare. -/
theorem tight_committee_constant (f : ℕ) :
    3 * ((3 * f + 1) - (2 * f + 1)) < 3 * f + 1 := by omega

/-- **The periodic count fails at `n = 3f + 1` for every period**: the one round of slack is
exactly what the coin's rounds take, so no period is small enough. -/
theorem tight_committee_periodic_fails (f p : ℕ) (hp : 0 < p) :
    ¬ (3 * ((3 * f + 1) - (2 * f + 1)) + 3 * ((3 * f + 1 + p - 1) / p) < 3 * f + 1) := by
  have := one_le_coin_rounds (n := 3 * f + 1) (by omega) hp
  omega

/-- **It holds when fewer than `f` validators lie outside the reliable set**: at `n = 7` with one
validator outside `T` and a period of seven, the count has room. -/
theorem slack_committee_periodic : 3 * (7 - 6) + 3 * ((7 + 7 - 1) / 7) < 7 := by decide

/-- **And when the whole committee is reliable**, where only the coin's rounds are deducted. -/
theorem full_committee_periodic : 3 * (4 - 4) + 3 * ((4 + 4 - 1) / 4) < 4 := by decide

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms tight_committee_periodic_fails
#print axioms slack_committee_periodic

end LeanDagTest
