import LeanDag.Steelhead.Model.Timeout
import Mathlib.Analysis.SpecificLimits.Basic
/-!
# The mistimed leader timeout — helpers

Generated proof layer; not part of the audit surface. Each helper closes the
conjunct of the same name in `Timeout/Statement.lean`.
-/

namespace LeanDag

namespace Steelhead

/-- **SH20a, the unanimous vote round.** The ratio is the same binomial over
itself, and `n choose (n − f)` is positive since `n − f ≤ n`. -/
theorem certProb_self {n f : ℕ} : certProb n f n = 1 := by
  have h : (n.choose (n - f) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (Nat.sub_le n f)).ne'
  exact div_self h

/-- **The one-abstention ratio.** `(n − 1 choose q) / (n choose q) = (n − q) / n`,
by `Nat.choose_mul_succ_eq` at `n − 1`. -/
theorem certProb_pred_aux {n q : ℕ} (hn : 0 < n) (hq : q ≤ n) :
    ((n - 1).choose q : ℚ) / n.choose q = ((n - q : ℕ) : ℚ) / (n : ℚ) := by
  have hid := Nat.choose_mul_succ_eq (n - 1) q
  rw [Nat.sub_add_cancel hn] at hid
  have hden : (n.choose q : ℚ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hq).ne'
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn.ne'
  refine (div_eq_div_iff hden hn').mpr ?_
  exact_mod_cast (by simpa only [Nat.mul_comm] using hid)

/-- **SH20a, one abstention.** At the threshold `n − f` the ratio is `f / n`,
not `(n − f) / n`: the complement of the threshold is the fault bound. -/
theorem certProb_pred {n f : ℕ} (hn : 0 < n) (hf : f ≤ n) :
    certProb n f (n - 1) = (f : ℚ) / n := by
  rw [certProb, certProb_pred_aux hn (Nat.sub_le n f), Nat.sub_sub_self hf]

/-- **SH20b.** The layer cake of the tail probabilities is geometric in
`1 − p`, and `1 − (1 − p) = p` in `ℝ≥0∞` once `p ≤ 1`. -/
theorem tsum_tail_eq_inv {p : ENNReal} (hp1 : p ≤ 1) :
    ∑' m : ℕ, (1 - p) ^ m = p⁻¹ := by
  rw [ENNReal.tsum_geometric, ENNReal.sub_sub_cancel (by norm_num) hp1]

end Steelhead

end LeanDag
