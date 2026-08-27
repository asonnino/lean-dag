import LeanDag.FinWhale.Model.Params

/-!
# FinWhale — the arithmetic of the committee

The facts that follow from `n + 1 = 3f + 2p` with `1 ≤ p ≤ f`, and
nothing else. `params_arith` is the standing form every counting argument
of the arc hands to `omega`; `spQuorum_eq_ceil` checks that the closed
form `2f + p` is the paper's `⌈(n + f + 1)/2⌉`; and the three remaining
results order the thresholds `spQuorum ≤ quorumCard ≤ fastCard`, which is
what lets a fast commit be read as a slow-path quorum wherever the slow
path's arguments are wanted.

`Model/Params.lean` defines the committee; this file is what may be
deduced from it.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]

/-- **The standing arithmetic of the committee**, in the form `omega`
consumes it: the correct and Byzantine sets partition the validators, at
most `f` are Byzantine, `1 ≤ p ≤ f`, and `n + 1 = 3f + 2p`. -/
theorem params_arith :
    (Correct : Finset Validator).card + F.byzantine.card = Fintype.card Validator ∧
      F.byzantine.card ≤ F.f ∧ 1 ≤ P.p ∧ P.p ≤ F.f ∧
      Fintype.card Validator + 1 = 3 * F.f + 2 * P.p :=
  ⟨card_correct_add_byzantine, F.card_byzantine, P.p_pos, P.p_le_f, P.card_add_one⟩

/-- The paper's `⌈(n+f+1)/2⌉` is `2f + p` at this committee. -/
theorem spQuorum_eq_ceil :
    spQuorum Validator = (Fintype.card Validator + F.f + 1 + 1) / 2 := by
  have := P.card_add_one
  simp only [spQuorum]
  omega

/-- The fast-path threshold clears the slow-path quorum, so a fast commit
carries a quorum of votes with it. This is what lets the slow-path
arguments be reused against a fast commit. -/
theorem spQuorum_le_fastCard : spQuorum Validator ≤ fastCard Validator := by
  have := params_arith (Validator := Validator)
  have hle : P.p ≤ Fintype.card Validator := by
    have := Finset.card_le_univ (F.byzantine)
    omega
  simp only [spQuorum, fastCard]
  omega

/-- **The slow-path quorum is below the parent threshold.** `n − f` is
`2f + 2p − 1` at this committee and `spQuorum` is `2f + p`, so at `p ≥ 2`
a block's parent set is strictly larger than an SP-certificate quorum.
The two coincide only at `p = 1`, where FinWhale's committee is the
core's. Every argument that intersects a parent set with a quorum uses
this direction. -/
theorem spQuorum_le_quorumCard : spQuorum Validator ≤ quorumCard Validator := by
  have := params_arith (Validator := Validator)
  simp only [spQuorum]
  omega

/-- The parent threshold is itself below the fast-path threshold, since
`p ≤ f`. -/
theorem quorumCard_le_fastCard : quorumCard Validator ≤ fastCard Validator := by
  have := params_arith (Validator := Validator)
  have hle : P.p ≤ Fintype.card Validator := by
    have := Finset.card_le_univ (F.byzantine)
    omega
  simp only [fastCard]
  omega

end FinWhale

end LeanDag
