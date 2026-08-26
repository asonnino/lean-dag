import LeanDag.Validators

/-!
# FinWhale — the committee, and the two thresholds it fixes

FinWhale [LF26] adds a two-round fast path to Mysticeti's commit rule. The
fast path costs resilience, and the paper pays for it in the committee
size: `n = 3f + 2p − 1`, where `f` is the fault bound as usual and `p` is
the number of validators that may misbehave *during the fast path*
without costing fast termination, with `1 ≤ p ≤ f`. Setting `p = f`
recovers `n = 5f − 1`; `p = 1` gives `n = 3f + 1`, the core's committee.

Two thresholds follow, and every counting argument of the arc is about
one of them.

* The **slow-path quorum** is the paper's `⌈(n+f+1)/2⌉`, which at this
  committee is exactly `2f + p`. `spQuorum` is written as that closed
  form, and `spQuorum_eq_ceil` checks the two agree.
* The **fast-path threshold** is `n − p`, the number of distinct
  round-`(r+1)` voters a leader block needs to commit in two rounds.

`Params` is a class on top of `Faults` rather than a replacement for it:
`n = 3f + 2p − 1` with `p ≥ 1` implies `n ≥ 3f + 1`, so a FinWhale
committee is a core committee and everything proved of `Faults` applies
unchanged (`card_validators` is re-derivable, and `params_arith` hands
`omega` the rest).

The committee equation is stated **additively**, as `n + 1 = 3f + 2p`,
so that no truncated subtraction ever reaches `omega`.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]

/-- **FinWhale's committee.** `n = 3f + 2p − 1`, with `1 ≤ p ≤ f`. -/
class Params (Validator : Type*) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] where
  /-- The fast-path fault budget. -/
  p : ℕ
  /-- At least one validator may misbehave on the fast path. -/
  p_pos : 1 ≤ p
  /-- The fast-path budget does not exceed the fault bound. -/
  p_le_f : p ≤ F.f
  /-- `n = 3f + 2p − 1`, written additively. -/
  card_add_one : Fintype.card Validator + 1 = 3 * F.f + 2 * p

variable [F : Faults Validator] [P : Params Validator]

/-- The slow-path quorum, the paper's `⌈(n+f+1)/2⌉`. -/
def spQuorum (Validator : Type*) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Params Validator] : ℕ :=
  2 * Faults.f Validator + Params.p Validator

/-- The fast-path threshold: `n − p` distinct voters one round above. -/
def fastCard (Validator : Type*) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [Params Validator] : ℕ :=
  Fintype.card Validator - Params.p Validator

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
