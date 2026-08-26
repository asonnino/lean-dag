import LeanDag.Minnow.Model.Rule

/-!
# Minnow — what blocks `crs*`

Two facts, and no more than the counterexamples need (`minnow.md` §2).
A commit under `Ps*` requires a quorum, so a vertex without one is never
committed however the recursion runs; and a slot whose every vertex is
out of the candidate's causal past, without a quorum and unskippable, can
never be resolved, so no leader after it commits.

Both are read straight off Definition 9. Neither is an approximation.
-/

namespace LeanDag

namespace Minnow

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload} {L : ℕ → Slot Validator}

/-- **A commit needs a quorum**, at every position in `leaders`. -/
theorem quorum_of_committedAt : ∀ {k : ℕ} {l : BlockId}, CommittedAt D L k l → Quorum D l
  | 0, _, h => by simpa only [CommittedAt] using h
  | (_ + 1), _, h => by simp only [CommittedAt] at h; exact h.1

/-- **A vertex with no quorum is never committed.** -/
theorem not_committedAt_of_not_quorum {k : ℕ} {l : BlockId} (h : ¬ Quorum D l) :
    ¬ CommittedAt D L k l := fun hc => h (quorum_of_committedAt hc)

/-- **A dead slot blocks every later leader.** If every vertex of the
`j`-th leader slot lies outside `l`'s causal past, carries no quorum and
cannot be skipped, then the second clause of `Φ*s` is unsatisfiable for
`l`, whatever the recursion decides elsewhere. -/
theorem not_committedAt_of_dead {k j : ℕ} (hj : j ≤ k) {l : BlockId}
    (h : ∀ v ∈ slotBlocks D (L j), ¬ Reaches D l v ∧ ¬ Quorum D v ∧ ¬ Skipped D v) :
    ¬ CommittedAt D L (k + 1) l := by
  intro hc
  simp only [CommittedAt] at hc
  obtain ⟨v, hv, hcase⟩ := hc.2 j hj
  obtain ⟨hnr, hnq, hns⟩ := h v hv
  rcases hcase with hr | ⟨-, hc | hs⟩
  · exact hnr hr
  · exact hnq (quorum_of_committedAt hc)
  · exact hns hs

end Minnow

end LeanDag
