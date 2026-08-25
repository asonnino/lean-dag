import LeanDag.BlackMarlin.Model.Repair
import LeanDag.BlackMarlin.Helpers.Descent

/-!
# Black Marlin — the repair layer

Generated proof layer; not part of the audit surface. At most one
candidate of a step is supported, the repaired descent takes it where
there is one, and two support-preferring records cannot part at a round
that has one. The repair changes which block a step returns and never
whether it returns one, nor at which round.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {B L : BlockId} {ρ : ℕ}

theorem mem_suppCandidates {A : BlockId} :
    A ∈ suppCandidates U B ↔
      A ∈ maxAnchor U (strongOf U B) ∧ Supported U A (U.block A).round :=
  Finset.mem_filter

/-- **At most one candidate is supported.** The candidates of a step
share a round, and an anchor round has one supported anchor (BM1) — so
where the filter bites there is nothing left to break ties over. -/
theorem suppCandidates_subsingleton :
    ∀ A ∈ suppCandidates U B, ∀ C ∈ suppCandidates U B, A = C := by
  intro A hA C hC
  obtain ⟨hAmax, hAs⟩ := mem_suppCandidates.mp hA
  obtain ⟨hCmax, hCs⟩ := mem_suppCandidates.mp hC
  have hAr := (mem_maxAnchor.mp hAmax).2
  have hCr := (mem_maxAnchor.mp hCmax).2
  have hcr : (U.block A).creator = (U.block C).creator := by
    have hAa := (mem_anchorsOf.mp (mem_maxAnchor.mp hAmax).1).2
    have hCa := (mem_anchorsOf.mp (mem_maxAnchor.mp hCmax).1).2
    unfold IsAnchorBlock at hAa hCa
    rw [hAa, hCa, hAr, hCr]
  exact eq_of_supported hAs (by rw [hCr, ← hAr] at hCs; exact hCs) hcr

/-- **The repaired choice is supported where one is.** -/
theorem descendSupp_supported (h : descendSupp U B = some L)
    (hne : (suppCandidates U B).Nonempty) : Supported U L (U.block L).round := by
  rw [descendSupp, if_pos hne] at h
  exact (mem_suppCandidates.mp (pick_mem h)).2

/-- The repaired choice is still a candidate of the step, so everything
`descend` guarantees of its result holds of this one. -/
theorem descendSupp_mem (h : descendSupp U B = some L) :
    L ∈ maxAnchor U (strongOf U B) := by
  rw [descendSupp] at h
  split at h
  · exact (mem_suppCandidates.mp (pick_mem h)).1
  · exact descend_mem h

theorem descendSupp_mem_ids (hB : B ∈ U.ids) (h : descendSupp U B = some L) : L ∈ U.ids :=
  history_subset_ids hB (mem_strongOf.mp (mem_anchorsOf.mp (mem_maxAnchor.mp
    (descendSupp_mem h)).1).1).2

theorem descendSupp_round_lt (hB : B ∈ U.ids) (h : descendSupp U B = some L) :
    (U.block L).round < (U.block B).round := by
  obtain ⟨hne, hhist⟩ :=
    mem_strongOf.mp (mem_anchorsOf.mp (mem_maxAnchor.mp (descendSupp_mem h)).1).1
  rcases Nat.lt_or_ge (U.block L).round (U.block B).round with hlt | hge
  · exact hlt
  · exact absurd (eq_of_mem_history_of_round_eq hB hhist
      (le_antisymm (round_le_of_mem_history hB hhist) hge)) hne

/-! ## What the repair costs

Nothing structural. The step still returns a block exactly when the
unrepaired one does, and always at the same round, so the rounds a record
flushes at are unchanged and the descent still exhausts. Only *which*
block a step returns can differ. -/

/-- **The repair never stalls the descent.** -/
theorem descendSupp_isSome_iff :
    (descendSupp U B).isSome ↔ (descend U B).isSome := by
  rw [descendSupp]
  split
  · rename_i hne
    constructor
    · intro _
      exact descend_isSome ⟨hne.choose,
        (mem_maxAnchor.mp (mem_suppCandidates.mp hne.choose_spec).1).1⟩
    · intro _; exact pick_isSome hne
  · exact Iff.rfl

/-- **And never moves a step to another round.** -/
theorem descendSupp_round_eq {L' : BlockId} (h : descendSupp U B = some L)
    (h' : descend U B = some L') : (U.block L).round = (U.block L').round := by
  rw [(mem_maxAnchor.mp (descendSupp_mem h)).2, (mem_maxAnchor.mp (descend_mem h')).2]

/-- **Where no candidate is supported, the repair is the original
rule.** So it refines L21–L24 rather than replacing it. -/
theorem descendSupp_eq_descend (h : ¬ (suppCandidates U B).Nonempty) :
    descendSupp U B = descend U B := by
  rw [descendSupp, if_neg h]

/-! ## What the repair buys -/

/-- **Two support-preferring records cannot part at a supported round.**
The whole content of the repair: BM1 makes the supported anchor of a
round unique, and the side-condition puts both records on it. -/
theorem eq_of_supportPreferring {f₁ f₂ : Flush U} {L₁ L₂ : BlockId}
    (hp₁ : SupportPreferring U f₁) (hp₂ : SupportPreferring U f₂)
    (h₁ : f₁.block ρ = some L₁) (h₂ : f₂.block ρ = some L₂)
    (hex : ∃ A, IsAnchor U ρ A ∧ Supported U A ρ) : L₁ = L₂ :=
  eq_of_isAnchor_of_supported (f₁.isAnchor ρ L₁ h₁) (f₂.isAnchor ρ L₂ h₂)
    (hp₁ ρ L₁ h₁ hex) (hp₂ ρ L₂ h₂ hex)

/-- And so they agree there. -/
theorem block_eq_of_supportPreferring {f₁ f₂ : Flush U}
    (hp₁ : SupportPreferring U f₁) (hp₂ : SupportPreferring U f₂)
    (hs₁ : (f₁.block ρ).isSome) (hs₂ : (f₂.block ρ).isSome)
    (hex : ∃ A, IsAnchor U ρ A ∧ Supported U A ρ) :
    f₁.block ρ = f₂.block ρ := by
  obtain ⟨L₁, h₁⟩ := Option.isSome_iff_exists.mp hs₁
  obtain ⟨L₂, h₂⟩ := Option.isSome_iff_exists.mp hs₂
  rw [h₁, h₂, eq_of_supportPreferring hp₁ hp₂ h₁ h₂ hex]

end BlackMarlin

end LeanDag
