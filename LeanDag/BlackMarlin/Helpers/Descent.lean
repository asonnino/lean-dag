import LeanDag.BlackMarlin.Model.Descent
import LeanDag.BlackMarlin.Helpers.Ledger

/-!
# Black Marlin — the descent layer

Generated proof layer; not part of the audit surface. The descent of
`commit` computed rather than assumed: its choice is sound and total
where an anchor lies below, the record it generates is a `Flush`, and
below any round two records both flush at they agree — with no
definedness hypothesis, because each value is a function of the one
above.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {B A M : BlockId} {ρ σ : ℕ} {s : Finset BlockId}

theorem mem_anchorsOf {X : BlockId} :
    X ∈ anchorsOf U s ↔ X ∈ s ∧ IsAnchorBlock U X := Finset.mem_filter

theorem mem_strongOf {X : BlockId} :
    X ∈ strongOf U B ↔ X ≠ B ∧ X ∈ history U B := Finset.mem_erase

theorem mem_maxAnchor {X : BlockId} :
    X ∈ maxAnchor U s ↔ X ∈ anchorsOf U s ∧ (U.block X).round = maxAnchorRound U s :=
  Finset.mem_filter

/-- No anchor of a set sits above its highest anchor round. -/
theorem le_maxAnchorRound {X : BlockId} (h : X ∈ anchorsOf U s) :
    (U.block X).round ≤ maxAnchorRound U s :=
  Finset.le_sup (f := fun Y => (U.block Y).round) h

/-- A set holding an anchor holds one at its highest anchor round. -/
theorem maxAnchor_nonempty (h : (anchorsOf U s).Nonempty) : (maxAnchor U s).Nonempty := by
  obtain ⟨b, hb, hsup⟩ := Finset.exists_mem_eq_sup (anchorsOf U s) h (fun X => (U.block X).round)
  exact ⟨b, mem_maxAnchor.mpr ⟨hb, hsup.symm⟩⟩

theorem pick_mem {t : Finset BlockId} (h : pick t = some A) : A ∈ t := by
  unfold pick at h
  split at h
  · rename_i hne
    rw [← Option.some.inj h]
    exact Finset.min'_mem t hne
  · exact absurd h (by simp)

theorem pick_isSome {t : Finset BlockId} (h : t.Nonempty) : (pick t).isSome := by
  unfold pick
  rw [dif_pos h]
  rfl

/-- **The descent's choice is one of the candidates.** -/
theorem descend_mem (h : descend U B = some A) : A ∈ maxAnchor U (strongOf U B) :=
  (Finset.mem_filter.mp (pick_mem h)).1

/-- **And it makes one whenever an anchor lies below.** The gap-minimal
survivors of a nonempty candidate set are themselves nonempty. -/
theorem descend_isSome (h : (anchorsOf U (strongOf U B)).Nonempty) :
    (descend U B).isSome := by
  obtain ⟨A, hA, hmin⟩ :=
    Finset.exists_min_image (maxAnchor U (strongOf U B)) (anchorGap U) (maxAnchor_nonempty h)
  exact pick_isSome ⟨A, Finset.mem_filter.mpr ⟨hA, hmin⟩⟩

/-- The chosen block sits at the highest anchor round below. -/
theorem round_descend (h : descend U B = some A) :
    (U.block A).round = maxAnchorRound U (strongOf U B) :=
  (mem_maxAnchor.mp (descend_mem h)).2

theorem descend_mem_ids (hB : B ∈ U.ids) (h : descend U B = some A) : A ∈ U.ids :=
  history_subset_ids hB (mem_strongOf.mp (mem_anchorsOf.mp (mem_maxAnchor.mp
    (descend_mem h)).1).1).2

/-- **A step drops the round strictly**, which is what makes the fuelled
descent exhaust. -/
theorem descend_round_lt (hB : B ∈ U.ids) (h : descend U B = some A) :
    (U.block A).round < (U.block B).round := by
  obtain ⟨hne, hhist⟩ :=
    mem_strongOf.mp (mem_anchorsOf.mp (mem_maxAnchor.mp (descend_mem h)).1).1
  rcases Nat.lt_or_ge (U.block A).round (U.block B).round with hlt | hge
  · exact hlt
  · exact absurd (eq_of_mem_history_of_round_eq hB hhist
      (le_antisymm (round_le_of_mem_history hB hhist) hge)) hne

/-! ## The fuelled descent -/

/-- A round-`0` block reaches only itself. -/
theorem strongOf_eq_empty_of_round_zero (hB : B ∈ U.ids) (h0 : (U.block B).round = 0) :
    strongOf U B = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro X hX
  obtain ⟨hne, hhist⟩ := mem_strongOf.mp hX
  exact hne (eq_of_mem_history_of_round_eq hB hhist
    (by have := round_le_of_mem_history hB hhist; omega))

/-- So the descent bottoms out there. -/
theorem descend_eq_none_of_round_zero (hB : B ∈ U.ids) (h0 : (U.block B).round = 0) :
    descend U B = none := by
  cases h : descend U B with
  | none => rfl
  | some A =>
      exact absurd (mem_anchorsOf.mp (mem_maxAnchor.mp (descend_mem h)).1).1
        (by rw [strongOf_eq_empty_of_round_zero hB h0]; simp)

/-- What the record holds at a round sits at that round. -/
theorem descentUpto_round : ∀ (n : ℕ) (B : BlockId) (ρ : ℕ) (A : BlockId),
    descentUpto U n B ρ = some A → (U.block A).round = ρ := by
  intro n
  induction n with
  | zero =>
      intro B ρ A h
      simp only [descentUpto] at h
      split at h
      · rename_i hbr; rw [← Option.some.inj h]; exact hbr
      · exact absurd h (by simp)
  | succ n ih =>
      intro B ρ A h
      simp only [descentUpto] at h
      split at h
      · rename_i hbr; rw [← Option.some.inj h]; exact hbr
      · cases hd : descend U B with
        | none => rw [hd] at h; exact absurd h (by simp)
        | some C => rw [hd, Option.bind_some] at h; exact ih C ρ A h

/-- And is a block of the universe. -/
theorem descentUpto_mem_ids : ∀ (n : ℕ) (B : BlockId), B ∈ U.ids →
    ∀ (ρ : ℕ) (A : BlockId), descentUpto U n B ρ = some A → A ∈ U.ids := by
  intro n
  induction n with
  | zero =>
      intro B hB ρ A h
      simp only [descentUpto] at h
      split at h
      · rw [← Option.some.inj h]; exact hB
      · exact absurd h (by simp)
  | succ n ih =>
      intro B hB ρ A h
      simp only [descentUpto] at h
      split at h
      · rw [← Option.some.inj h]; exact hB
      · cases hd : descend U B with
        | none => rw [hd] at h; exact absurd h (by simp)
        | some C =>
            rw [hd, Option.bind_some] at h
            exact ih C (descend_mem_ids hB hd) ρ A h

/-- And, below the top, anchors its round. -/
theorem descentUpto_isAnchorBlock : ∀ (n : ℕ) (B : BlockId), B ∈ U.ids →
    IsAnchorBlock U B → ∀ (ρ : ℕ) (A : BlockId),
    descentUpto U n B ρ = some A → IsAnchorBlock U A := by
  intro n
  induction n with
  | zero =>
      intro B hB haB ρ A h
      simp only [descentUpto] at h
      split at h
      · rw [← Option.some.inj h]; exact haB
      · exact absurd h (by simp)
  | succ n ih =>
      intro B hB haB ρ A h
      simp only [descentUpto] at h
      split at h
      · rw [← Option.some.inj h]; exact haB
      · cases hd : descend U B with
        | none => rw [hd] at h; exact absurd h (by simp)
        | some C =>
            rw [hd, Option.bind_some] at h
            exact ih C (descend_mem_ids hB hd)
              (mem_anchorsOf.mp (mem_maxAnchor.mp (descend_mem hd)).1).2 ρ A h

/-- The descent never rises. -/
theorem descentUpto_round_le : ∀ (n : ℕ) (B : BlockId), B ∈ U.ids →
    ∀ (ρ : ℕ) (A : BlockId), descentUpto U n B ρ = some A →
    (U.block A).round ≤ (U.block B).round := by
  intro n
  induction n with
  | zero =>
      intro B hB ρ A h
      simp only [descentUpto] at h
      split at h
      · rw [← Option.some.inj h]
      · exact absurd h (by simp)
  | succ n ih =>
      intro B hB ρ A h
      simp only [descentUpto] at h
      split at h
      · rw [← Option.some.inj h]
      · cases hd : descend U B with
        | none => rw [hd] at h; exact absurd h (by simp)
        | some C =>
            rw [hd, Option.bind_some] at h
            have := ih C (descend_mem_ids hB hd) ρ A h
            have := descend_round_lt hB hd
            omega

/-- **Fuel beyond the block's round changes nothing**: a step drops the
round strictly, so the descent has exhausted itself by then. -/
theorem descentUpto_succ_eq : ∀ (n : ℕ) (B : BlockId), B ∈ U.ids →
    (U.block B).round ≤ n → ∀ ρ, descentUpto U n B ρ = descentUpto U (n + 1) B ρ := by
  intro n
  induction n with
  | zero =>
      intro B hB hr ρ
      by_cases hbr : (U.block B).round = ρ
      · simp [descentUpto, hbr]
      · simp only [descentUpto, if_neg hbr]
        rw [descend_eq_none_of_round_zero hB (by omega)]
        rfl
  | succ n ih =>
      intro B hB hr ρ
      by_cases hbr : (U.block B).round = ρ
      · simp [descentUpto, hbr]
      · simp only [descentUpto, if_neg hbr]
        cases hd : descend U B with
        | none => rfl
        | some C =>
            simp only [Option.bind_some]
            exact ih C (descend_mem_ids hB hd)
              (by have := descend_round_lt hB hd; omega) ρ

theorem descentUpto_add : ∀ (k m : ℕ) (B : BlockId), B ∈ U.ids →
    (U.block B).round ≤ m → ∀ ρ, descentUpto U m B ρ = descentUpto U (m + k) B ρ := by
  intro k
  induction k with
  | zero => intro m B _ _ ρ; rfl
  | succ k ih =>
      intro m B hB hr ρ
      rw [ih m B hB hr ρ, show m + (k + 1) = (m + k) + 1 by omega]
      exact descentUpto_succ_eq (m + k) B hB (by omega) ρ

theorem descentUpto_eq_of_le {m n : ℕ} (hB : B ∈ U.ids) (hr : (U.block B).round ≤ m)
    (hmn : m ≤ n) (ρ : ℕ) : descentUpto U m B ρ = descentUpto U n B ρ := by
  have := descentUpto_add (n - m) m B hB hr ρ
  rwa [show m + (n - m) = n by omega] at this

/-- The record with the fuel its own round supplies. -/
theorem flushRecord_eq (hB : B ∈ U.ids) {n : ℕ} (hn : (U.block B).round ≤ n) (ρ : ℕ) :
    flushRecord U B ρ = descentUpto U n B ρ :=
  descentUpto_eq_of_le hB (le_refl _) hn ρ

/-! ## The suffix property -/

theorem descentUpto_suffix : ∀ (n : ℕ) (B : BlockId), B ∈ U.ids →
    (U.block B).round ≤ n → ∀ (σ : ℕ) (M : BlockId), descentUpto U n B σ = some M →
    ∀ ρ, ρ ≤ σ → descentUpto U n B ρ = descentUpto U n M ρ := by
  intro n
  induction n with
  | zero =>
      intro B hB hr σ M h ρ hρ
      simp only [descentUpto] at h
      split at h
      · rw [← Option.some.inj h]
      · exact absurd h (by simp)
  | succ n ih =>
      intro B hB hr σ M h ρ hρ
      by_cases hbr : (U.block B).round = σ
      · rw [show M = B from (Option.some.inj (by rwa [descentUpto, if_pos hbr] at h)).symm]
      · rw [descentUpto, if_neg hbr] at h
        cases hd : descend U B with
        | none => rw [hd] at h; exact absurd h (by simp)
        | some C =>
            rw [hd, Option.bind_some] at h
            have hCids := descend_mem_ids hB hd
            have hClt := descend_round_lt hB hd
            have hMσ : (U.block M).round = σ := descentUpto_round n C σ M h
            have hMle : (U.block M).round ≤ (U.block C).round :=
              descentUpto_round_le n C hCids σ M h
            have hσlt : σ < (U.block B).round := by omega
            have hbρ : (U.block B).round ≠ ρ := by omega
            rw [descentUpto, if_neg hbρ, hd, Option.bind_some]
            rw [ih C hCids (by omega) σ M h ρ hρ]
            exact descentUpto_succ_eq n M (descentUpto_mem_ids n C hCids σ M h)
              (by omega) ρ

/-- **The record below a visited anchor is that anchor's own record.**
This is what makes the descent's agreement a consequence rather than a
hypothesis: below a block both records reached, both are the record of
that block. -/
theorem flushRecord_suffix (hB : B ∈ U.ids) {σ : ℕ} (h : flushRecord U B σ = some M)
    {ρ : ℕ} (hρ : ρ ≤ σ) : flushRecord U B ρ = flushRecord U M ρ := by
  have hMids : M ∈ U.ids := descentUpto_mem_ids _ B hB σ M h
  have hMσ : (U.block M).round = σ := descentUpto_round _ B σ M h
  have hσle : σ ≤ (U.block B).round := by
    have := descentUpto_round_le _ B hB σ M h
    omega
  rw [flushRecord, descentUpto_suffix _ B hB (le_refl _) σ M h ρ hρ]
  exact (flushRecord_eq hMids (by omega) ρ).symm

/-! ## The record is a `Flush`, and it agrees -/

theorem descentUpto_self (n : ℕ) (A : BlockId) :
    descentUpto U n A ((U.block A).round) = some A := by
  cases n <;> simp [descentUpto]

theorem flushRecord_isAnchor (hB : B ∈ U.ids) (haB : IsAnchorBlock U B)
    {ρ : ℕ} {L : BlockId} (h : flushRecord U B ρ = some L) : IsAnchor U ρ L := by
  refine ⟨descentUpto_mem_ids _ B hB ρ L h, descentUpto_round _ B ρ L h, ?_⟩
  have hanc := descentUpto_isAnchorBlock _ B hB haB ρ L h
  unfold IsAnchorBlock at hanc
  rwa [descentUpto_round _ B ρ L h] at hanc

/-- **The descent steps by one round when it can.** Where the record
holds blocks at `ρ` and `ρ + 1`, the lower is a reference of the higher —
`Flush.step`, derived rather than assumed. -/
theorem flushRecord_step (hB : B ∈ U.ids) {ρ : ℕ} {L M : BlockId}
    (hL : flushRecord U B ρ = some L) (hM : flushRecord U B (ρ + 1) = some M) :
    L ∈ (U.block M).refs := by
  have hMids : M ∈ U.ids := descentUpto_mem_ids _ B hB _ M hM
  have hMr : (U.block M).round = ρ + 1 := descentUpto_round _ B _ M hM
  rw [flushRecord_suffix hB hM (show ρ ≤ ρ + 1 by omega), flushRecord, hMr,
    descentUpto, if_neg (show ¬ ((U.block M).round = ρ) by rw [hMr]; omega)] at hL
  cases hd : descend U M with
  | none => rw [hd] at hL; exact absurd hL (by simp)
  | some C =>
      rw [hd, Option.bind_some] at hL
      have hCids := descend_mem_ids hMids hd
      have hClt := descend_round_lt hMids hd
      have hLr : (U.block L).round = ρ := descentUpto_round _ C ρ L hL
      have hLle := descentUpto_round_le _ C hCids ρ L hL
      have hCr : (U.block C).round = ρ := by omega
      have hCL : C = L := by
        rw [← hCr, descentUpto_self] at hL
        exact Option.some.inj hL
      obtain ⟨-, hCh⟩ := mem_strongOf.mp (mem_anchorsOf.mp (mem_maxAnchor.mp
        (descend_mem hd)).1).1
      rw [hCL] at hCh
      exact mem_refs_of_mem_history_of_round_succ hMids hCh (by omega)

/-- **And does not pass over an anchor it references** — `Flush.dense`,
also derived: an anchor of the round below is a candidate, and the
descent takes the highest round its candidates reach. -/
theorem flushRecord_dense (hB : B ∈ U.ids) {ρ : ℕ} {M : BlockId}
    (hM : flushRecord U B (ρ + 1) = some M) (hcone : (coneAnchors U M ρ).Nonempty) :
    (flushRecord U B ρ).isSome := by
  have hMids : M ∈ U.ids := descentUpto_mem_ids _ B hB _ M hM
  have hMr : (U.block M).round = ρ + 1 := descentUpto_round _ B _ M hM
  rw [flushRecord_suffix hB hM (show ρ ≤ ρ + 1 by omega), flushRecord, hMr,
    descentUpto, if_neg (show ¬ ((U.block M).round = ρ) by rw [hMr]; omega)]
  obtain ⟨X, hX⟩ := hcone
  obtain ⟨hXa, hXh⟩ := mem_coneAnchors.mp hX
  have hXstrong : X ∈ strongOf U M :=
    mem_strongOf.mpr ⟨by intro hEq; rw [hEq] at hXa; have := hXa.2.1; omega, hXh⟩
  have hXanc : IsAnchorBlock U X := by
    unfold IsAnchorBlock
    rw [hXa.2.1]
    exact hXa.2.2
  obtain ⟨C, hd⟩ := Option.isSome_iff_exists.mp
    (descend_isSome ⟨X, mem_anchorsOf.mpr ⟨hXstrong, hXanc⟩⟩)
  rw [hd, Option.bind_some]
  have hClt := descend_round_lt hMids hd
  have hCge : ρ ≤ (U.block C).round := by
    rw [round_descend hd, ← hXa.2.1]
    exact le_maxAnchorRound (mem_anchorsOf.mpr ⟨hXstrong, hXanc⟩)
  rw [show ρ = (U.block C).round by omega, descentUpto_self]
  rfl

/-- **The record of `commit(B)` is a flush record.** -/
def toFlush (U : BlockUniverse Validator BlockId Payload) (B : BlockId)
    (hB : B ∈ U.ids) (haB : IsAnchorBlock U B) : Flush U where
  block := flushRecord U B
  isAnchor := fun _ _ h => flushRecord_isAnchor hB haB h
  step := fun _ _ _ hL hM => flushRecord_step hB hL hM
  dense := fun _ _ hM hcone => flushRecord_dense hB hM hcone

/-- **Agreement, with no definedness hypothesis.** Two descents that
reach the same block at a round agree at every round below it: below that
block both records *are* its record. This is what `Ledger`'s BMD3 has to
assume of an abstract record and what the descent supplies. -/
theorem flushRecord_agree {B₁ B₂ : BlockId} (h₁ : B₁ ∈ U.ids) (h₂ : B₂ ∈ U.ids)
    {σ : ℕ} {M : BlockId}
    (hm₁ : flushRecord U B₁ σ = some M) (hm₂ : flushRecord U B₂ σ = some M)
    {ρ : ℕ} (hρ : ρ ≤ σ) : flushRecord U B₁ ρ = flushRecord U B₂ ρ := by
  rw [flushRecord_suffix h₁ hm₁ hρ, flushRecord_suffix h₂ hm₂ hρ]

end BlackMarlin

end LeanDag
