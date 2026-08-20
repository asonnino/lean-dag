import LeanDag.MahiMahi.Model.Decision
import LeanDag.MahiMahi.Helpers.Rules

/-!
# Helpers — the decision layer

Generated lemma infrastructure for `Model/Decision.lean`; not part of the
audit surface. View lifting, the direct-versus-indirect agreement lemmas
at wave `w` (the core's M4 and M5 in their slot-indexed forms), the
anchor round bound, and the wave-three correspondences the
conservativity claims consume.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## A view can only under-report -/

theorem directCommit_of_directCommitIn {V : View Validator BlockId Payload U}
    {w : ℕ} {L : BlockId} {r : ℕ} (h : DirectCommitIn U V w L r) : DirectCommit U w L r :=
  le_trans h (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

theorem directSkip_of_directSkipIn {V : View Validator BlockId Payload U}
    {w : ℕ} {a : Validator} {r : ℕ} (h : DirectSkipIn U V w a r) : DirectSkip U w a r :=
  le_trans h (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

theorem certificates_nonempty_of_certifiedIn {w : ℕ} {A L : BlockId} {r : ℕ}
    (h : CertifiedIn U w A L r) : (certificates U w L r).Nonempty := by
  obtain ⟨C, hC, -⟩ := h
  exact ⟨C, hC⟩

/-- The commit half of M4: a directly committed candidate is certified in
the cone of every block above its decision round. -/
theorem certifiedIn_of_directCommit {w : ℕ} {L : BlockId} {r : ℕ} (h : DirectCommit U w L r)
    {A : BlockId} (hA : A ∈ U.ids) (hAr : decisionRoundAt w r + 1 ≤ (U.block A).round) :
    CertifiedIn U w A L r :=
  exists_certificate_reaches_of_directCommit h hA hAr

/-- The skip half of M4: a skipped slot's candidates are certified nowhere. -/
theorem not_certifiedIn_of_directSkip {w : ℕ} {a : Validator} {r : ℕ} {L : BlockId}
    (hw : 2 ≤ w) (h : DirectSkip U w a r)
    (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r) {A : BlockId} :
    ¬ CertifiedIn U w A L r := by
  intro hc
  have hne := certificates_nonempty_of_certifiedIn hc
  rw [certificates_eq_empty_of_directSkip hw h hLc hLr] at hne
  exact Finset.not_nonempty_empty hne

section Slots

variable [S : Slots Validator]

omit [Fintype Validator] [DecidableEq Validator] F in
theorem decisionRound_eq (w k : ℕ) :
    decisionRound Validator w k = decisionRoundAt w (S.slotRound k) := rfl

omit [LinearOrder BlockId] in
/-- An eligible anchor's block sits above the slot's decision round. -/
theorem anchor_round {w k j : ℕ} {A : BlockId} (hA : IsLeaderBlock U j A)
    (helig : Eligible Validator w k j) :
    decisionRoundAt w (S.slotRound k) + 1 ≤ (U.block A).round := by
  rw [hA.2.1]
  unfold Eligible at helig
  rw [decisionRound_eq] at helig
  omega

theorem isLeaderBlock_of_decided {w : ℕ} {V : View Validator BlockId Payload U} {j : ℕ}
    {A : BlockId} (h : Decided w U V j (some A)) : IsLeaderBlock U j A := by
  cases h with
  | directCommit hL _ => exact hL
  | indirectCommit _ _ _ _ hL _ => exact hL

/-- Two candidates of one slot with certificates coincide. -/
theorem eq_of_hasCertificate {w k : ℕ} {L₁ L₂ : BlockId} (hw : 2 ≤ w)
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : (certificates U w L₁ (S.slotRound k)).Nonempty)
    (h₂ : (certificates U w L₂ (S.slotRound k)).Nonempty) : L₁ = L₂ :=
  eq_of_certificates_nonempty hw h₁ h₂ (by rw [hL₁.2.2, hL₂.2.2]) (by rw [hL₁.2.1, hL₂.2.1])

theorem eq_of_directCommitIn {w : ℕ} {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {L₁ L₂ : BlockId} (hw : 2 ≤ w)
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V₁ w L₁ (S.slotRound k))
    (h₂ : DirectCommitIn U V₂ w L₂ (S.slotRound k)) : L₁ = L₂ :=
  eq_of_hasCertificate hw hL₁ hL₂
    (certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h₁))
    (certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h₂))

/-- A committed candidate's slot is not skipped, across views. -/
theorem not_directSkipIn_of_directCommitIn {w : ℕ} {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L : BlockId} (hw : 2 ≤ w) (hL : IsLeaderBlock U k L)
    (h₁ : DirectCommitIn U V₁ w L (S.slotRound k))
    (h₂ : DirectSkipIn U V₂ w (S.leader k) (S.slotRound k)) : False := by
  have hne := certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h₁)
  rw [certificates_eq_empty_of_directSkip hw (directSkip_of_directSkipIn h₂) hL.2.2 hL.2.1] at hne
  exact Finset.not_nonempty_empty hne

/-- A direct commit is seen from any eligible anchor. -/
theorem certifiedIn_of_directCommitIn_at_anchor {w : ℕ}
    {V W : View Validator BlockId Payload U} {k j : ℕ} {L A : BlockId}
    (h : DirectCommitIn U V w L (S.slotRound k))
    (hj : Decided w U W j (some A)) (helig : Eligible Validator w k j) :
    CertifiedIn U w A L (S.slotRound k) :=
  certifiedIn_of_directCommit (directCommit_of_directCommitIn h)
    (isLeaderBlock_of_decided hj).1 (anchor_round (isLeaderBlock_of_decided hj) helig)

/-- **Agreement** (the core's M6 at wave `w`): structural induction on the
first derivation; the one real case compares anchors through the core's
`anchor_eq`. -/
theorem decided_unique {w : ℕ} (hw : 2 ≤ w) {V₁ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ : Option BlockId} (h₁ : Decided w U V₁ k v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided w U V₂ k v₂ → v₁ = v₂ := by
  induction h₁ with
  | @directCommit k L hL h =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ => exact congrArg some (eq_of_directCommitIn hw hL hL₂ h h₂)
    | directSkip hskip => exact absurd (not_directSkipIn_of_directCommitIn hw hL h hskip) not_false
    | indirectCommit _ _ _ _ hL₂ hcert₂ =>
      exact congrArg some (eq_of_hasCertificate hw hL hL₂
        (certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h))
        (certificates_nonempty_of_certifiedIn hcert₂))
    | @indirectSkip _ j A _ helig hj _ hnone =>
      exact absurd (certifiedIn_of_directCommitIn_at_anchor h hj helig) (hnone _ hL)
  | @directSkip k hskip =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact absurd (not_directSkipIn_of_directCommitIn hw hL₂ h₂ hskip) not_false
    | directSkip _ => rfl
    | indirectCommit _ _ _ _ hL₂ hcert₂ =>
      exact absurd hcert₂
        (not_certifiedIn_of_directSkip hw (directSkip_of_directSkipIn hskip) hL₂.2.2 hL₂.2.1)
    | indirectSkip _ _ _ _ _ => rfl
  | @indirectCommit k j A L hkj helig hj hmid hL hcert ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact congrArg some (eq_of_hasCertificate hw hL hL₂
        (certificates_nonempty_of_certifiedIn hcert)
        (certificates_nonempty_of_directCommit (directCommit_of_directCommitIn h₂)))
    | directSkip hskip₂ =>
      exact absurd hcert
        (not_certifiedIn_of_directSkip hw (directSkip_of_directSkipIn hskip₂) hL.2.2 hL.2.1)
    | indirectCommit _ _ _ _ hL₂ hcert₂ =>
      exact congrArg some (eq_of_hasCertificate hw hL hL₂
        (certificates_nonempty_of_certifiedIn hcert)
        (certificates_nonempty_of_certifiedIn hcert₂))
    | @indirectSkip _ j₂ A₂ hkj₂ helig₂ hj₂ hmid₂ hnone₂ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact absurd hcert (hnone₂ _ hL)
  | @indirectSkip k j A hkj helig hj hmid hnone ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact absurd (certifiedIn_of_directCommitIn_at_anchor h₂ hj helig) (hnone _ hL₂)
    | directSkip _ => rfl
    | @indirectCommit _ j₂ A₂ L₂ hkj₂ helig₂ hj₂ hmid₂ hL₂ hcert₂ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact absurd hcert₂ (hnone _ hL₂)
    | indirectSkip _ _ _ _ _ => rfl

/-! ## Wave three is the core's relation -/

omit [Fintype Validator] [DecidableEq Validator] F in
theorem eligible_three_iff {k j : ℕ} :
    Eligible Validator 3 k j ↔ LeanDag.Eligible Validator k j := by
  unfold Eligible decisionRound LeanDag.Eligible LeanDag.decisionRound
  omega

omit S in
theorem certifiedIn_three_iff {A L : BlockId} {r : ℕ} (hLr : (U.block L).round = r) :
    CertifiedIn U 3 A L r ↔ LeanDag.CertifiedIn U A L r := by
  unfold CertifiedIn LeanDag.CertifiedIn
  rw [certificates_eq_of_three hLr]

omit S in
theorem directCommitIn_three_iff {V : View Validator BlockId Payload U} {L : BlockId} {r : ℕ}
    (hLr : (U.block L).round = r) :
    DirectCommitIn U V 3 L r ↔ LeanDag.DirectCommitIn U V L r := by
  unfold DirectCommitIn LeanDag.DirectCommitIn certificatesIn LeanDag.certificatesIn
  rw [certificates_eq_of_three hLr]

omit S in
/-- A blame of the slot in view is a blame of each candidate in view. -/
theorem core_directSkipIn_of_directSkipIn {V : View Validator BlockId Payload U}
    {a : Validator} {r : ℕ} {L : BlockId} (h : DirectSkipIn U V 3 a r)
    (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r) :
    LeanDag.DirectSkipIn U V L r := by
  refine le_trans h (Finset.card_le_card (Finset.image_subset_image ?_))
  intro q hq
  rw [votingRound_three] at hq
  rw [Finset.mem_inter, Finset.mem_filter] at hq ⊢
  obtain ⟨⟨hqb, hqblame⟩, hqV⟩ := hq
  exact ⟨⟨hqb, not_mem_refs_of_blames (mem_blocksAt.mp hqb).1 hqblame hLc hLr⟩, hqV⟩

/-- At wave three every derivation is a derivation of the core's relation. -/
theorem core_decided_of_decided {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId} (h : Decided 3 U V k v) : LeanDag.Decided U V k v := by
  induction h with
  | @directCommit k L hL h =>
    exact LeanDag.Decided.directCommit hL ((directCommitIn_three_iff hL.2.1).mp h)
  | @directSkip k hskip =>
    exact LeanDag.Decided.directSkip
      (fun L hL => core_directSkipIn_of_directSkipIn hskip hL.2.2 hL.2.1)
  | @indirectCommit k j A L hkj helig hj hmid hL hcert ihj ihmid =>
    exact LeanDag.Decided.indirectCommit hkj (eligible_three_iff.mp helig) ihj
      (fun i h1 h2 he => ihmid i h1 h2 (eligible_three_iff.mpr he)) hL
      ((certifiedIn_three_iff hL.2.1).mp hcert)
  | @indirectSkip k j A hkj helig hj hmid hnone ihj ihmid =>
    exact LeanDag.Decided.indirectSkip hkj (eligible_three_iff.mp helig) ihj
      (fun i h1 h2 he => ihmid i h1 h2 (eligible_three_iff.mpr he))
      (fun L hL hc => hnone L hL ((certifiedIn_three_iff hL.2.1).mpr hc))

end Slots

end MahiMahi

end LeanDag
