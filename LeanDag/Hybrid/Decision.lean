import LeanDag.Hybrid.Rules

/-!
# The hybrid decision relation, and agreement

The Odontoceti decision layer at the hybrid thresholds: two-round
eligibility, the view-relative direct rules at `q`, the decision
relation with the canonicity clause — retained unchanged, since a
*Byzantine* leader can still plant two passing candidates in one
anchor's cone, and nothing about the crash class closes that gap — and
agreement (H6), by the same sixteen-case induction as O5 and M6, with
`anchor_eq` consumed as found.

Every agreement-side theorem threads `HonestNoEquiv` and the
admissible-interval hypotheses for the indirect threshold `k`; the
relation itself is a definition and carries neither.
-/

namespace LeanDag

namespace Hybrid

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {L A : BlockId} {r k : ℕ}

/-! ## Eligibility at wavelength two -/

variable (Validator) in
/-- The round at which a slot's verdict is settled: its supports live
here. One round — there is no certificate round. -/
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 1

variable (Validator) in
/-- `j` may anchor `k`: its proposal lies past `k`'s decision round. -/
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j

omit [Fintype Validator] [DecidableEq Validator] H in
/-- Eligibility, unfolded: two rounds. -/
theorem eligible_iff {k j : ℕ} :
    Eligible Validator k j ↔ S.slotRound k + 2 ≤ S.slotRound j := by
  simp [Eligible, decisionRound]
  omega

instance decidableEligible (k j : ℕ) : Decidable (Eligible Validator k j) :=
  inferInstanceAs (Decidable (decisionRound Validator k < S.slotRound j))

omit [Fintype Validator] [DecidableEq Validator] H in
/-- An eligible anchor is a later slot. -/
theorem lt_of_eligible {k j : ℕ} (h : Eligible Validator k j) : k < j := by
  by_contra hle
  have : S.slotRound j ≤ S.slotRound k := S.mono (by omega)
  rw [eligible_iff] at h
  omega

/-- The anchor's round clears the slot's decision round by one — enough
for H4 to read the whole certificate out of its cone. -/
theorem anchor_round_le {j : ℕ} (hA : IsLeaderBlock U j A)
    (helig : Eligible Validator k j) :
    S.slotRound k + 2 ≤ (U.block A).round := by
  rw [hA.2.1]
  exact eligible_iff.mp helig

/-! ## The view-relative direct rules -/

/-- The supporters a view actually holds. -/
def supportersIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun p => L ∈ (U.block p).refs)) ∩ V.ids)

/-- The blamers a view actually holds. -/
def blamesIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun p => L ∉ (U.block p).refs)) ∩ V.ids)

/-- Direct commit, as judged from a single view. -/
def DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  q Validator ≤ (supportersIn U V L r).card

/-- Direct skip, as judged from a single view. -/
def DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  q Validator ≤ (blamesIn U V L r).card

instance {V : View Validator BlockId Payload U} :
    Decidable (DirectCommitIn U V L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance {V : View Validator BlockId Payload U} :
    Decidable (DirectSkipIn U V L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- A view can only under-report: its direct commit is genuine. -/
theorem directCommit_of_directCommitIn
    {V : View Validator BlockId Payload U}
    (h : DirectCommitIn U V L r) : DirectCommit U L r :=
  le_trans h (Finset.card_le_card
    (Finset.image_subset_image Finset.inter_subset_left))

/-- A view can only under-report: its direct skip is genuine. -/
theorem directSkip_of_directSkipIn
    {V : View Validator BlockId Payload U}
    (h : DirectSkipIn U V L r) : DirectSkip U L r :=
  le_trans h (Finset.card_le_card
    (Finset.image_subset_image Finset.inter_subset_left))

/-! ## The safety lemmas, lifted to views -/

/-- Cross-view H2: one validator cannot directly commit what another
directly skips. -/
theorem not_directSkipIn_of_directCommitIn (hne : HonestNoEquiv U)
    {V₁ V₂ : View Validator BlockId Payload U}
    (h₁ : DirectCommitIn U V₁ L r) (h₂ : DirectSkipIn U V₂ L r) : False :=
  not_directSkip_of_directCommit hne
    (directCommit_of_directCommitIn h₁) (directSkip_of_directSkipIn h₂)

/-- Cross-view twin uniqueness: two direct commits for one slot agree. -/
theorem eq_of_directCommitIn (hne : HonestNoEquiv U)
    {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V₁ L₁ r) (h₂ : DirectCommitIn U V₂ L₂ r) :
    L₁ = L₂ :=
  eq_of_directCommit hne (directCommit_of_directCommitIn h₁)
    (directCommit_of_directCommitIn h₂) (by rw [hL₁.2.2, hL₂.2.2])

/-- H4, from a view: a view-level direct commit passes the indirect
test at every block two rounds up. -/
theorem thickLink_of_directCommitIn (hne : HonestNoEquiv U)
    (hkb : k + 3 * H.fb + 2 * H.fc ≤ Fintype.card Validator)
    {V : View Validator BlockId Payload U}
    (h : DirectCommitIn U V L r) (hA : A ∈ U.ids)
    (hround : r + 2 ≤ (U.block A).round) : ThickLink k U A L r :=
  thickLink_of_directCommit hne hkb (directCommit_of_directCommitIn h)
    hA hround

/-- H3, from a view: a view-level direct skip fails the indirect test
everywhere. -/
theorem not_thickLink_of_directSkipIn (hne : HonestNoEquiv U)
    (hka : 2 * H.fb + H.fc + 1 ≤ k)
    {V : View Validator BlockId Payload U}
    (h : DirectSkipIn U V L r) (A : BlockId) : ¬ ThickLink k U A L r :=
  not_thickLink_of_directSkip hne hka (directSkip_of_directSkipIn h) A

/-- H5, from a view: a view-level direct commit is the only same-slot
candidate that can pass the indirect test, at any anchor. -/
theorem eq_of_directCommitIn_of_thickLink (hne : HonestNoEquiv U)
    (hka : 2 * H.fb + H.fc + 1 ≤ k)
    {V : View Validator BlockId Payload U} {j : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U j L₁) (hL₂ : IsLeaderBlock U j L₂)
    (h₁ : DirectCommitIn U V L₁ r) (ht : ThickLink k U A L₂ r) : L₁ = L₂ :=
  eq_of_directCommit_of_thickLink hne hka
    (directCommit_of_directCommitIn h₁) ht (by rw [hL₁.2.2, hL₂.2.2])

/-! ## The decision relation -/

/-- `Decided k U V s v` — a validator holding `V` has settled slot `s`,
at indirect threshold `k`. Mirrors the Odontoceti relation, canonicity
clause included: a Byzantine leader can still plant two passing
candidates in one anchor's cone, and the crash class does not close the
gap, so the committed candidate is the `≤`-least passing one. -/
inductive Decided (k : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {s : ℕ} {L : BlockId} :
      IsLeaderBlock U s L → DirectCommitIn U V L (S.slotRound s) →
      Decided k U V s (some L)
  /-- The direct rule blames every candidate — vacuously, when the
  leader produced nothing. -/
  | directSkip {s : ℕ} :
      (∀ L, IsLeaderBlock U s L → DirectSkipIn U V L (S.slotRound s)) →
      Decided k U V s none
  /-- Anchored on the nearest eligible committed slot, the least
  candidate passing the indirect test is committed. -/
  | indirectCommit {s j : ℕ} {A L : BlockId} :
      s < j → Eligible Validator s j → Decided k U V j (some A) →
      (∀ i, s < i → i < j → Eligible Validator s i → Decided k U V i none) →
      IsLeaderBlock U s L → ThickLink k U A L (S.slotRound s) →
      (∀ L', IsLeaderBlock U s L' → ThickLink k U A L' (S.slotRound s) →
        ¬ L' < L) →
      Decided k U V s (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate
  passes the indirect test. -/
  | indirectSkip {s j : ℕ} {A : BlockId} :
      s < j → Eligible Validator s j → Decided k U V j (some A) →
      (∀ i, s < i → i < j → Eligible Validator s i → Decided k U V i none) →
      (∀ L, IsLeaderBlock U s L → ¬ ThickLink k U A L (S.slotRound s)) →
      Decided k U V s none

/-- A committed slot's block is a candidate of that slot. -/
theorem isLeaderBlock_of_decided {V : View Validator BlockId Payload U}
    {j : ℕ} {A : BlockId} (h : Decided k U V j (some A)) :
    IsLeaderBlock U j A := by
  cases h with
  | directCommit hL _ => exact hL
  | indirectCommit _ _ _ _ hL _ _ => exact hL

/-! ## H6 — agreement -/

/-- **Visibility from an anchor.** A slot committed directly carries a
thick link at any eligible anchor above it — what rules out the mixed
cases, where one validator commits directly and the other skips
indirectly. -/
theorem thickLink_of_directCommitIn_at_anchor (hne : HonestNoEquiv U)
    (hkb : k + 3 * H.fb + 2 * H.fc ≤ Fintype.card Validator)
    {V W : View Validator BlockId Payload U} {s j : ℕ} {L A : BlockId}
    (h : DirectCommitIn U V L (S.slotRound s))
    (hj : Decided k U W j (some A)) (helig : Eligible Validator s j) :
    ThickLink k U A L (S.slotRound s) :=
  thickLink_of_directCommitIn hne hkb h (isLeaderBlock_of_decided hj).1
    (anchor_round_le (isLeaderBlock_of_decided hj) helig)

/-- **H6 (agreement; the O5 mirror).** No two validators reach
conflicting decisions for a slot at any admissible threshold, whatever
views they hold and whichever routes they took. The sixteen-case
induction of O5 and M6: the direct diagonal by H2 and twin uniqueness,
every direct-versus-indirect crossing by H3, H4 or H5, and the shared
anchor forced by `anchor_eq` with canonicity arbitrating the
commit-commit case. -/
theorem decided_unique (hne : HonestNoEquiv U)
    (hk : Admissible Validator k)
    {V₁ : View Validator BlockId Payload U} {s : ℕ}
    {v₁ : Option BlockId} (h₁ : Decided k U V₁ s v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided k U V₂ s v₂ → v₁ = v₂ := by
  obtain ⟨hka, hkb⟩ := hk
  induction h₁ with
  | @directCommit s L hL h =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact congrArg some (eq_of_directCommitIn hne hL hL₂ h h₂)
    | directSkip hskip =>
      exact absurd (not_directSkipIn_of_directCommitIn hne h (hskip L hL))
        not_false
    | indirectCommit _ _ _ _ hL₂ ht₂ _ =>
      exact congrArg some
        (eq_of_directCommitIn_of_thickLink hne hka hL hL₂ h ht₂)
    | @indirectSkip _ j A hkj helig hj hmid hnone =>
      exact absurd (thickLink_of_directCommitIn_at_anchor hne hkb h hj helig)
        (hnone _ hL)
  | @directSkip s hskip =>
    intro V₂ v₂ h₂
    cases h₂ with
    | @directCommit _ L₂ hL₂ h₂ =>
      exact absurd (not_directSkipIn_of_directCommitIn hne h₂ (hskip L₂ hL₂))
        not_false
    | directSkip _ => rfl
    | indirectCommit _ _ _ _ hL₂ ht₂ _ =>
      exact absurd ht₂ (not_thickLink_of_directSkipIn hne hka (hskip _ hL₂) _)
    | indirectSkip _ _ _ _ _ => rfl
  | @indirectCommit s j A L hkj helig hj hmid hL ht hmin ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact congrArg some
        (eq_of_directCommitIn_of_thickLink hne hka hL₂ hL h₂ ht).symm
    | directSkip hskip₂ =>
      exact absurd ht (not_thickLink_of_directSkipIn hne hka (hskip₂ _ hL) _)
    | @indirectCommit _ j₂ A₂ L₂ hkj₂ helig₂ hj₂ hmid₂ hL₂ ht₂ hmin₂ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact congrArg some (le_antisymm
        (not_lt.mp (hmin L₂ hL₂ ht₂)) (not_lt.mp (hmin₂ L hL ht)))
    | @indirectSkip _ j₂ A₂ hkj₂ helig₂ hj₂ hmid₂ hnone₂ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact absurd ht (hnone₂ _ hL)
  | @indirectSkip s j A hkj helig hj hmid hnone ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact absurd (thickLink_of_directCommitIn_at_anchor hne hkb h₂ hj helig)
        (hnone _ hL₂)
    | directSkip _ => rfl
    | @indirectCommit _ j₂ A₂ L₂ hkj₂ helig₂ hj₂ hmid₂ hL₂ ht₂ hmin₂ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact absurd ht₂ (hnone _ hL₂)
    | indirectSkip _ _ _ _ _ => rfl

/-- Agreement, in M6's binary shape. -/
theorem decided_agree (hne : HonestNoEquiv U) (hk : Admissible Validator k)
    {V₁ V₂ : View Validator BlockId Payload U} {s : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : Decided k U V₁ s v₁)
    (h₂ : Decided k U V₂ s v₂) : v₁ = v₂ :=
  decided_unique hne hk h₁ V₂ v₂ h₂

/-- **Safety.** Two committed blocks for one slot are the same block,
across any two views and any two routes. -/
theorem safety (hne : HonestNoEquiv U) (hk : Admissible Validator k)
    {V₁ V₂ : View Validator BlockId Payload U} {s : ℕ}
    {L₁ L₂ : BlockId} (h₁ : Decided k U V₁ s (some L₁))
    (h₂ : Decided k U V₂ s (some L₂)) : L₁ = L₂ :=
  Option.some.inj (decided_unique hne hk h₁ V₂ (some L₂) h₂)

end Hybrid

end LeanDag
