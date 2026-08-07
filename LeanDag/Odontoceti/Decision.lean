import LeanDag.Odontoceti.Rules
import LeanDag.Liveness

/-!
# Odontoceti: the decision relation, and agreement

`odontoceti.md` §4, OP3 — `Decided`, its view layer, and **O5**
(`decided_unique`, the M6 analogue): no two validators reach conflicting
decisions for a slot, whatever views they hold and whichever routes they
took.

The relation mirrors Mysticeti's constructor for constructor — direct
commit, direct skip quantified over all candidate blocks, and the
indirect rules through the nearest eligible anchor with the positive
intermediate premise — with two deliberate differences:

* **The wavelength.** `decisionRound k = slotRound k + 1`: supports at
  the decision round are the whole story, there is no certificate
  round, and eligibility starts one round earlier
  (`Eligible k j ↔ slotRound k + 2 ≤ slotRound j`).
* **The canonical candidate.** `indirectCommit` carries a minimality
  premise: the committed block is the `≤`-least candidate passing the
  indirect test at the anchor. This is not decoration — it is a **gap
  in the thesis** made explicit. Lemma 5's proof asserts that sharing
  an anchor yields agreement, but nothing in the quorum arithmetic
  prevents two equivocating candidates from *both* passing ThickLink at
  one anchor (the witness file realises exactly that configuration on
  data at `n = 5f+1`); the implementation's determinism — the iteration
  order of `GetLeaderBlocks` — is what actually arbitrates, and the
  minimality premise is that determinism as mathematics, under
  `[LinearOrder BlockId]` (hash order, in an implementation). Every
  *other* pairing closes by counting alone: direct-vs-direct by O1/O1′,
  the direct-vs-indirect crossings by O2/O3/O4′ — a directly committed
  block is the unique candidate that can pass the test anywhere, which
  is why the direct verdicts need no canonicity.
-/

namespace LeanDag

namespace Odontoceti

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {L A : BlockId} {r k : ℕ}

/-! ## Eligibility at wavelength two -/

variable (Validator) in
/-- The round at which a slot's verdict is settled: its supports live
here. One round, not two — there is no certificate round. -/
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 1

variable (Validator) in
/-- `j` may anchor `k`: its proposal lies past `k`'s decision round. A
predicate on the slot pair alone — which is what lets the agreement
induction match two validators' premises against each other. -/
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j

omit [Fintype Validator] [DecidableEq Validator] F in
theorem eligible_iff {k j : ℕ} :
    Eligible Validator k j ↔ S.slotRound k + 2 ≤ S.slotRound j := by
  simp [Eligible, decisionRound]
  omega

instance decidableEligible (k j : ℕ) : Decidable (Eligible Validator k j) :=
  inferInstanceAs (Decidable (decisionRound Validator k < S.slotRound j))

omit [Fintype Validator] [DecidableEq Validator] F in
/-- An eligible anchor is a later slot. -/
theorem lt_of_eligible {k j : ℕ} (h : Eligible Validator k j) : k < j := by
  by_contra hle
  have : S.slotRound j ≤ S.slotRound k := S.mono (by omega)
  rw [eligible_iff] at h
  omega

/-- The anchor's round clears the slot's decision round by one — enough
for O3 to read the whole certificate out of its cone. -/
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
    (((blocksAt U (r + 1)).filter (fun q => L ∈ (U.block q).refs)) ∩ V.ids)

/-- The blamers a view actually holds. -/
def blamesIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun q => L ∉ (U.block q).refs)) ∩ V.ids)

/-- Direct commit, as judged from a single view. -/
def DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (supportersIn U V L r).card

/-- Direct skip, as judged from a single view. -/
def DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (blamesIn U V L r).card

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

/-- Cross-view O1: one validator cannot directly commit what another
directly skips. -/
theorem not_directSkipIn_of_directCommitIn
    {V₁ V₂ : View Validator BlockId Payload U}
    (h₁ : DirectCommitIn U V₁ L r) (h₂ : DirectSkipIn U V₂ L r) : False :=
  not_directSkip_of_directCommit
    (directCommit_of_directCommitIn h₁) (directSkip_of_directSkipIn h₂)

/-- Cross-view O1′: two direct commits for one slot agree. -/
theorem eq_of_directCommitIn {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V₁ L₁ r) (h₂ : DirectCommitIn U V₂ L₂ r) :
    L₁ = L₂ :=
  eq_of_directCommit (directCommit_of_directCommitIn h₁)
    (directCommit_of_directCommitIn h₂) (by rw [hL₁.2.2, hL₂.2.2])

/-- O3, from a view: a view-level direct commit passes the indirect
test at every block two rounds up. -/
theorem thickLink_of_directCommitIn {V : View Validator BlockId Payload U}
    (h : DirectCommitIn U V L r) (hA : A ∈ U.ids)
    (hround : r + 2 ≤ (U.block A).round) : ThickLink U A L r :=
  thickLink_of_directCommit (directCommit_of_directCommitIn h) hA hround

/-- O2, from a view: a view-level direct skip fails the indirect test
everywhere. -/
theorem not_thickLink_of_directSkipIn {V : View Validator BlockId Payload U}
    (h : DirectSkipIn U V L r) (A : BlockId) : ¬ ThickLink U A L r :=
  not_thickLink_of_directSkip (directSkip_of_directSkipIn h) A

/-- O4′, from a view: a view-level direct commit is the only same-slot
candidate that can pass the indirect test, at any anchor. -/
theorem eq_of_directCommitIn_of_thickLink
    {V : View Validator BlockId Payload U} {k : ℕ} {L₁ L₂ : BlockId}
    (hL₁ : IsLeaderBlock U k L₁) (hL₂ : IsLeaderBlock U k L₂)
    (h₁ : DirectCommitIn U V L₁ r) (ht : ThickLink U A L₂ r) : L₁ = L₂ :=
  eq_of_directCommit_of_thickLink (directCommit_of_directCommitIn h₁) ht
    (by rw [hL₁.2.2, hL₂.2.2])

/-! ## The decision relation -/

/-- `Decided U V k v` — a validator holding `V` has settled slot `k`.

Mirrors Mysticeti's relation: the anchor is the **nearest eligible**
committed slot (the intermediate premise, stated positively), and the
skip case quantifies over all candidate blocks. The one new element is
the canonicity premise on `indirectCommit` — the committed candidate is
the `≤`-least one passing the test at the anchor — which is the
implementation's deterministic iteration order made explicit; see the
module docstring for why agreement is unprovable without it. -/
inductive Decided (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      Decided U V k (some L)
  /-- The direct rule blames every candidate — vacuously, when the
  leader produced nothing. -/
  | directSkip {k : ℕ} :
      (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      Decided U V k none
  /-- Anchored on the nearest eligible committed slot, the least
  candidate passing the indirect test is committed. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      IsLeaderBlock U k L → ThickLink U A L (S.slotRound k) →
      (∀ L', IsLeaderBlock U k L' → ThickLink U A L' (S.slotRound k) →
        ¬ L' < L) →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate
  passes the indirect test. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ ThickLink U A L (S.slotRound k)) →
      Decided U V k none

/-- A committed slot's block is a candidate of that slot. -/
theorem isLeaderBlock_of_decided {V : View Validator BlockId Payload U}
    {j : ℕ} {A : BlockId} (h : Decided U V j (some A)) :
    IsLeaderBlock U j A := by
  cases h with
  | directCommit hL _ => exact hL
  | indirectCommit _ _ _ _ hL _ _ => exact hL

/-! ## O5 — agreement -/

/-- **O5 (thesis Lemma 5; the M6 analogue).** No two validators reach
conflicting decisions for a slot, whatever views they hold and
whichever routes they took.

Structural induction on the first derivation, exactly M6's shape. The
direct/direct diagonal closes by O1/O1′; every direct-versus-indirect
crossing closes by O2/O3/O4′ — the two-round replacements for
M2/M3/M4/M5′; and the one real case, indirect against indirect, closes
by the anchor trichotomy: an earlier anchor is covered by the *other*
validator's intermediate-skip premise, and a shared anchor forces a
shared verdict — skip against commit by the `hnone` premise, commit
against commit by canonicity, which is the step the thesis's Lemma 5
takes silently. -/
theorem decided_unique {V₁ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ : Option BlockId} (h₁ : Decided U V₁ k v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided U V₂ k v₂ → v₁ = v₂ := by
  induction h₁ with
  | @directCommit k L hL h =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact congrArg some (eq_of_directCommitIn hL hL₂ h h₂)
    | directSkip hskip =>
      exact absurd (not_directSkipIn_of_directCommitIn h (hskip L hL))
        not_false
    | indirectCommit _ _ _ _ hL₂ ht₂ _ =>
      exact congrArg some (eq_of_directCommitIn_of_thickLink hL hL₂ h ht₂)
    | @indirectSkip _ j A hkj helig hj hmid hnone =>
      -- the engine: our commit is visible from their anchor
      exact absurd (thickLink_of_directCommitIn h
          (isLeaderBlock_of_decided hj).1
          (anchor_round_le (isLeaderBlock_of_decided hj) helig))
        (hnone _ hL)
  | @directSkip k hskip =>
    intro V₂ v₂ h₂
    cases h₂ with
    | @directCommit _ L₂ hL₂ h₂ =>
      exact absurd (not_directSkipIn_of_directCommitIn h₂ (hskip L₂ hL₂))
        not_false
    | directSkip _ => rfl
    | indirectCommit _ _ _ _ hL₂ ht₂ _ =>
      exact absurd ht₂ (not_thickLink_of_directSkipIn (hskip _ hL₂) _)
    | indirectSkip _ _ _ _ _ => rfl
  | @indirectCommit k j A L hkj helig hj hmid hL ht hmin ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact congrArg some
        (eq_of_directCommitIn_of_thickLink hL₂ hL h₂ ht).symm
    | directSkip hskip₂ =>
      exact absurd ht (not_thickLink_of_directSkipIn (hskip₂ _ hL) _)
    | @indirectCommit _ j₂ A₂ L₂ hkj₂ helig₂ hj₂ hmid₂ hL₂ ht₂ hmin₂ =>
      rcases lt_trichotomy j j₂ with hlt | heq | hgt
      · exact absurd (ihj V₂ none (hmid₂ j hkj hlt helig)) (by simp)
      · subst heq
        have hA : A = A₂ := Option.some.inj (ihj V₂ (some A₂) hj₂)
        subst hA
        -- shared anchor: canonicity arbitrates
        exact congrArg some (le_antisymm
          (not_lt.mp (hmin L₂ hL₂ ht₂)) (not_lt.mp (hmin₂ L hL ht)))
      · exact absurd (ihmid j₂ hkj₂ hgt helig₂ V₂ (some A₂) hj₂) (by simp)
    | @indirectSkip _ j₂ A₂ hkj₂ helig₂ hj₂ hmid₂ hnone₂ =>
      rcases lt_trichotomy j j₂ with hlt | heq | hgt
      · exact absurd (ihj V₂ none (hmid₂ j hkj hlt helig)) (by simp)
      · subst heq
        have hA : A = A₂ := Option.some.inj (ihj V₂ (some A₂) hj₂)
        subst hA
        exact absurd ht (hnone₂ _ hL)
      · exact absurd (ihmid j₂ hkj₂ hgt helig₂ V₂ (some A₂) hj₂) (by simp)
  | @indirectSkip k j A hkj helig hj hmid hnone ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact absurd (thickLink_of_directCommitIn h₂
          (isLeaderBlock_of_decided hj).1
          (anchor_round_le (isLeaderBlock_of_decided hj) helig))
        (hnone _ hL₂)
    | directSkip _ => rfl
    | @indirectCommit _ j₂ A₂ L₂ hkj₂ helig₂ hj₂ hmid₂ hL₂ ht₂ hmin₂ =>
      rcases lt_trichotomy j j₂ with hlt | heq | hgt
      · exact absurd (ihj V₂ none (hmid₂ j hkj hlt helig)) (by simp)
      · subst heq
        have hA : A = A₂ := Option.some.inj (ihj V₂ (some A₂) hj₂)
        subst hA
        exact absurd ht₂ (hnone _ hL₂)
      · exact absurd (ihmid j₂ hkj₂ hgt helig₂ V₂ (some A₂) hj₂) (by simp)
    | indirectSkip _ _ _ _ _ => rfl

/-- **O6 (safety).** Two committed blocks for one slot are the same
block, across any two views and any two routes. -/
theorem safety {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {L₁ L₂ : BlockId} (h₁ : Decided U V₁ k (some L₁))
    (h₂ : Decided U V₂ k (some L₂)) : L₁ = L₂ :=
  Option.some.inj (decided_unique h₁ V₂ (some L₂) h₂)

end Odontoceti

end LeanDag
