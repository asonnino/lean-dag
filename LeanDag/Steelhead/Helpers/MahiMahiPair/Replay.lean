import LeanDag.Steelhead.MahiMahiPair.Replay.Statement
import LeanDag.Steelhead.Helpers.Replay
import LeanDag.Steelhead.Helpers.MahiMahiPair.Coin
/-!
# Helpers — the `3f + 1` pair's replay

Generated lemma infrastructure for `MahiMahiPair/Replay/Statement.lean`;
not part of the audit surface. The window's evidence is Mahi-Mahi's
predicates intersected with the window; the window's committed
candidates are the counting lemma's, read on the anchor's causal history
as a record, whose votes and certificates are the universe's restricted
to it; and the selection at an anchor is the generic one of
`Helpers/Replay.lean` on the window's evidence.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

open Steelhead.Replay
open scoped ENNReal

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [LinearOrder BlockId]

/-! ## The selection at an anchor -/

/-- **SH-MM18h.** SH18h on the anchor's window. -/
theorem anchorUpdate_range {U : BlockUniverse Validator BlockId Payload} {I : ℕ}
    (C : Config Validator) (candidates : List ℕ) (epsilon : ℚ) {K k : ℕ} (A : BlockId)
    (hc : ∀ c ∈ candidates, 1 ≤ c ∧ c ≤ K) (h1 : 1 ≤ k) (hk : k ≤ K) :
    1 ≤ anchorUpdate U I C candidates epsilon A k ∧
      anchorUpdate U I C candidates epsilon A k ≤ K :=
  update_range (ofAnchor U A I) C candidates epsilon hc h1 hk

/-- **SH-MM18n, second half.** SH18n's second half on the anchor's window. -/
theorem anchorUpdate_dvd {U : BlockUniverse Validator BlockId Payload} {I : ℕ}
    (C : Config Validator) (epsilon : ℚ) {e k : ℕ} (A : BlockId) (hk : k ∣ 2 ^ e) :
    anchorUpdate U I C (candidatesUpto (2 ^ e)) epsilon A k ∣ 2 ^ e :=
  update_dvd (ofAnchor U A I) C epsilon hk

/-! ## The evidence -/

/-- A quorum of certificates within the window is at least one. -/
theorem certified_of_commits (U : BlockUniverse Validator BlockId Payload) (A : BlockId)
    (I r w : ℕ) (a : Validator) (h : (ofAnchor U A I).commits r w a = true) :
    (ofAnchor U A I).certified r w a = true := by
  simp only [ofAnchor, decide_eq_true_eq] at h ⊢
  obtain ⟨L, hL, hc⟩ := h
  refine ⟨L, hL, ?_⟩
  intro he
  rw [he] at hc
  simp only [creatorsOf, Finset.image_empty, Finset.card_empty] at hc
  have := F.card_validators
  omega

/-- A quorum of blames within the window is one in the universe, and MM1a then leaves no
certificate at all. -/
theorem not_certified_of_skips (U : BlockUniverse Validator BlockId Payload) (A : BlockId)
    (I r w : ℕ) (a : Validator) (hw : 2 ≤ w) (h : (ofAnchor U A I).skips r w a = true) :
    (ofAnchor U A I).certified r w a = false := by
  simp only [ofAnchor, decide_eq_true_eq] at h
  simp only [ofAnchor, decide_eq_false_iff_not, not_exists, not_and, not_not]
  intro L hL
  have hglobal : MahiMahi.DirectSkip U w a r :=
    le_trans h (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))
  obtain ⟨hLr, hLa, _⟩ := Finset.mem_filter.mp hL
  have he := MahiMahi.certificates_eq_empty_of_directSkip hw hglobal hLa (mem_blocksAt.mp hLr).2
  rw [he]
  simp

/-! ## The window as a record -/

variable {U : BlockUniverse Validator BlockId Payload}

/-- The candidates a block of a view sees are the universe's: the histories coincide, and a
view is closed under references. -/
theorem candidatesAt_toRecord {V : View Validator BlockId Payload U} {q : BlockId}
    (hq : q ∈ V.ids) (a : Validator) (r : ℕ) :
    MahiMahi.candidatesAt V.toRecord q a r = MahiMahi.candidatesAt U q a r := by
  ext L
  simp only [MahiMahi.candidatesAt, Finset.mem_filter, mem_blocksAt, BlockRecord.View.toRecord_ids,
    BlockRecord.View.toRecord_block]
  constructor
  · rintro ⟨⟨hL, hLr⟩, hLa, hLh⟩
    exact ⟨⟨V.subset_ids hL, hLr⟩, hLa, hLh⟩
  · rintro ⟨⟨hL, hLr⟩, hLa, hLh⟩
    refine ⟨⟨?_, hLr⟩, hLa, hLh⟩
    exact mem_of_reaches_of_closed V.complete hq ((mem_history_iff (V.subset_ids hq)).mp hLh)

/-- A vote read in a view is a vote in the universe. -/
theorem votes_toRecord {V : View Validator BlockId Payload U} {q L : BlockId} (hq : q ∈ V.ids) :
    MahiMahi.Votes V.toRecord q L ↔ MahiMahi.Votes U q L := by
  unfold MahiMahi.Votes
  simp only [BlockRecord.View.toRecord_block, candidatesAt_toRecord hq]

/-- The certificates a view holds are the universe's within it. -/
theorem certificates_toRecord {V : View Validator BlockId Payload U} {w : ℕ} {L : BlockId}
    {r : ℕ} :
    MahiMahi.certificates V.toRecord w L r = MahiMahi.certificates U w L r ∩ V.ids := by
  ext C
  simp only [MahiMahi.certificates, mem_certificatesAt, BlockRecord.View.toRecord_ids,
    BlockRecord.View.toRecord_block, Finset.mem_inter]
  constructor
  · rintro ⟨hC, hCr, hcar⟩
    refine ⟨⟨V.subset_ids hC, hCr, ?_⟩, hC⟩
    unfold CarriesVotes at hcar ⊢
    refine le_trans hcar (Finset.card_le_card (Finset.image_subset_image ?_))
    intro q hq
    rw [mem_carriedVotes] at hq ⊢
    exact ⟨hq.1, (votes_toRecord (V.complete C hC q hq.1)).mp hq.2⟩
  · rintro ⟨⟨hC, hCr, hcar⟩, hCV⟩
    refine ⟨hCV, hCr, ?_⟩
    unfold CarriesVotes at hcar ⊢
    refine le_trans hcar (Finset.card_le_card (Finset.image_subset_image ?_))
    intro q hq
    rw [mem_carriedVotes] at hq ⊢
    exact ⟨hq.1, (votes_toRecord (V.complete C hCV q hq.1)).mpr hq.2⟩

/-- **SH-MM18d.** The counting lemma on the anchor's history as a record, whose committed candidates
the window's evidence marks: their certificates are the universe's within the history, at a
round the window retains. -/
theorem window_count {wa I : ℕ} {A : BlockId} (hA : A ∈ U.ids) {T : Finset Validator} {r : ℕ}
    (hwa : 5 ≤ wa) (hcard : quorumCard Validator ≤ T.card) (hr : windowBottom U A I ≤ r)
    (hpop3 : PopulatedOn (U.historyView A hA).toRecord T (r + 3))
    (hpopd : PopulatedOn (U.historyView A hA).toRecord T (MahiMahi.decisionRoundAt wa r)) :
    Fintype.card Validator - F.f - F.byzantine.card ≤ committedCount (ofAnchor U A I) r wa := by
  unfold committedCount
  refine le_trans (MahiMahiPair.card_goodAt_of_populated hwa hcard hpop3 hpopd)
    (Finset.card_le_card fun a ha => ?_)
  obtain ⟨L, hLW, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp ha
  change L ∈ history U A at hLW
  rw [BlockRecord.View.toRecord_block] at hLr hLc
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  simp only [ofAnchor, decide_eq_true_eq]
  have hLwin : L ∈ windowIds U A I := by
    refine Finset.mem_filter.mpr ⟨hLW, ?_, round_le_of_mem_history hA hLW⟩
    rw [hLr]
    exact hr
  refine ⟨L, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨history_subset_ids hA hLW, hLr⟩, hLc,
    hLwin⟩, ?_⟩
  unfold MahiMahi.DirectCommit at hdc
  rw [certificates_toRecord] at hdc
  refine le_trans hdc (Finset.card_le_card (Finset.image_subset_image ?_))
  intro C hC
  obtain ⟨hCU, hCW⟩ := Finset.mem_inter.mp hC
  refine Finset.mem_inter.mpr ⟨hCU, ?_⟩
  change C ∈ history U A at hCW
  refine Finset.mem_filter.mpr ⟨hCW, ?_, round_le_of_mem_history hA hCW⟩
  rw [(mem_certificatesAt.mp hCU).2.1]
  exact le_trans hr (by unfold MahiMahi.decisionRoundAt; omega)

/-- **SH-MM18g.** A quorum of certificates within the window is a quorum of certificates on the DAG,
for a block of the author at the round. -/
theorem commits_sound {A : BlockId} {I r w : ℕ} {a : Validator}
    (h : (ofAnchor U A I).commits r w a = true) :
    ∃ L ∈ blocksAt U r, (U.block L).creator = a ∧ MahiMahi.DirectCommit U w L r := by
  simp only [ofAnchor, decide_eq_true_eq] at h
  obtain ⟨L, hL, hc⟩ := h
  obtain ⟨hLr, hLa, -⟩ := Finset.mem_filter.mp hL
  refine ⟨L, hLr, hLa, ?_⟩
  unfold MahiMahi.DirectCommit
  exact le_trans hc (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))

/-- The window marks committed exactly the authors whose round-`r` block the anchor's history,
read as a record, directly commits: a candidate at a round the window retains lies in the history,
and its certificates within the window are its certificates within the history, whose round the
window retains too. -/
theorem committedCount_eq_card_goodAt {wa I : ℕ} (hwa : 1 ≤ wa) {A : BlockId} (hA : A ∈ U.ids)
    {r : ℕ} (hr : windowBottom U A I ≤ r) :
    committedCount (ofAnchor U A I) r wa =
      (MahiMahi.goodAt (U.historyView A hA).toRecord wa r).card := by
  unfold committedCount
  congr 1
  ext a
  rw [Finset.mem_filter, MahiMahi.mem_goodAt]
  simp only [Finset.mem_univ, true_and, ofAnchor, decide_eq_true_eq,
    BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block]
  constructor
  · rintro ⟨L, hL, hc⟩
    obtain ⟨hLr, hLa, hLw⟩ := Finset.mem_filter.mp hL
    obtain ⟨-, hLround⟩ := mem_blocksAt.mp hLr
    obtain ⟨hLh, -, -⟩ := Finset.mem_filter.mp hLw
    refine ⟨L, hLh, hLround, hLa, ?_⟩
    unfold MahiMahi.DirectCommit
    rw [certificates_toRecord]
    refine le_trans hc (Finset.card_le_card (Finset.image_subset_image ?_))
    intro C hC
    obtain ⟨hCU, hCw⟩ := Finset.mem_inter.mp hC
    exact Finset.mem_inter.mpr ⟨hCU, (Finset.mem_filter.mp hCw).1⟩
  · rintro ⟨L, hLh, hLround, hLa, hdc⟩
    change L ∈ history U A at hLh
    have hLw : L ∈ windowIds U A I :=
      Finset.mem_filter.mpr ⟨hLh, by rw [hLround]; exact hr, round_le_of_mem_history hA hLh⟩
    refine ⟨L, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨history_subset_ids hA hLh, hLround⟩, hLa,
      hLw⟩, ?_⟩
    unfold MahiMahi.DirectCommit at hdc
    rw [certificates_toRecord] at hdc
    refine le_trans hdc (Finset.card_le_card (Finset.image_subset_image ?_))
    intro C hC
    obtain ⟨hCU, hCh⟩ := Finset.mem_inter.mp hC
    change C ∈ history U A at hCh
    refine Finset.mem_inter.mpr
      ⟨hCU, Finset.mem_filter.mpr ⟨hCh, ?_, round_le_of_mem_history hA hCh⟩⟩
    rw [(mem_certificatesAt.mp hCU).2.1]
    exact le_trans hr (by unfold MahiMahi.decisionRoundAt; omega)

/-- **SH-MM18i.** The count, over `n`, is the uniform coin's measure of the committed set. -/
theorem commitWeight_eq_commitProb {wa I : ℕ} (hwa : 1 ≤ wa) {A : BlockId} (hA : A ∈ U.ids)
    {r : ℕ} (hr : windowBottom U A I ≤ r) :
    (committedCount (ofAnchor U A I) r wa : ℝ≥0∞) / Fintype.card Validator =
      commitProb (MahiMahi.goodAt (U.historyView A hA).toRecord wa) r := by
  rw [committedCount_eq_card_goodAt hwa hA hr, commitProb_eq]

end MahiMahiPair

end Steelhead

end LeanDag
