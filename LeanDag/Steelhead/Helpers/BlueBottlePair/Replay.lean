import LeanDag.Steelhead.BlueBottlePair.Replay.Statement
import LeanDag.Steelhead.Helpers.Replay
import LeanDag.Steelhead.Helpers.MahiMahiPair.Replay
import LeanDag.Steelhead.Helpers.BlueBottlePair.Coin
import LeanDag.AsyncBlueBottle.Helpers.Rules
import LeanDag.AsyncBlueBottle.Helpers.Counting
/-!
# Helpers — the `5f + 1` pair's replay

Generated lemma infrastructure for `BlueBottlePair/Replay/Statement.lean`;
not part of the audit surface. The window's evidence is the pair's
support intersected with the window, Odontoceti's references one round
up at wave two and Async BlueBottle's cone votes two rounds up otherwise;
the window's committed candidates at wave three are ABB7's, read on the
anchor's causal history as a record whose cone votes are the universe's
restricted to it; and the selection at an anchor is the generic one of
`Helpers/Replay.lean` on the window's evidence.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Replay

open Steelhead.Replay (Config Evidence committedCount candidatesUpto update_range update_dvd
  windowIds)
open scoped ENNReal

variable {Validator BlockId Payload : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] [LinearOrder BlockId]

/-! ## The selection at an anchor -/

/-- **SH-BB18h.** SH18h on the pair's window. -/
theorem anchorUpdate_range {U : BlockUniverse Validator BlockId Payload} {I : ℕ}
    (C : Config Validator) (candidates : List ℕ) (epsilon : ℚ) {K k : ℕ} (A : BlockId)
    (hc : ∀ c ∈ candidates, 1 ≤ c ∧ c ≤ K) (h1 : 1 ≤ k) (hk : k ≤ K) :
    1 ≤ anchorUpdate U I C candidates epsilon A k ∧
      anchorUpdate U I C candidates epsilon A k ≤ K :=
  update_range (ofAnchor U A I) C candidates epsilon hc h1 hk

/-- **SH-BB18n, second half.** SH18n's second half on the pair's window. -/
theorem anchorUpdate_dvd {U : BlockUniverse Validator BlockId Payload} {I : ℕ}
    (C : Config Validator) (epsilon : ℚ) {e k : ℕ} (A : BlockId) (hk : k ∣ 2 ^ e) :
    anchorUpdate U I C (candidatesUpto (2 ^ e)) epsilon A k ∣ 2 ^ e :=
  update_dvd (ofAnchor U A I) C epsilon hk

/-! ## The support at each wave -/

variable {U : BlockUniverse Validator BlockId Payload}

/-- At wave two the support blocks are Odontoceti's references one round up, whose authors are
the core's `supporters`. -/
theorem creatorsOf_supportBlocks_two (L : BlockId) (r : ℕ) :
    creatorsOf U.block (supportBlocks U 2 L r) = supporters U L (r + 1) := by
  unfold supportBlocks supporters
  rw [if_pos rfl]

/-- At any other wave the support blocks are Async BlueBottle's cone votes two rounds up, whose
authors are its `supporters`. -/
theorem creatorsOf_supportBlocks_ne {w : ℕ} (hw : w ≠ 2) (L : BlockId) (r : ℕ) :
    creatorsOf U.block (supportBlocks U w L r) = AsyncBlueBottle.supporters U L r := by
  unfold supportBlocks AsyncBlueBottle.supporters
  rw [if_neg hw]

/-- Wave three reads Async BlueBottle's cone votes. -/
theorem supportBlocks_three (L : BlockId) (r : ℕ) :
    supportBlocks U 3 L r = AsyncBlueBottle.voters U L r := by
  unfold supportBlocks
  rw [if_neg (by decide)]

/-- At any wave but two the blame blocks are Async BlueBottle's blamers, whose authors are its
`blamers`. -/
theorem creatorsOf_blameBlocks_ne {w : ℕ} (hw : w ≠ 2) (a : Validator) (r : ℕ) :
    creatorsOf U.block (blameBlocks U w a r) = AsyncBlueBottle.blamers U a r := by
  unfold blameBlocks AsyncBlueBottle.blamers
  rw [if_neg hw]

/-- The window's supporters are among the rule's. -/
theorem card_support_le {ids : Finset BlockId} {w : ℕ} {L : BlockId} {r : ℕ} :
    (creatorsOf U.block (supportBlocks U w L r ∩ ids)).card ≤
      (creatorsOf U.block (supportBlocks U w L r)).card :=
  Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left)

/-! ## The evidence -/

/-- A quorum of supporters within the window is at least the indirect threshold. -/
theorem certified_of_commits (A : BlockId) (I r w : ℕ) (a : Validator)
    (h : (ofAnchor U A I).commits r w a = true) : (ofAnchor U A I).certified r w a = true := by
  simp only [ofAnchor, decide_eq_true_eq] at h ⊢
  obtain ⟨L, hL, hc⟩ := h
  exact ⟨L, hL, le_trans (by omega) hc⟩

/-- A quorum of blames within the window is one on the DAG, which leaves a candidate at most `2f`
supporters, below the indirect threshold `n − 3f`: the counting halves of O2 and ABB2. -/
theorem not_certified_of_skips (A : BlockId) (I r w : ℕ) (a : Validator)
    (h : (ofAnchor U A I).skips r w a = true) : (ofAnchor U A I).certified r w a = false := by
  simp only [ofAnchor, decide_eq_true_eq] at h
  simp only [ofAnchor, decide_eq_false_iff_not, not_exists, not_and, not_le]
  intro L hL
  obtain ⟨hLr, hLa, -⟩ := Finset.mem_filter.mp hL
  obtain ⟨-, hLround⟩ := mem_blocksAt.mp hLr
  have h5 := F.card_validators5
  have hblame : quorumCard Validator ≤ (creatorsOf U.block (blameBlocks U w a r)).card :=
    le_trans h (Finset.card_le_card (Finset.image_subset_image Finset.inter_subset_left))
  refine lt_of_le_of_lt card_support_le ?_
  by_cases hw : w = 2
  · subst hw
    rw [creatorsOf_supportBlocks_two]
    -- an omitter of the slot omits L in particular, so it blames L
    have hsub : creatorsOf U.block (blameBlocks U 2 a r) ⊆ blames U L (r + 1) := by
      intro v hv
      obtain ⟨q, hq, hqc⟩ := mem_creatorsOf.mp hv
      unfold blameBlocks at hq
      rw [if_pos rfl] at hq
      obtain ⟨hqr, hqn⟩ := Finset.mem_filter.mp hq
      obtain ⟨hqU, hqround⟩ := mem_blocksAt.mp hqr
      exact mem_blames.mpr ⟨q, hqU, hqround, fun hLq => hqn L hLq ⟨hLround, hLa⟩, hqc⟩
    have hsum := card_supporters_add_card_blames_le U.noEquivOn_honest card_compl_correct_le
      (L := L) (n := r + 1)
    have hle := Finset.card_le_card hsub
    omega
  · rw [creatorsOf_supportBlocks_ne hw]
    rw [creatorsOf_blameBlocks_ne hw] at hblame
    have hsum := AsyncBlueBottle.card_supporters_add_card_blamers_le (U := U) (L := L) (r := r)
      hLround
    rw [hLa] at hsum
    omega

/-- **SH-BB18g.** A quorum of supporters within the window is a quorum on the DAG, for a block of
the author at the round, under the wave's rule. -/
theorem commits_sound {A : BlockId} {I r w : ℕ} {a : Validator}
    (h : (ofAnchor U A I).commits r w a = true) :
    ∃ L ∈ blocksAt U r, (U.block L).creator = a ∧
      (w = 2 → Odontoceti.DirectCommit U L r) ∧ (w ≠ 2 → AsyncBlueBottle.DirectCommit U L r) := by
  simp only [ofAnchor, decide_eq_true_eq] at h
  obtain ⟨L, hL, hc⟩ := h
  obtain ⟨hLr, hLa, -⟩ := Finset.mem_filter.mp hL
  have hle := le_trans hc (card_support_le (U := U))
  refine ⟨L, hLr, hLa, fun hw => ?_, fun hw => ?_⟩
  · subst hw
    unfold Odontoceti.DirectCommit
    rwa [creatorsOf_supportBlocks_two] at hle
  · unfold AsyncBlueBottle.DirectCommit
    rwa [creatorsOf_supportBlocks_ne hw] at hle

/-! ## The window as a record -/

/-- The cone votes a view's block casts are the universe's: the histories coincide. -/
theorem voters_toRecord {V : View Validator BlockId Payload U} {L : BlockId} {r : ℕ} :
    AsyncBlueBottle.voters V.toRecord L r = AsyncBlueBottle.voters U L r ∩ V.ids := by
  ext q
  simp only [AsyncBlueBottle.mem_voters, BlockRecord.View.toRecord_ids,
    BlockRecord.View.toRecord_block, Finset.mem_inter]
  constructor
  · rintro ⟨hq, hqr, hv⟩
    exact ⟨⟨V.subset_ids hq, hqr, (MahiMahiPair.votes_toRecord hq).mp hv⟩, hq⟩
  · rintro ⟨⟨_, hqr, hv⟩, hq⟩
    exact ⟨hq, hqr, (MahiMahiPair.votes_toRecord hq).mpr hv⟩

/-- The supporters a view holds are the universe's cone voters within it. -/
theorem supporters_toRecord {V : View Validator BlockId Payload U} {L : BlockId} {r : ℕ} :
    AsyncBlueBottle.supporters V.toRecord L r =
      creatorsOf U.block (AsyncBlueBottle.voters U L r ∩ V.ids) := by
  unfold AsyncBlueBottle.supporters
  rw [voters_toRecord, BlockRecord.View.toRecord_block]

/-- The window marks committed at wave three exactly the authors whose round-`r` block the anchor's
history, read as a record, directly commits: a candidate at a round the window retains lies in the
history, and its cone votes within the window are its cone votes within the history, whose round
the window retains too. -/
theorem committedCount_eq_card_goodAt {I : ℕ} {A : BlockId} (hA : A ∈ U.ids) {r : ℕ}
    (hr : windowBottom U A I ≤ r) :
    committedCount (ofAnchor U A I) r 3 =
      (AsyncBlueBottle.goodAt (U.historyView A hA).toRecord r).card := by
  unfold committedCount
  congr 1
  ext a
  rw [Finset.mem_filter, AsyncBlueBottle.mem_goodAt]
  simp only [Finset.mem_univ, true_and, ofAnchor, decide_eq_true_eq,
    BlockRecord.View.toRecord_ids, BlockRecord.View.toRecord_block]
  constructor
  · rintro ⟨L, hL, hc⟩
    obtain ⟨hLr, hLa, hLw⟩ := Finset.mem_filter.mp hL
    obtain ⟨-, hLround⟩ := mem_blocksAt.mp hLr
    obtain ⟨hLh, -, -⟩ := Finset.mem_filter.mp hLw
    refine ⟨L, hLh, hLround, hLa, ?_⟩
    unfold AsyncBlueBottle.DirectCommit
    rw [supporters_toRecord]
    rw [supportBlocks_three] at hc
    refine le_trans hc (Finset.card_le_card (Finset.image_subset_image ?_))
    intro q hq
    obtain ⟨hqU, hqw⟩ := Finset.mem_inter.mp hq
    exact Finset.mem_inter.mpr ⟨hqU, (Finset.mem_filter.mp hqw).1⟩
  · rintro ⟨L, hLh, hLround, hLa, hdc⟩
    change L ∈ history U A at hLh
    have hLw : L ∈ windowIds U A I :=
      Finset.mem_filter.mpr ⟨hLh, by rw [hLround]; exact hr, round_le_of_mem_history hA hLh⟩
    refine ⟨L, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨history_subset_ids hA hLh, hLround⟩, hLa,
      hLw⟩, ?_⟩
    unfold AsyncBlueBottle.DirectCommit at hdc
    rw [supporters_toRecord] at hdc
    rw [supportBlocks_three]
    refine le_trans hdc (Finset.card_le_card (Finset.image_subset_image ?_))
    intro q hq
    obtain ⟨hqU, hqh⟩ := Finset.mem_inter.mp hq
    change q ∈ history U A at hqh
    refine Finset.mem_inter.mpr
      ⟨hqU, Finset.mem_filter.mpr ⟨hqh, ?_, round_le_of_mem_history hA hqh⟩⟩
    rw [(AsyncBlueBottle.mem_voters.mp hqU).2.1]
    omega

/-- **SH-BB18d.** ABB7 on the anchor's history as a record, whose committed candidates the window's
evidence marks at wave three. -/
theorem window_count {I : ℕ} {A : BlockId} (hA : A ∈ U.ids) {T : Finset Validator} {r : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hr : windowBottom U A I ≤ r)
    (hpop1 : PopulatedOn (U.historyView A hA).toRecord T (r + 1))
    (hpop2 : PopulatedOn (U.historyView A hA).toRecord T (r + 2)) :
    Fintype.card Validator - 3 * F.f ≤ committedCount (ofAnchor U A I) r 3 := by
  rw [committedCount_eq_card_goodAt hA hr]
  exact card_goodAt_of_populated ⟨hT, hcard, hpop1, hpop2⟩

/-- **SH-BB18i.** The count, over `n`, is the uniform coin's measure of the committed set. -/
theorem commitWeight_eq_commitProb {I : ℕ} {A : BlockId} (hA : A ∈ U.ids) {r : ℕ}
    (hr : windowBottom U A I ≤ r) :
    (committedCount (ofAnchor U A I) r 3 : ℝ≥0∞) / Fintype.card Validator =
      commitProb (AsyncBlueBottle.goodAt (U.historyView A hA).toRecord) r := by
  rw [committedCount_eq_card_goodAt hA hr, commitProb_eq]

end Replay

end BlueBottlePair

end Steelhead

end LeanDag
