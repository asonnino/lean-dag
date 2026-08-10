import LeanDag.SafeSkip.Basic
import LeanDag.SafeSkip.Invariance
import LeanDagTest.Unbounded
import LeanDagTest.Quantitative

/-!
# Safe Skip, witnessed

`Ucrash` is the round-robin scheme with validator `3` crashed after its
genesis block: validators `0`, `1` and `2` run full lines whose
references omit the absent author, and `3` owns exactly one block, id
`3`, at round `0`.

`ucrashMsg` is the Safe Skip message `3` sends on recovery: anchor `B1 =
3`, donor line `v2 = 1`, target round `r`. The filled block at round `k`
carries `1`'s references at that round plus the added self reference —
concretely, at round `1` the references become `{0, 1, 2, 3}`: the
copied `{0, 1, 2}` and the anchor, a full quorum of four distinct
authors where the donor's own block had three.

The two theorems of the construction are exercised on data: the gap
rounds are populated with `3` restored to the reliable set, and the
filled block at a leader round is directly skipped — every old block
blames it, since none can reference an id that did not exist.
-/

namespace LeanDagTest

open LeanDag

/-- The crashed universe: full lines for `0`, `1`, `2` with references
omitting the absent author; validator `3` owns its genesis only. -/
def Ucrash (N : ℕ) : BlockUniverse (Fin 4) ℕ Unit where
  ids := (Finset.range (4 * (N + 1))).filter fun b => b % 4 ≠ 3 ∨ b / 4 = 0
  block := rrBlock (omitRefs 3)
  complete := by
    intro i hi j hj
    simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
    rw [rrBlock_refs, mem_omitRefs] at hj
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    rw [h3] at hj
    constructor
    · omega
    · left
      omega
  valid := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_range] at hi
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [rrBlock_refs, mem_omitRefs, h3] at hj
      simp only [rrBlock_round]
      omega
    · intro j hj k hk hjk
      rw [rrBlock_refs, mem_omitRefs, h3] at hj hk
      have : (j % 4) = (k % 4) := by
        have := congrArg (fun (v : Fin 4) => (v : ℕ)) hjk
        simpa using this
      omega
    · intro h
      simp only [rrBlock_round] at h
      -- the three running validators are always referenced
      have hi3 : i % 4 ≠ 3 := by
        rcases hi.2 with h' | h'
        · exact h'
        · omega
      have hsub : (Finset.univ.erase (3 : Fin 4)) ⊆
          creators (rrBlock (omitRefs 3)) (rrBlock (omitRefs 3) i) := by
        intro y hy
        rw [Finset.mem_erase] at hy
        have hyx : (y : ℕ) ≠ 3 := fun hc => hy.1 (Fin.ext (by rw [hc]; rfl))
        have hylt := y.isLt
        simp only [creators, creatorsOf, rrBlock_refs, Finset.mem_image]
        refine ⟨4 * (i / 4) - 4 + (y : ℕ), ?_, ?_⟩
        · rw [mem_omitRefs, h3]; omega
        · apply Fin.ext
          simp only [rrBlock_creator_val]
          omega
      have hcard : (Finset.univ.erase (3 : Fin 4)).card = 3 := by decide
      have := Finset.card_le_card hsub
      have hf : Faults.f (Fin 4) = 1 := rfl
      have hn : Fintype.card (Fin 4) = 4 := rfl
      omega
    · intro h
      simp only [rrBlock_round] at h
      have hi3 : i % 4 ≠ 3 := by
        rcases hi.2 with h' | h'
        · exact h'
        · omega
      refine ⟨4 * (i / 4) - 4 + i % 4, ?_, ?_⟩
      · rw [rrBlock_refs, mem_omitRefs, h3]
        exact ⟨by omega, Or.inr (by omega)⟩
      · apply Fin.ext
        simp only [rrBlock_creator_val]
        omega
  no_equivocation := by
    intro i hi j hj _ hc hr
    simp only [Finset.mem_filter, Finset.mem_range] at hi hj
    have : (i % 4) = (j % 4) := by
      have := congrArg (fun (v : Fin 4) => (v : ℕ)) hc
      simpa using this
    simp only [rrBlock_round] at hr
    omega

@[simp] theorem ucrash_ids (N : ℕ) : (Ucrash N).ids =
    (Finset.range (4 * (N + 1))).filter (fun b => b % 4 ≠ 3 ∨ b / 4 = 0) := rfl
@[simp] theorem ucrash_block (N : ℕ) : (Ucrash N).block = rrBlock (omitRefs 3) := rfl

/-- The recovery message: anchor `3` (round `0`), donor line `1`, target
round `r`; fresh ids beyond the id range, decoded by subtraction. -/
def ucrashMsg (N r : ℕ) (hr : r ≤ N) : SkipMsg (Ucrash N) where
  v1 := 3
  B1 := 3
  v2 := 1
  r := r
  line k := 4 * k + 1
  fresh k := 4 * (N + 1) + k
  idx b := b - 4 * (N + 1)
  hB1uniq :=
    hB1uniq_of_correct
      (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Or.inr rfl⟩)
      (by apply Fin.ext; simp only [ucrash_block, rrBlock_creator_val]; decide)
      (by decide)
  hv12 := by decide
  hB1 := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Or.inr rfl⟩
  hB1c := by
    apply Fin.ext
    simp only [ucrash_block, rrBlock_creator_val]
    decide
  hline_mem k _ hk := by
    simp only [ucrash_ids, Finset.mem_filter, Finset.mem_range]
    omega
  hline_creator k _ _ := by
    apply Fin.ext
    simp only [ucrash_block, rrBlock_creator_val]
    omega
  hline_round k _ _ := by
    simp only [ucrash_block, rrBlock_round]
    omega
  hline_chain k hk1 hk2 := by
    have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    simp only [ucrash_block, rrBlock_round] at hk1
    simp only [ucrash_block, rrBlock_refs, mem_omitRefs, rrBlock_round, h3]
    omega
  hfresh_new k := by
    simp only [ucrash_ids, Finset.mem_filter, Finset.mem_range]
    omega
  hidx k := by omega
  hgap b hb hbc h1 h2 := by
    simp only [ucrash_ids, Finset.mem_filter, Finset.mem_range] at hb
    simp only [ucrash_block, rrBlock_round] at h1 h2
    have hbc' : b % 4 = 3 := by
      have := congrArg (fun (v : Fin 4) => (v : ℕ)) hbc
      simpa using this
    -- the filter admits an author-`3` block only at round `0`
    rcases hb.2 with h | h
    · exact h hbc'
    · omega

/-- The filled block at round `1`: the donor's references `{0, 1, 2}`
plus the anchor — four distinct authors where the donor had three. -/
example : ((ucrashMsg 2 2 (by omega)).skipFill.block
    ((ucrashMsg 2 2 (by omega)).fresh 1)).refs = {3, 0, 1, 2} := by decide

/-- The extension is a universe with exactly the old blocks plus one per
gap round: ten kept blocks and two filled. -/
example : (ucrashMsg 2 2 (by omega)).skipFill.ids.card = 12 := by decide

/-- **The gap is populated, on data**: with `3` restored, every gap
round carries blocks from `{1, 2, 3}`. -/
theorem ucrash_populated (N r : ℕ) (hr : r ≤ N) {k : ℕ}
    (hk1 : 0 < k) (hk2 : k ≤ r) :
    PopulatedOn (ucrashMsg N r hr).skipFill (insert 3 {1, 2}) k := by
  have hr0 : (ucrashMsg N r hr).r0 = 0 := by
    simp [SkipMsg.r0, ucrashMsg]
  refine SkipMsg.skipFill_populatedOn _ ?_ (by omega) hk2
  intro v hv
  have hv12 : (v : ℕ) = 1 ∨ (v : ℕ) = 2 := by
    fin_cases hv <;> simp
  have hv4 := v.isLt
  refine ⟨4 * k + (v : ℕ), ?_, ?_, ?_⟩
  · simp only [ucrash_ids, Finset.mem_filter, Finset.mem_range]
    omega
  · apply Fin.ext
    simp only [ucrash_block, rrBlock_creator_val]
    omega
  · simp only [ucrash_block, rrBlock_round]
    omega

/-- **No conjured commit, on data**: the filled block at round `1` is
directly skipped — every running validator's round-`2` block blames it. -/
theorem ucrash_directSkip (N : ℕ) (hN : 2 ≤ N) :
    DirectSkip (ucrashMsg N 2 hN).skipFill
      ((ucrashMsg N 2 hN).fresh 1) 1 := by
  have hr0 : (ucrashMsg N 2 hN).r0 = 0 := by
    simp [SkipMsg.r0, ucrashMsg]
  refine SkipMsg.directSkip_fresh _ (T := {0, 1, 2}) (by decide)
    (by change (3 : Fin 4) ∉ _; decide)
    ?_ (by rw [hr0]; omega) (by change (1 : ℕ) ≤ 2; omega)
  intro v hv
  have hv4 := v.isLt
  have hv3 : (v : ℕ) ≠ 3 := by fin_cases hv <;> decide
  refine ⟨4 * 2 + (v : ℕ), ?_, ?_, ?_⟩
  · simp only [ucrash_ids, Finset.mem_filter, Finset.mem_range]
    omega
  · apply Fin.ext
    simp only [ucrash_block, rrBlock_creator_val]
    omega
  · simp only [ucrash_block, rrBlock_round]
    omega

attribute [local instance 2000] rrSlots

/-- The view quorum the invariance theorem consumes, discharged for the
full view: three authors at every round above the gap. -/
theorem ucrash_full_hq (N r : ℕ) (hrN : r < N) :
    ∀ n, (ucrashMsg N r (le_of_lt hrN)).r0 < n → n ≤ r →
      Fintype.card (Fin 4) - Faults.f (Fin 4) ≤
        (creatorsOf (Ucrash N).block
          ((blocksAt (Ucrash N) (n + 1)) ∩ (View.full (Ucrash N)).ids)).card := by
  intro n _ hn2
  have hsub : (Finset.univ.erase (3 : Fin 4)) ⊆
      creatorsOf (Ucrash N).block
        ((blocksAt (Ucrash N) (n + 1)) ∩ (View.full (Ucrash N)).ids) := by
    intro y hy
    rw [Finset.mem_erase] at hy
    have hyx : (y : ℕ) ≠ 3 := fun hc => hy.1 (Fin.ext (by rw [hc]; rfl))
    have hylt := y.isLt
    refine mem_creatorsOf.mpr ⟨4 * (n + 1) + (y : ℕ), ?_, ?_⟩
    · refine Finset.mem_inter.mpr ⟨?_, ?_⟩
      · refine mem_blocksAt.mpr ⟨?_, ?_⟩
        · simp only [ucrash_ids, Finset.mem_filter, Finset.mem_range]
          omega
        · simp only [ucrash_block, rrBlock_round]
          omega
      · change _ ∈ (Ucrash N).ids
        simp only [ucrash_ids, Finset.mem_filter, Finset.mem_range]
        omega
    · apply Fin.ext
      simp only [ucrash_block, rrBlock_creator_val]
      omega
  have := Finset.card_le_card hsub
  have hcard : (Finset.univ.erase (3 : Fin 4)).card = 3 := by decide
  have hf : Faults.f (Fin 4) = 1 := rfl
  have hn : Fintype.card (Fin 4) = 4 := rfl
  omega

/-- **Verdict invariance, exercised**: every full-view verdict of the
crashed universe re-derives in the fill. -/
example (N r : ℕ) (hrN : r < N) {k : ℕ} {v : Option ℕ}
    (h : Decided (Ucrash N) (View.full (Ucrash N)) k v) :
    Decided (ucrashMsg N r (le_of_lt hrN)).skipFill
      ((ucrashMsg N r (le_of_lt hrN)).liftView (View.full (Ucrash N))) k v :=
  SkipMsg.decided_fill _ (ucrash_full_hq N r hrN) h

#print axioms LeanDag.SkipMsg.decided_fill
#print axioms LeanDag.SkipMsg.decided_fill_agree
#print axioms ucrash_populated
#print axioms ucrash_directSkip
#print axioms LeanDag.SkipMsg.skipFill_populatedOn
#print axioms LeanDag.SkipMsg.directSkip_fresh

end LeanDagTest
