import LeanDag.Liveness

/-!
# Safe Skip: rejoining after a crash, in one message

A validator that crashes and recovers faces a gap: liveness rests on
correct validators building in every round (P8), skipping rounds is
known to break it, and producing the missing blocks one by one costs a
round trip per round of downtime. **Safe Skip** closes the gap with a
single message. The recovering validator `v1` names a block `B2` at
round `r` on another validator `v2`'s history line, and its own last
block `B1`; the message *denotes* one block per gap round, deterministic
given the DAG: at each round the filled block carries the references of
`v2`'s block on the line, **plus one added self reference** to `v1`'s
block of the round below — `B1` at the boundary, the previous filled
block above it.

The added self reference is not an optimisation but a validity
requirement: `ValidWrt.self_parent` (P3′) demands that every non-genesis
block reference a block by its own creator, and `v2`'s references cannot
supply one — `v1` authored nothing in the gap. With it, every clause of
validity holds: the copied references sit one round below (P1 of the
line), `v1` appears among the authors exactly once (in the gap there is
no `v1`-authored block for the line to have referenced, and at the
boundary the only candidate is `B1` itself, by non-equivocation), and
the reference quorum only grows.

The denotation is `skipFill`: a universe extending `U` with the filled
blocks, every old block untouched. What this file proves:

* `skipFill` **is** a `BlockUniverse` — validity, completeness and
  non-equivocation survive the fill;
* old blocks and their references are preserved verbatim
  (`skipFill_block_old`), so every store, view and certificate built on
  `U` reads the same in the extension;
* the gap is populated (`skipFill_populatedOn`): with `v1` restored,
  `PopulatedOn` holds at every gap round, which is the production
  hypothesis liveness consumes;
* a filled block that lands on a leader slot is **directly skipped**
  (`directSkip_fresh`): its only supporter is `v1`'s own line, and every
  other reliable validator's block at the round above blames it. The
  fill cannot conjure a commit for a slot the network already passed —
  the mechanism restores production without touching consensus.

Full verdict invariance across the fill — every `Decided U V k v`
re-derives in `skipFill U`, and hence agrees with every verdict reached
after recovery — is `decided_fill` and `decided_fill_agree` in
`Invariance.lean`, the `decided_chop` analogue for extension rather than
truncation.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The denotation of a Safe Skip message, together with the freshness
data an implementation supplies (new ids for the filled blocks and their
decoder).

`line` is `v2`'s history line: one block per round from `r0 := round B1`
up to `r`, each referencing the one below — the chain the message's `B2`
pins by following self-parents. `hgap` is the crash itself: `v1`
authored nothing strictly between `B1` and `r`. -/
structure SkipMsg (U : BlockUniverse Validator BlockId Payload) where
  /-- The recovering validator. -/
  v1 : Validator
  /-- Its last block before the crash. -/
  B1 : BlockId
  /-- The donor of the reference structure. -/
  v2 : Validator
  /-- The target round — the round of the pinned block `B2 = line r`. -/
  r : ℕ
  /-- `v2`'s history line, meaningful on rounds `[round B1, r]`. -/
  line : ℕ → BlockId
  /-- Fresh ids for the filled blocks, and their decoder. -/
  fresh : ℕ → BlockId
  idx : BlockId → ℕ
  /-- `B1` is `v1`'s only block at its round — the whole of what the
  boundary argument needs. Stated directly rather than as `v1 ∈ Correct`
  because the two are not interchangeable in every fault model:
  non-equivocation gives it for a correct `v1` (`hB1uniq_of_correct`),
  and the hybrid model of report §14 gives it for a *crash-prone* one,
  which is the case Safe Skip exists to serve. -/
  hB1uniq : ∀ j ∈ U.ids, (U.block j).creator = v1 →
    (U.block j).round = (U.block B1).round → j = B1
  hv12 : v1 ≠ v2
  hB1 : B1 ∈ U.ids
  hB1c : (U.block B1).creator = v1
  hline_mem : ∀ k, (U.block B1).round ≤ k → k ≤ r → line k ∈ U.ids
  hline_creator : ∀ k, (U.block B1).round ≤ k → k ≤ r →
    (U.block (line k)).creator = v2
  hline_round : ∀ k, (U.block B1).round ≤ k → k ≤ r →
    (U.block (line k)).round = k
  hline_chain : ∀ k, (U.block B1).round < k → k ≤ r →
    line (k - 1) ∈ (U.block (line k)).refs
  hfresh_new : ∀ k, fresh k ∉ U.ids
  hidx : ∀ k, idx (fresh k) = k
  /-- The crash: `v1` authored nothing in the gap. -/
  hgap : ∀ b ∈ U.ids, (U.block b).creator = v1 →
    (U.block B1).round < (U.block b).round → (U.block b).round ≤ r → False

/-- **The boundary condition from correctness.** For a `v1` outside the
ambient model's Byzantine set, non-equivocation pins its round-`r0`
block to `B1`. This is how a `SkipMsg` is built in the base fault
model, and it is what the `hB1uniq` field generalises: report §14's
hybrid model discharges the same field for a *crash-prone* `v1`, whom
`Correct` excludes. -/
theorem hB1uniq_of_correct {v1 : Validator} {B1 : BlockId}
    (hB1 : B1 ∈ U.ids) (hB1c : (U.block B1).creator = v1)
    (hv1 : v1 ∈ (Correct : Finset Validator)) :
    ∀ j ∈ U.ids, (U.block j).creator = v1 →
      (U.block j).round = (U.block B1).round → j = B1 :=
  fun j hj hjc hjr => U.eq_of_creator_eq hj hB1 hv1 hjc hB1c hjr

namespace SkipMsg

variable (sk : SkipMsg U)

/-- The round of the anchor block — the bottom of the gap. -/
def r0 : ℕ := (U.block sk.B1).round

/-- The self reference of the filled block at round `k`: the anchor at
the boundary, the previous filled block above it. -/
def prev (k : ℕ) : BlockId :=
  if k = sk.r0 + 1 then sk.B1 else sk.fresh (k - 1)

/-- The filled block at gap round `k`: `v2`'s references at that round,
plus the added self reference. -/
def fillBlock (k : ℕ) : Block Validator BlockId Payload where
  round := k
  creator := sk.v1
  refs := insert (sk.prev k) (U.block (sk.line k)).refs
  payload := (U.block (sk.line k)).payload

/-- The gap rounds, as a `Finset`. -/
def gap : Finset ℕ := (Finset.range (sk.r + 1)).filter (fun k => sk.r0 < k)

/-- The ids of the filled blocks. -/
def freshIds : Finset BlockId := sk.gap.image sk.fresh

theorem mem_freshIds {b : BlockId} :
    b ∈ sk.freshIds ↔ ∃ k, sk.r0 < k ∧ k ≤ sk.r ∧ b = sk.fresh k := by
  simp only [freshIds, gap, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨k, ⟨h2, h1⟩, h3⟩; exact ⟨k, h1, by omega, h3.symm⟩
  · rintro ⟨k, h1, h2, h3⟩; exact ⟨k, ⟨by omega, h1⟩, h3.symm⟩

/-- **The denotation.** `U`, extended with one filled block per gap
round; every old block looked up unchanged. -/
def skipFill : BlockUniverse Validator BlockId Payload where
  ids := U.ids ∪ sk.freshIds
  block b := if b ∈ U.ids then U.block b else sk.fillBlock (sk.idx b)
  complete := by
    intro i hi j hj
    rcases Finset.mem_union.mp hi with ho | hf
    · rw [if_pos ho] at hj
      exact Finset.mem_union_left _ (U.complete i ho j hj)
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hj
      simp only [fillBlock, Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · -- the self reference: the anchor, or the previous filled block
        by_cases hb : k = sk.r0 + 1
        · simp only [prev, if_pos hb]
          exact Finset.mem_union_left _ sk.hB1
        · simp only [prev, if_neg hb]
          refine Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k - 1, ?_, ?_, rfl⟩)
          · omega
          · omega
      · -- a copied reference: old, by completeness of `U` at the line
        exact Finset.mem_union_left _
          (U.complete _ (sk.hline_mem k (by omega) hk2) j hj)
  valid := by
    intro i hi
    rcases Finset.mem_union.mp hi with ho | hf
    · -- old blocks: `U`'s validity, reference lookups unchanged
      rw [if_pos ho]
      have hv := U.valid i ho
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [if_pos (U.complete i ho j hj)]
        exact hv.predecessor j hj
      · intro j hj l hl
        rw [if_pos (U.complete i ho j hj), if_pos (U.complete i ho l hl)]
        exact hv.distinct_creators j hj l hl
      · intro hr
        refine le_trans (hv.quorum hr) (Finset.card_le_card ?_)
        intro c hc
        unfold creators creatorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
        simp only
        rw [if_pos (U.complete i ho j hj)]
        exact hjc
      · intro hr
        obtain ⟨j, hj, hjc⟩ := hv.self_parent hr
        exact ⟨j, hj, by rw [if_pos (U.complete i ho j hj)]; exact hjc⟩
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx]
      have hlm := sk.hline_mem k (by omega) hk2
      have hlv := U.valid _ hlm
      have hlr := sk.hline_round k (by omega) hk2
      -- the self reference is an old id at round `k − 1` with creator `v1`
      have hprev_old : sk.prev k ∈ U.ids ∨ sk.prev k = sk.fresh (k - 1) := by
        by_cases hb : k = sk.r0 + 1
        · exact Or.inl (by simp only [prev, if_pos hb]; exact sk.hB1)
        · exact Or.inr (by simp only [prev, if_neg hb])
      have hprev_round : (if sk.prev k ∈ U.ids then U.block (sk.prev k)
          else sk.fillBlock (sk.idx (sk.prev k))).round = k - 1 := by
        by_cases hb : k = sk.r0 + 1
        · simp only [prev, if_pos hb, if_pos sk.hB1]
          show (U.block sk.B1).round = k - 1
          omega
        · simp only [prev, if_neg hb, if_neg (sk.hfresh_new (k - 1)), sk.hidx]
          rfl
      have hprev_creator : (if sk.prev k ∈ U.ids then U.block (sk.prev k)
          else sk.fillBlock (sk.idx (sk.prev k))).creator = sk.v1 := by
        by_cases hb : k = sk.r0 + 1
        · simp only [prev, if_pos hb, if_pos sk.hB1]
          exact sk.hB1c
        · simp only [prev, if_neg hb, if_neg (sk.hfresh_new (k - 1)), sk.hidx]
          rfl
      -- no copied reference is `v1`-authored, except possibly the anchor itself
      have hno_v1 : ∀ j ∈ (U.block (sk.line k)).refs,
          (U.block j).creator = sk.v1 → j = sk.prev k := by
        intro j hj hjc
        have hjo := U.complete _ hlm j hj
        have hjr : (U.block j).round = k - 1 := by
          have := hlv.predecessor j hj
          omega
        by_cases hb : k = sk.r0 + 1
        · -- boundary: non-equivocation pins it to the anchor
          simp only [prev, if_pos hb]
          exact sk.hB1uniq j hjo hjc (by omega)
        · -- inside the gap: the crash forbids it
          exact (sk.hgap j hjo hjc (by omega) (by omega)).elim
      refine ⟨?_, ?_, ?_, ?_⟩
      · -- P1: the self reference and every copied reference sit at `k − 1`
        intro j hj
        simp only [fillBlock, Finset.mem_insert] at hj
        rcases hj with rfl | hj
        · rw [hprev_round]; show k - 1 + 1 = k; omega
        · rw [if_pos (U.complete _ hlm j hj)]
          have := hlv.predecessor j hj
          show (U.block j).round + 1 = k
          omega
      · -- P2: copied references are distinct by the line's P2; the self
        -- reference's author appears nowhere else
        intro j hj l hl hjl
        simp only [fillBlock, Finset.mem_insert] at hj hl
        rcases hj with rfl | hj <;> rcases hl with rfl | hl
        · rfl
        · rw [hprev_creator] at hjl
          rw [if_pos (U.complete _ hlm l hl)] at hjl
          exact (hno_v1 l hl hjl.symm).symm
        · rw [hprev_creator] at hjl
          rw [if_pos (U.complete _ hlm j hj)] at hjl
          exact hno_v1 j hj hjl
        · rw [if_pos (U.complete _ hlm j hj), if_pos (U.complete _ hlm l hl)] at hjl
          exact hlv.distinct_creators j hj l hl hjl
      · -- P3: the copied quorum survives, since lookups of old ids agree
        intro _
        have hq := hlv.quorum (by show 0 < (U.block (sk.line k)).round; omega)
        refine le_trans hq ?_
        refine Finset.card_le_card ?_
        intro c hc
        unfold creators creatorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, ?_, ?_⟩
        · simp only [fillBlock, Finset.mem_insert]
          exact Or.inr hj
        · simp only
          rw [if_pos (U.complete _ hlm j hj)]
          exact hjc
      · -- P3′: the added self reference
        intro _
        exact ⟨sk.prev k, Finset.mem_insert_self _ _, hprev_creator⟩
  no_equivocation := by
    intro i hi j hj hic hcc hrr
    rcases Finset.mem_union.mp hi with ho | hf <;>
      rcases Finset.mem_union.mp hj with ho' | hf'
    · rw [if_pos ho] at hic hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact U.no_equivocation i ho j ho' hic hcc hrr
    · -- an old block equal in author and round to a filled one: the
      -- author is `v1`, and the crash forbids it
      obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf'
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_pos ho] at hic hcc hrr
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hcc hrr
      exact (sk.hgap i ho hcc
        (by simp only [fillBlock] at hrr; omega)
        (by simp only [fillBlock] at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hic hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact (sk.hgap j ho' hcc.symm
        (by simp only [fillBlock] at hrr; omega)
        (by simp only [fillBlock] at hrr; omega)).elim
    · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      obtain ⟨l, hl1, hl2, rfl⟩ := sk.mem_freshIds.mp hf'
      rw [if_neg (sk.hfresh_new k), sk.hidx] at hrr
      rw [if_neg (sk.hfresh_new l), sk.hidx] at hrr
      simp only [fillBlock] at hrr
      exact hrr ▸ rfl

/-- Old blocks read unchanged: every store, view and certificate built
on `U` sees the same data in the extension. -/
@[simp] theorem skipFill_block_old {b : BlockId} (hb : b ∈ U.ids) :
    sk.skipFill.block b = U.block b := if_pos hb

@[simp] theorem skipFill_block_fresh {k : ℕ} :
    sk.skipFill.block (sk.fresh k) = sk.fillBlock k := by
  simp only [skipFill, if_neg (sk.hfresh_new k), sk.hidx]

theorem ids_subset_skipFill : U.ids ⊆ sk.skipFill.ids :=
  Finset.subset_union_left

/-- **The gap is populated.** With `v1` restored to the reliable set,
every gap round carries a `v1` block — the production hypothesis
liveness consumes, recovered from one message. -/
theorem skipFill_populatedOn {T : Finset Validator} {k : ℕ}
    (hpop : PopulatedOn U T k) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    PopulatedOn sk.skipFill (insert sk.v1 T) k := by
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · refine ⟨sk.fresh k, ?_, ?_, ?_⟩
    · exact Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩)
    · rw [sk.skipFill_block_fresh]; rfl
    · rw [sk.skipFill_block_fresh]; rfl
  · obtain ⟨b, hb, hbc, hbr⟩ := hpop v hv
    exact ⟨b, sk.ids_subset_skipFill hb,
      by rw [sk.skipFill_block_old hb]; exact hbc,
      by rw [sk.skipFill_block_old hb]; exact hbr⟩

/-- **The fill cannot conjure a commit.** A filled block landing on a
leader slot is directly skipped: no old block references a fresh id, so
every reliable validator's block at the round above blames it. The
mechanism restores production without touching the slots the network
already passed. -/
theorem directSkip_fresh {T : Finset Validator} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hv1T : sk.v1 ∉ T)
    (hpop : PopulatedOn U T (k + 1)) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    DirectSkip sk.skipFill (sk.fresh k) k := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨b, hb, hbc, hbr⟩ := hpop v hv
  refine mem_blames.mpr ⟨b, ?_, ?_, ?_, ?_⟩
  · exact sk.ids_subset_skipFill hb
  · rw [sk.skipFill_block_old hb]; exact hbr
  · -- an old block cannot reference a fresh id
    rw [sk.skipFill_block_old hb]
    intro hmem
    exact sk.hfresh_new k (U.complete b hb _ hmem)
  · rw [sk.skipFill_block_old hb]; exact hbc

end SkipMsg

end LeanDag
