import LeanDag.CausalHistory
-- Broad import: the counting argument below uses big operators, ordered
-- sums, pigeonhole and `nlinarith`. Narrowing this to specific modules is
-- not worth the churn -- the rest of the library keeps its targeted imports.
import Mathlib

/-!
# A common correct ancestor

`spec.md` §4, Phase 1b — T3a, T3b, T3c.

Persistence (T3) says a block *already backed by a quorum* survives forever.
This file says something is **always** backed, whether or not anyone arranged
it: across any three consecutive rounds, some correct validator's round-`r`
block ends up in the causal history of every round-`(r+2)` block. The
argument is a counting one, in the spirit of the Gather protocol's
common-core lemma.

Nothing here uses T3 — only T0, T1 and T2. The independence is the point:
T3b needs far fewer supporters than T3 needs quorum members, because its
supporters are *correct*, and dodging a correct validator means dodging its
one and only block.

Everything is parameterised by `p := (authorsAt U (r+1)).card`, the number of
validators holding a round-`(r+1)` block. A round-`(r+2)` block draws its
2f+1 referenced creators from those same `p`, so it misses exactly
`p - (2f+1)`. Low participation weakens the counting but narrows the room to
dodge by exactly as much, which is why no progress assumption is needed.

Thresholds are stated **additively** (`p ≤ k + 2 * F.f`) rather than as
`p - 2f ≤ k`. Truncated `ℕ` subtraction would silently collapse the
threshold to `0` whenever `p ≤ 2f` — precisely the degenerate range where no
round-`(r+2)` block exists — turning a vacuous case into an apparently
provable one.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The ids present at a given round. -/
def blocksAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  U.ids.filter (fun i => (U.block i).round = n)

/-- The validators holding a block at a given round. -/
def authorsAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset Validator :=
  creatorsOf U.block (blocksAt U n)

@[simp]
theorem mem_blocksAt {i : BlockId} {n : ℕ} :
    i ∈ blocksAt U n ↔ i ∈ U.ids ∧ (U.block i).round = n := by
  simp [blocksAt]

theorem mem_authorsAt {v : Validator} {n : ℕ} :
    v ∈ authorsAt U n ↔ ∃ i ∈ U.ids, (U.block i).round = n ∧ (U.block i).creator = v := by
  simp [authorsAt, mem_creatorsOf]
  tauto

/-- The creators of a round-`(n+1)` block's references all hold round-`n`
blocks. This is what forces a round-`(r+2)` block to choose its 2f+1
referenced creators from the same pool the counting argument ranges over. -/
theorem creators_refs_subset_authorsAt {c : BlockId} {n : ℕ}
    (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    creatorsOf U.block (U.block c).refs ⊆ authorsAt U n := by
  intro v hv
  rw [mem_creatorsOf] at hv
  obtain ⟨i, hi_mem, hi_creator⟩ := hv
  rw [mem_authorsAt]
  refine ⟨i, U.complete c hc i hi_mem, ?_, hi_creator⟩
  have := U.round_of_mem_refs hc hi_mem
  omega

/-- The round-`n` blocks authored by *correct* validators. The counting
argument ranges over these: a correct author has exactly one block per round
(T1), so `creator` is injective here and blocks and authors can be counted
interchangeably. -/
def correctBlocksAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  (blocksAt U n).filter (fun q => (U.block q).creator ∈ (Correct : Finset Validator))

theorem mem_correctBlocksAt {i : BlockId} {n : ℕ} :
    i ∈ correctBlocksAt U n ↔
      i ∈ U.ids ∧ (U.block i).round = n ∧ (U.block i).creator ∈ (Correct : Finset Validator) := by
  simp [correctBlocksAt, and_assoc]

/-- Distinct correct round-`n` blocks have distinct authors — non-equivocation
(T1) in the form the count needs. -/
theorem creator_injOn_correctBlocksAt {n : ℕ} :
    Set.InjOn (fun q => (U.block q).creator) (correctBlocksAt U n) := by
  intro q hq q' hq' h
  obtain ⟨hq_ids, hq_round, hq_corr⟩ := mem_correctBlocksAt.mp hq
  obtain ⟨hq'_ids, hq'_round, _⟩ := mem_correctBlocksAt.mp hq'
  exact U.eq_of_creator_eq hq_ids hq'_ids hq_corr rfl h.symm (by rw [hq_round, hq'_round])

theorem card_creatorsOf_correctBlocksAt {n : ℕ} :
    (creatorsOf U.block (correctBlocksAt U n)).card = (correctBlocksAt U n).card :=
  Finset.card_image_of_injOn creator_injOn_correctBlocksAt

theorem creatorsOf_correctBlocksAt_subset {n : ℕ} :
    creatorsOf U.block (correctBlocksAt U n) ⊆ (Correct : Finset Validator) := by
  intro v hv
  rw [mem_creatorsOf] at hv
  obtain ⟨q, hq, rfl⟩ := hv
  exact (mem_correctBlocksAt.mp hq).2.2

/-- The author pool at round `n` is covered by the correct authors together
with the Byzantine validators, bounding `p` by `l + b`. -/
theorem card_authorsAt_le {n : ℕ} :
    (authorsAt U n).card ≤ (correctBlocksAt U n).card + F.byzantine.card := by
  rw [← card_creatorsOf_correctBlocksAt]
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro v hv
  rw [mem_authorsAt] at hv
  obtain ⟨i, hi_ids, hi_round, hi_creator⟩ := hv
  by_cases hc : v ∈ (Correct : Finset Validator)
  · refine Finset.mem_union_left _ ?_
    rw [mem_creatorsOf]
    exact ⟨i, mem_correctBlocksAt.mpr ⟨hi_ids, hi_round, hi_creator ▸ hc⟩, hi_creator⟩
  · exact Finset.mem_union_right _ (by simpa using hc)

-- Only `supporters` needs decidable equality on ids: its defining filter
-- tests membership in a `Finset BlockId`. Everything above manages without.
variable [DecidableEq BlockId]

/-- The validators whose round-`n` block references `b`. -/
def supporters (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((blocksAt U n).filter (fun q => b ∈ (U.block q).refs))

theorem mem_supporters {b : BlockId} {n : ℕ} {v : Validator} :
    v ∈ supporters U b n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v := by
  simp [supporters, mem_creatorsOf]
  tauto

theorem supporters_subset_authorsAt {b : BlockId} {n : ℕ} :
    supporters U b n ⊆ authorsAt U n :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-- Validators that are both correct and back `b` with their round-`n`
block. This is exactly what T3b consumes. -/
def correctSupporters (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  supporters U b n ∩ (Correct : Finset Validator)

theorem correctSupporters_subset {b : BlockId} {n : ℕ} :
    correctSupporters U b n ⊆ supporters U b n := Finset.inter_subset_left

theorem correctSupporters_correct {b : BlockId} {n : ℕ} {v : Validator}
    (hv : v ∈ correctSupporters U b n) : v ∈ (Correct : Finset Validator) :=
  Finset.mem_of_mem_inter_right hv

/-- **T3a (Correct-support counting).** Some correct validator's round-`r`
block is backed by enough correct round-`(r+1)` validators to satisfy T3b's
threshold.

Double counting: each correct round-`(r+1)` block names at least `2f+1 - b`
correct round-`r` authors, and there are `l` such blocks spread over
`c = 3f+1 - b` correct validators, so some author `w` collects at least
`l(2f+1-b)/c`. The arithmetic obligation reduces to `c² ≤ f(l+c)`, which
`l ≤ c` turns into `c ≤ 2f` — impossible, since `b ≤ f` forces `c ≥ 2f+1`. -/
theorem exists_correct_common_support {r : ℕ}
    (hp : 2 * F.f + 1 ≤ (authorsAt U (r + 1)).card) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ (Correct : Finset Validator) ∧
      (authorsAt U (r + 1)).card ≤ (correctSupporters U bw (r + 1)).card + 2 * F.f := by
  classical
  -- Derive the ambient cardinality facts *before* abbreviating, so that
  -- `set` rewrites them too; otherwise `omega` sees `Correct.card` and
  -- `C.card` as unrelated atoms.
  have hcb := card_correct_add_byzantine (Validator := Validator)
  have hbf := F.card_byzantine
  have hE := card_authorsAt_le (U := U) (n := r + 1)
  have hlc : (correctBlocksAt U (r + 1)).card ≤ (Correct : Finset Validator).card := by
    rw [← card_creatorsOf_correctBlocksAt]
    exact Finset.card_le_card creatorsOf_correctBlocksAt_subset
  set L := correctBlocksAt U (r + 1) with hLdef
  set C := (Correct : Finset Validator) with hCdef
  set g : Validator → ℕ :=
    fun w => (L.filter (fun q => w ∈ creatorsOf U.block (U.block q).refs)).card with hgdef
  -- Count incidences (correct round-(r+1) block, correct round-r author) twice.
  have hdouble : ∑ q ∈ L, ((creatorsOf U.block (U.block q).refs) ∩ C).card = ∑ w ∈ C, g w := by
    have h1 : ∀ q : BlockId, ((creatorsOf U.block (U.block q).refs) ∩ C).card
        = ∑ w ∈ C, if w ∈ creatorsOf U.block (U.block q).refs then 1 else 0 := by
      intro q
      rw [Finset.inter_comm, ← Finset.filter_mem_eq_inter, Finset.card_filter]
    simp_rw [h1, hgdef, Finset.card_filter]
    exact Finset.sum_comm
  -- Each correct round-(r+1) block names 2f+1 validators, at most b Byzantine.
  have hper : ∀ q ∈ L,
      2 * F.f + 1 ≤ ((creatorsOf U.block (U.block q).refs) ∩ C).card + F.byzantine.card := by
    intro q hq
    obtain ⟨hq_ids, hq_round, _⟩ := mem_correctBlocksAt.mp hq
    have hquorum := U.creators_quorum hq_ids (by omega)
    have hsplit := Finset.card_inter_add_card_sdiff (creatorsOf U.block (U.block q).refs) C
    have hsdiff : ((creatorsOf U.block (U.block q).refs) \ C).card ≤ F.byzantine.card := by
      refine Finset.card_le_card fun x hx => ?_
      rw [Finset.mem_sdiff] at hx
      simpa [hCdef] using hx.2
    omega
  have hsum : L.card * (2 * F.f + 1) ≤ (∑ w ∈ C, g w) + L.card * F.byzantine.card := by
    rw [← hdouble]
    calc L.card * (2 * F.f + 1)
        = ∑ _q ∈ L, (2 * F.f + 1) := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ ∑ q ∈ L, (((creatorsOf U.block (U.block q).refs) ∩ C).card + F.byzantine.card) :=
          Finset.sum_le_sum hper
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul]
  -- Pigeonhole on the correct authors.
  have hC_ne : C.Nonempty := by
    rw [← Finset.card_pos]; omega
  obtain ⟨w, hw_mem, hw_max⟩ := C.exists_max_image g hC_ne
  have hpig : ∑ w' ∈ C, g w' ≤ C.card * g w := by
    calc ∑ w' ∈ C, g w' ≤ ∑ _w' ∈ C, g w := Finset.sum_le_sum fun x hx => hw_max x hx
      _ = C.card * g w := by rw [Finset.sum_const, smul_eq_mul]
  have hA : L.card * (2 * F.f + 1) ≤ C.card * g w + L.card * F.byzantine.card :=
    le_trans hsum (Nat.add_le_add_right hpig _)
  -- The arithmetic core: p ≤ (max degree) + 2f.
  have harith : (authorsAt U (r + 1)).card ≤ g w + 2 * F.f := by
    by_contra hcon
    push Not at hcon
    have h1 : g w + 2 * F.f + 1 ≤ L.card + F.byzantine.card := by omega
    have h2 : C.card * (g w + 2 * F.f + 1) ≤ C.card * (L.card + F.byzantine.card) :=
      Nat.mul_le_mul_left _ h1
    have hcge : 2 * F.f + 1 ≤ C.card := by omega
    have key : C.card * C.card ≤ F.f * (L.card + C.card) := by nlinarith [h2, hA]
    nlinarith [key, hlc, hcge]
  -- The maximiser has positive degree, so it really does author a round-r block.
  have hgw_pos : 0 < g w := by omega
  obtain ⟨q₀, hq₀⟩ := Finset.card_pos.mp hgw_pos
  rw [Finset.mem_filter] at hq₀
  obtain ⟨hq₀L, hq₀w⟩ := hq₀
  obtain ⟨hq₀_ids, hq₀_round, _⟩ := mem_correctBlocksAt.mp hq₀L
  rw [mem_creatorsOf] at hq₀w
  obtain ⟨bw, hbw_mem, hbw_creator⟩ := hq₀w
  have hbw_ids : bw ∈ U.ids := U.complete _ hq₀_ids _ hbw_mem
  have hbw_round : (U.block bw).round = r := by
    have := U.round_of_mem_refs hq₀_ids hbw_mem; omega
  have hw_correct : w ∈ C := hw_mem
  refine ⟨bw, hbw_ids, hbw_round, hbw_creator ▸ hw_correct, ?_⟩
  -- Every block counted by `g w` references `bw` (T1), and distinct such
  -- blocks have distinct correct authors, so they inject into the support set.
  have hsub : Finset.image (fun q => (U.block q).creator)
      (L.filter (fun q => w ∈ creatorsOf U.block (U.block q).refs))
      ⊆ correctSupporters U bw (r + 1) := by
    intro v hv
    simp only [Finset.mem_image, Finset.mem_filter] at hv
    obtain ⟨q, ⟨hqL, hqw⟩, rfl⟩ := hv
    obtain ⟨hq_ids, hq_round, hq_corr⟩ := mem_correctBlocksAt.mp hqL
    rw [mem_creatorsOf] at hqw
    obtain ⟨i', hi'_mem, hi'_creator⟩ := hqw
    have hi'_ids : i' ∈ U.ids := U.complete q hq_ids i' hi'_mem
    have hi'_round : (U.block i').round = r := by
      have := U.round_of_mem_refs hq_ids hi'_mem; omega
    have hib : i' = bw :=
      U.eq_of_creator_eq hi'_ids hbw_ids hw_correct hi'_creator hbw_creator
        (by rw [hi'_round, hbw_round])
    refine Finset.mem_inter.mpr ⟨?_, hq_corr⟩
    rw [mem_supporters]
    exact ⟨q, hq_ids, hq_round, hib ▸ hi'_mem, rfl⟩
  calc (authorsAt U (r + 1)).card ≤ g w + 2 * F.f := harith
    _ = (Finset.image (fun q => (U.block q).creator)
          (L.filter (fun q => w ∈ creatorsOf U.block (U.block q).refs))).card + 2 * F.f := by
        rw [Finset.card_image_of_injOn
          (creator_injOn_correctBlocksAt.mono (Finset.coe_subset.mpr (Finset.filter_subset _ _)))]
    _ ≤ _ := Nat.add_le_add_right (Finset.card_le_card hsub) _

/-- **T3b (Coverage).** A block supported by enough *correct* round-`(r+1)`
validators is reached by every round-`(r+2)` block.

The threshold is one short of what a round-`(r+2)` block can miss: it names
2f+1 of the `p` validators holding round-`(r+1)` blocks, so it omits
`p - (2f+1)`, and a support set of size `p - 2f` cannot be dodged. The
supporter it is forced to name is correct, so by non-equivocation its single
round-`(r+1)` block is the one referencing `b`. -/
theorem reaches_of_correct_support
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_sub : S ⊆ supporters U b (r + 1))
    (hS_correct : ∀ v ∈ S, v ∈ (Correct : Finset Validator))
    (hp : (authorsAt U (r + 1)).card ≤ S.card + 2 * F.f)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b := by
  set A := creatorsOf U.block (U.block c).refs with hA
  -- `c`'s referenced creators form a quorum, and both they and `S` live
  -- inside the round-`(r+1)` author pool.
  have hA_quorum : 2 * F.f + 1 ≤ A.card := U.creators_quorum hc (by omega)
  have hA_sub : A ⊆ authorsAt U (r + 1) :=
    creators_refs_subset_authorsAt hc (by omega)
  have hS_auth : S ⊆ authorsAt U (r + 1) := hS_sub.trans supporters_subset_authorsAt
  -- Their sizes overflow the pool, so they must meet.
  have hunion : (A ∪ S).card ≤ (authorsAt U (r + 1)).card :=
    Finset.card_le_card (Finset.union_subset hA_sub hS_auth)
  have hadd := Finset.card_union_add_card_inter A S
  have hinter : 0 < (A ∩ S).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hinter
  rw [Finset.mem_inter] at hv
  obtain ⟨hv_A, hv_S⟩ := hv
  -- Unfold both memberships into concrete ids.
  rw [hA, mem_creatorsOf] at hv_A
  obtain ⟨i, hi_mem, hi_creator⟩ := hv_A
  obtain ⟨q, hq_ids, hq_round, hq_ref, hq_creator⟩ := mem_supporters.mp (hS_sub hv_S)
  -- `v` is correct, so its round-`(r+1)` block is unique: `i = q`.
  have hi_ids : i ∈ U.ids := U.complete c hc i hi_mem
  have hi_round : (U.block i).round = r + 1 := by
    have := U.round_of_mem_refs hc hi_mem
    omega
  have hiq : i = q :=
    U.eq_of_creator_eq hi_ids hq_ids (hS_correct v hv_S) hi_creator hq_creator
      (by rw [hi_round, hq_round])
  exact Reaches.of_mem_refs hi_mem (Reaches.single (by rw [hiq]; exact hq_ref))

/-- **T3c (Common correct ancestor).** If any block exists at round `r+2`,
some correct validator's round-`r` block lies in the causal history of
*every* round-`(r+2)` block.

The only premise is that a round-`(r+2)` block exists — a fact about the DAG
in hand, not an assumption that anyone makes progress. Its own reference
quorum supplies the `2f+1` author bound T3a needs. -/
theorem exists_common_correct_ancestor {r : ℕ} {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ (Correct : Finset Validator) ∧
      ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c bw := by
  -- A round-(r+2) block names 2f+1 distinct round-(r+1) authors, so the
  -- author pool is at least that large -- exactly T3a's hypothesis.
  have hp : 2 * F.f + 1 ≤ (authorsAt U (r + 1)).card :=
    le_trans (U.creators_quorum hc₀ (by omega))
      (Finset.card_le_card (creators_refs_subset_authorsAt hc₀ (by omega)))
  obtain ⟨bw, hbw_ids, hbw_round, hbw_correct, hbw_support⟩ :=
    exists_correct_common_support (U := U) (r := r) hp
  refine ⟨bw, hbw_ids, hbw_round, hbw_correct, fun c hc hcr => ?_⟩
  exact reaches_of_correct_support correctSupporters_subset
    (fun _ hv => correctSupporters_correct hv) hbw_support hc hcr

end LeanDag
