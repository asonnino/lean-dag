import LeanDag.Integration.ReGenesis
import LeanDag.SafeSkip.Invariance

/-!
# I1 — the fill enlarges cones, and what that costs

`integration.md` §5.6 predicted that `DoSValid` fails under the Safe
Skip fill. This file establishes the mechanism, which is the part worth
having: **the fill's blocks reach strictly more than the donor's do.**

`fillBlock` is the donor's references *plus* a self reference to `v1`'s
chain (P3′ forces it, report §12.1). So a filled block's cone is the
donor block's cone together with `v1`'s pre-crash history — and
`DoSValid` forbids a block from citing an author exposed **in its own
cone**. A larger cone can only expose more authors, while the citations
are inherited unchanged from the donor. That is the whole of the
predicted failure, and `reaches_B1_of_fill` below is its engine.

The contrast with re-genesis (I19a) is exact and worth keeping in view:
re-genesis adds a block with *no* references, which enlarges no cone
and cites nothing, so it preserves `DoSValid` outright. The fill adds
blocks with references, and the self reference it is obliged to add is
precisely what breaks the cone-based condition. **P3′ pays for itself
in §8 and charges for itself in §12.**
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The first filled block reaches the anchor: the self reference P3′
obliges is a reference like any other, and reachability follows it. -/
theorem reaches_B1_of_fill (sk : SkipMsg U) :
    Reaches sk.skipFill (sk.fresh (sk.r0 + 1)) sk.B1 := by
  refine Reaches.single ?_
  show sk.B1 ∈ (sk.skipFill.block (sk.fresh (sk.r0 + 1))).refs
  rw [sk.skipFill_block_fresh]
  simp only [SkipMsg.fillBlock, SkipMsg.prev, if_pos rfl]
  exact Finset.mem_insert_self _ _

/-- **The cone grows.** Everything the anchor reaches, the first filled
block reaches — so `v1`'s entire pre-crash history is inside the fill's
cone, whether or not the donor's block at that round could see any of
it.

This is I1's mechanism. `DoSValid` quantifies over a block's own cone,
so a citation inherited from the donor — innocuous in the donor's
smaller cone — can be a violation in the filled block's larger one. -/
theorem reaches_of_fill_of_reaches_B1 (sk : SkipMsg U) {x : BlockId}
    (h : Reaches U sk.B1 x) :
    Reaches sk.skipFill (sk.fresh (sk.r0 + 1)) x :=
  (reaches_B1_of_fill sk).trans
    ((sk.reaches_fill_old sk.hB1).mpr ⟨mem_ids_of_reaches sk.hB1 h, h⟩)

/-- The anchor's whole cone lies in the filled block's cone. Needs the
gap to be nonempty, which is when there is anything to fill. -/
theorem history_B1_subset_fill (sk : SkipMsg U) (hne : sk.r0 < sk.r) :
    history U sk.B1 ⊆ history sk.skipFill (sk.fresh (sk.r0 + 1)) := by
  have hmem : sk.fresh (sk.r0 + 1) ∈ sk.skipFill.ids :=
    Finset.mem_union_right _
      (sk.mem_freshIds.mpr ⟨sk.r0 + 1, by omega, by omega, rfl⟩)
  intro x hx
  rw [mem_history_iff sk.hB1] at hx
  rw [mem_history_iff hmem]
  exact reaches_of_fill_of_reaches_B1 sk hx

/-! ## The failure is local to the fill

The fill copies a donor block's references, and the donor is a block of
`U`, so `DoSValid U` already vouches for those citations *in the
donor's cone*. What the fill adds is the self reference report §12.1 is
obliged to add, which enlarges the cone. The question is whether that
can disturb anything **else**, and it cannot: an old block's cone
contains no filled block, because no old block references a fresh
identifier — SS3's observation once more.

So the exposure condition decomposes. `DoSValid` holds of the fill
exactly when it held of `U` and the filled blocks themselves are sound,
and the second half is a property of the fill alone. That makes it a
*checkable precondition*: a recipient computes the fill and inspects
its blocks, consulting no identity oracle and nothing outside the
message and its own DAG. In report §8's vocabulary the condition is
enforceable, which is the standard that section holds its clauses to.
-/

section Locality

variable (sk : SkipMsg U)

/-- An old block's cone is unchanged by the fill: reachability from an
old block stays among old blocks. -/
theorem history_skipFill_old {b : BlockId} (hb : b ∈ U.ids) :
    history sk.skipFill b = history U b := by
  ext i
  rw [mem_history_iff (sk.ids_subset_skipFill hb), mem_history_iff hb]
  constructor
  · intro h; exact ((sk.reaches_fill_old hb).mp h).2
  · intro h
    exact (sk.reaches_fill_old hb).mpr ⟨mem_ids_of_reaches hb h, h⟩

/-- Exposure is unchanged at an old block, in both directions. -/
theorem exposedIn_skipFill_old {b : BlockId} (hb : b ∈ U.ids) {X : Validator} :
    ExposedIn sk.skipFill b X ↔ ExposedIn U b X := by
  constructor
  · rintro ⟨x, hx, y, hy, hne, hxc, hyc, hr⟩
    rw [history_skipFill_old sk hb] at hx hy
    have hxo : x ∈ U.ids := mem_ids_of_reaches hb ((mem_history_iff hb).mp hx)
    have hyo : y ∈ U.ids := mem_ids_of_reaches hb ((mem_history_iff hb).mp hy)
    rw [sk.skipFill_block_old hxo] at hxc hr
    rw [sk.skipFill_block_old hyo] at hyc hr
    exact ⟨x, hx, y, hy, hne, hxc, hyc, hr⟩
  · rintro ⟨x, hx, y, hy, hne, hxc, hyc, hr⟩
    have hxo : x ∈ U.ids := mem_ids_of_reaches hb ((mem_history_iff hb).mp hx)
    have hyo : y ∈ U.ids := mem_ids_of_reaches hb ((mem_history_iff hb).mp hy)
    refine ⟨x, ?_, y, ?_, hne, ?_, ?_, ?_⟩
    · rw [history_skipFill_old sk hb]; exact hx
    · rw [history_skipFill_old sk hb]; exact hy
    · rw [sk.skipFill_block_old hxo]; exact hxc
    · rw [sk.skipFill_block_old hyo]; exact hyc
    · rw [sk.skipFill_block_old hxo, sk.skipFill_block_old hyo]; exact hr

/-- **I1.** The fill can break the exposure condition only at its own
blocks. Given `DoSValid U`, the extension is `DoSValid` as soon as each
filled block is sound — a condition on the fill alone, which a
recipient checks by computing the fill and inspecting it.

This is the form report §8 asks of its clauses: structural,
author-blind, and checkable by the party it binds. The predicted
failure (`history_B1_subset_fill`) is not thereby avoided — a fill
whose enlarged cone exposes a donor citation simply fails the check,
and is refused rather than accepted and unsound. -/
theorem dosValid_skipFill (hdos : DoSValid U)
    (hnew : ∀ k, sk.r0 < k → k ≤ sk.r →
      ∀ i ∈ (sk.skipFill.block (sk.fresh k)).refs,
        ¬ ExposedIn sk.skipFill (sk.fresh k) (sk.skipFill.block i).creator) :
    DoSValid sk.skipFill := by
  intro b hb i hi
  rcases Finset.mem_union.mp hb with ho | hf
  · -- an old block: its cone, and the condition, read as in `U`
    rw [sk.skipFill_block_old ho] at hi
    rw [exposedIn_skipFill_old sk ho,
      sk.skipFill_block_old (U.complete b ho i hi)]
    exact hdos b ho i hi
  · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
    exact hnew k hk1 hk2 i hi

/-! ## The check reduces to reachability

The obligation of `dosValid_skipFill` asks a recipient to compute
exposure over the fill's cone. It collapses to a **reachability test**
under a condition that holds in the ordinary case: *the donor's block
at each gap round already reaches the anchor*. That is what a donor
line does whenever it referenced `v1`'s last block, which it would
have, `v1` having been producing at `r0`.

Under it the fill's cone adds nothing but `v1`'s own new blocks
(`fill_cone_subset`), and those cannot form an equivocating pair: they
sit at distinct rounds, `hgap` excludes an old `v1` block at any of
them, and `hB1uniq` pins the anchor's round. What is left is the
donor's own cone, for which `DoSValid U` already vouches.

The second hypothesis is forced rather than chosen. `SkipMsg` records
only that the anchor is `v1`'s unique block *at its own round*
(report §12.1), which leaves open that `v1` equivocated before
crashing — and a fill's self reference would then cite an exposed
author. Non-equivocation of `v1` throughout is what the base model's
correctness and report §14's honesty each supply. -/

section Reachability

variable (sk : SkipMsg U)

theorem fill_cone_subset (sk : SkipMsg U)
    (hcov : ∀ k, sk.r0 < k → k ≤ sk.r → sk.B1 ∈ history U (sk.line k)) :
    ∀ k, sk.r0 < k → k ≤ sk.r → ∀ i, Reaches sk.skipFill (sk.fresh k) i →
      i ∈ sk.freshIds ∨ i ∈ history U (sk.line k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk1 hk2 i hreach
    have hR0 : sk.r0 = (U.block sk.B1).round := rfl
    have hlm := sk.hline_mem k (by omega) hk2
    rcases hreach.cases_head with rfl | ⟨j, hstep, hji⟩
    · exact Or.inl (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩)
    · -- unfold the first step: the self reference, or a donor reference
      have hstep' : j ∈ insert (sk.prev k) (U.block (sk.line k)).refs := by
        have : j ∈ (sk.skipFill.block (sk.fresh k)).refs := hstep
        rwa [sk.skipFill_block_fresh] at this
      rcases Finset.mem_insert.mp hstep' with hj | hj
      · -- the self reference
        subst hj
        by_cases hb : k = sk.r0 + 1
        · -- boundary: the anchor, whose cone the donor covers
          rw [SkipMsg.prev, if_pos hb] at hji
          obtain ⟨hio, hiU⟩ := (sk.reaches_fill_old sk.hB1).mp hji
          refine Or.inr (history_subset_of_reaches hlm
            ((mem_history_iff hlm).mp (hcov k hk1 hk2)) ?_)
          exact (mem_history_iff sk.hB1).mpr hiU
        · -- inside the gap: the previous filled block, by induction
          rw [SkipMsg.prev, if_neg hb] at hji
          rcases ih (k - 1) (by omega) (by omega) (by omega) i hji with h | h
          · exact Or.inl h
          · refine Or.inr (history_subset_of_reaches hlm ?_ h)
            exact Reaches.single (sk.hline_chain k (by omega) hk2)
      · -- a donor reference: old, and inside the donor's cone
        have hjo : j ∈ U.ids := U.complete _ hlm j hj
        obtain ⟨hio, hiU⟩ := (sk.reaches_fill_old hjo).mp hji
        refine Or.inr (history_subset_of_reaches hlm ?_ ((mem_history_iff hjo).mpr hiU))
        exact Reaches.single hj


/-- **I14.** The enforceable check reduces to reachability. If each
donor block reaches the anchor and `v1` never equivocates, the fill
preserves the exposure condition outright — no exposure computation
over the extension is needed.

This is the deployable form: a recipient verifies that the donor line
covers the anchor, which is one reachability query per gap round
against its own DAG. -/
theorem dosValid_skipFill_of_covered (hdos : DoSValid U)
    (hcov : ∀ k, sk.r0 < k → k ≤ sk.r → sk.B1 ∈ history U (sk.line k))
    (hv1ne : ∀ p ∈ U.ids, ∀ q ∈ U.ids, (U.block p).creator = sk.v1 →
      (U.block q).creator = sk.v1 → (U.block p).round = (U.block q).round → p = q) :
    DoSValid sk.skipFill := by
  refine dosValid_skipFill sk hdos (fun k hk1 hk2 i hi hexp => ?_)
  have hR0 : sk.r0 = (U.block sk.B1).round := rfl
  have hlm := sk.hline_mem k (by omega) hk2
  have hfk : sk.fresh k ∈ sk.skipFill.ids :=
    Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩)
  obtain ⟨x, hx, y, hy, hne, hxc, hyc, hr⟩ := hexp
  rw [mem_history_iff hfk] at hx hy
  -- each twin is one of `v1`'s new blocks, or lies in the donor's cone
  have hxs := fill_cone_subset sk hcov k hk1 hk2 x hx
  have hys := fill_cone_subset sk hcov k hk1 hk2 y hy
  rcases hxs with hxf | hxo <;> rcases hys with hyf | hyo
  · -- both fresh: equal rounds are equal gap indices, so the ids coincide
    obtain ⟨m, hm1, hm2, rfl⟩ := sk.mem_freshIds.mp hxf
    obtain ⟨m', hm1', hm2', rfl⟩ := sk.mem_freshIds.mp hyf
    rw [sk.skipFill_block_fresh, sk.skipFill_block_fresh] at hr
    simp only [SkipMsg.fillBlock] at hr
    exact hne (hr ▸ rfl)
  · -- one fresh, one old: an old `v1` block at a gap round is the crash
    obtain ⟨m, hm1, hm2, rfl⟩ := sk.mem_freshIds.mp hxf
    have hyU : y ∈ U.ids := mem_ids_of_reaches hlm ((mem_history_iff hlm).mp hyo)
    rw [sk.skipFill_block_fresh] at hxc hr
    rw [sk.skipFill_block_old hyU] at hyc hr
    simp only [SkipMsg.fillBlock] at hxc hr
    exact sk.hgap y hyU (hyc.trans hxc.symm) (by omega) (by omega)
  · obtain ⟨m, hm1, hm2, rfl⟩ := sk.mem_freshIds.mp hyf
    have hxU : x ∈ U.ids := mem_ids_of_reaches hlm ((mem_history_iff hlm).mp hxo)
    rw [sk.skipFill_block_fresh] at hyc hr
    rw [sk.skipFill_block_old hxU] at hxc hr
    simp only [SkipMsg.fillBlock] at hyc hr
    exact sk.hgap x hxU (hxc.trans hyc.symm) (by omega) (by omega)
  · -- both old: the donor's own cone, for which `DoSValid U` vouches
    have hxU : x ∈ U.ids := mem_ids_of_reaches hlm ((mem_history_iff hlm).mp hxo)
    have hyU : y ∈ U.ids := mem_ids_of_reaches hlm ((mem_history_iff hlm).mp hyo)
    rw [sk.skipFill_block_old hxU] at hxc hr
    rw [sk.skipFill_block_old hyU] at hyc hr
    -- the cited author is the anchor's, or one of the donor's
    have hi' : i ∈ insert (sk.prev k) (U.block (sk.line k)).refs := by
      have : i ∈ (sk.skipFill.block (sk.fresh k)).refs := hi
      rwa [sk.skipFill_block_fresh] at this
    rcases Finset.mem_insert.mp hi' with hip | hid
    · -- the self reference: `v1`, who does not equivocate
      subst hip
      have hpv : (sk.skipFill.block (sk.prev k)).creator = sk.v1 := by
        by_cases hb : k = sk.r0 + 1
        · rw [SkipMsg.prev, if_pos hb, sk.skipFill_block_old sk.hB1]; exact sk.hB1c
        · rw [SkipMsg.prev, if_neg hb, sk.skipFill_block_fresh]; rfl
      rw [hpv] at hxc hyc
      exact hne (hv1ne x hxU y hyU hxc hyc hr)
    · -- a donor citation: `DoSValid U` at the donor block
      have hio : i ∈ U.ids := U.complete _ hlm i hid
      rw [sk.skipFill_block_old hio] at *
      exact hdos (sk.line k) hlm i hid ⟨x, hxo, y, hyo, hne, hxc, hyc, hr⟩

end Reachability

end Locality

end Integration

end LeanDag
