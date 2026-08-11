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

end Locality

end Integration

end LeanDag
