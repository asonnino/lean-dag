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

end Integration

end LeanDag
