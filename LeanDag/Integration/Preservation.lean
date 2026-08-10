import LeanDag.GC.Chop
import LeanDag.SafeSkip.Basic
import LeanDag.Hybrid.Faults

/-!
# Preservation: the transformer × invariant table, layer U

The integration arc's core move (`integration.md` §3.1). Each lemma
here has the shape

    I U  →  I (F U)

for a named invariant `I` and a universe transformer `F`, so that every
property stated against named invariants transfers to the transformed
universe with no further proof. The table this file fills:

| Invariant | `chop U G` | `skipFill` |
|:---|:---|:---|
| `HonestNoEquiv` | I2 | I3 |
| `SynchronisedOn` | I4 | I5 — *refuted*, see `Integration/Coverage.lean` |

`Populated`, `DoSValid` and the verdict facts already had their cells
filled by the arcs themselves (`populated_chop`, `dosValid_chop`,
`decided_chop`; SS2, SS5).

One wrinkle recurs and is worth naming once: `chopBlock` rebases rounds
to `round − G`, so equal *chopped* rounds do not by themselves give
equal original rounds — truncated subtraction is faithful only above
the cut, and the `chop` filter supplies `G ≤ round` on both sides to
close the gap. Every round-sensitive `chop` lemma below pays it.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-! ## I2 — truncation preserves honest non-equivocation

The lemma that makes §14 (hybrid) compose with §9 (garbage collection):
a hybrid-model universe stays a hybrid-model universe below a horizon.
Truncation removes blocks and never adds them, and `HonestNoEquiv` is
universally quantified over pairs of retained blocks, so it restricts
downward. -/

section Chop

variable [H : HybridFaults Validator]
variable {U : BlockUniverse Validator BlockId Payload} {G : ℕ}

/-- **I2.** Truncation preserves honest non-equivocation. -/
theorem honestNoEquiv_chop (hne : HonestNoEquiv U) :
    HonestNoEquiv (chop U G) := by
  intro i hi j hj hib hij hround
  rw [mem_chop_ids] at hi hj
  simp only [chop_block_eq, chopBlock_creator, chopBlock_round] at hib hij hround
  -- rounds are rebased by `−G`; the filter pins both above the cut,
  -- where the subtraction is faithful
  exact hne i hi.1 j hj.1 hib hij (by omega)

end Chop

/-! ## I4 — truncation preserves coverage, above the cut

Coverage transfers, with the round offset the truncation introduces:
a chopped round `n` is original round `G + n`, so a chopped universe is
synchronised from `R'` whenever the original is synchronised from
`R ≤ G + R'`. The base layer is not an exception here, unlike
`supporters_chop`: the clause only constrains blocks at chopped round
`n + 1 ≥ 1`, whose references `chop` retains. -/

section Coverage

variable [F : Faults Validator]
variable {U : BlockUniverse Validator BlockId Payload} {G : ℕ}
variable {T : Finset Validator} {R R' : ℕ}

/-- **I4.** Truncation preserves coverage, with the horizon offset.

The referencing block sits at chopped round `n + 1`, hence at original
round `G + n + 1`, strictly above the cut — so `chop` retains its
references verbatim and the original clause applies directly. -/
theorem synchronisedOn_chop (hs : SynchronisedOn U T R) (hGR : R ≤ G + R') :
    SynchronisedOn (chop U G) T R' := by
  intro n hn b hb hbround hbcreator a ha haround hacreator
  rw [mem_chop_ids] at hb ha
  simp only [chop_block_eq, chopBlock_round] at hbround haround
  simp only [chop_block_eq, chopBlock_creator] at hbcreator hacreator
  -- the referrer is strictly above the cut, so its references survive
  have hb_lt : G < (U.block b).round := by omega
  rw [chop_block_eq, chopBlock_refs_of_lt hb_lt]
  exact hs (G + n) (by omega) b hb.1 (by omega) hbcreator a ha.1 (by omega) hacreator

end Coverage

/-! ## I3 — the fill preserves honest non-equivocation

The recovering validator is honest, so the blocks its fill creates must
not equivocate against its own history. That is exactly what
`skipFill`'s own `no_equivocation` field proves for the *derived*
correct class; this is the same argument at the wider honest class, and
it turns on the same clause — `hgap`, the crash itself. A fresh block
sits at a gap round, an old block by `v1` at a gap round contradicts
`hgap`, and two fresh blocks at one round are one block. -/

section Fill

variable [H : HybridFaults Validator]
variable {U : BlockUniverse Validator BlockId Payload}

/-- **I3.** The Safe Skip fill preserves honest non-equivocation. -/
theorem honestNoEquiv_skipFill (sk : SkipMsg U) (hne : HonestNoEquiv U) :
    HonestNoEquiv sk.skipFill := by
  intro i hi j hj hib hij hround
  rcases Finset.mem_union.mp hi with ho | hf <;>
    rcases Finset.mem_union.mp hj with ho' | hf'
  · -- both old: the hypothesis, verbatim
    rw [sk.skipFill_block_old ho] at hib hij hround
    rw [sk.skipFill_block_old ho'] at hij hround
    exact hne i ho j ho' hib hij hround
  · -- old against fresh: an old `v1` block at a gap round is the crash
    obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf'
    have hR0 : sk.r0 = (U.block sk.B1).round := rfl
    rw [sk.skipFill_block_old ho] at hij hround
    rw [sk.skipFill_block_fresh] at hij hround
    exact (sk.hgap i ho hij
      (by simp only [SkipMsg.fillBlock] at hround; omega)
      (by simp only [SkipMsg.fillBlock] at hround; omega)).elim
  · -- fresh against old: the same, on the other side
    obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
    have hR0 : sk.r0 = (U.block sk.B1).round := rfl
    rw [sk.skipFill_block_old ho'] at hij hround
    rw [sk.skipFill_block_fresh] at hij hround
    exact (sk.hgap j ho' hij.symm
      (by simp only [SkipMsg.fillBlock] at hround; omega)
      (by simp only [SkipMsg.fillBlock] at hround; omega)).elim
  · -- both fresh: equal rounds are equal gap indices
    obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
    obtain ⟨l, hl1, hl2, rfl⟩ := sk.mem_freshIds.mp hf'
    rw [sk.skipFill_block_fresh, sk.skipFill_block_fresh] at hround
    simp only [SkipMsg.fillBlock] at hround
    exact hround ▸ rfl

end Fill

end Integration

end LeanDag
