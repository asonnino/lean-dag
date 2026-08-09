import LeanDag.ViewSync
import LeanDagTest.Partial

/-!
# View convergence, witnessed

`ugrowSkewView` is `ugrowSkew` (`LeanDagTest/Partial.lean`) with its
`covers` field replaced by the two clauses that field conflates: a
view-level network guarantee and the protocol's referencing rule. The
holdings function is the honest one for that model — validator `v` holds
every block whose author built it at least `delay = 2` before time `t` —
so `converges` is a statement about *views* with no mention of references,
and `references` is a statement about *blocks* with no mention of the
network.

The point of the witness is that the split is satisfiable at the same
constants: drift `2`, `delay = 2`, `timeout = 4`, all tight
(`ugrowSkew_drift_tight`). Reference coverage then comes out through
`ViewSync.toTiming`, so nothing downstream is re-proved.
-/

namespace LeanDagTest

open LeanDag

/-- What `v` holds at time `t`. In this model the block `b` sits at round
`b / 4` with author `b % 4` and is built at time `(b % 4) + 4 * (b / 4)`,
which is `b` itself — so "built at least `delay` ago" is `b + 2 ≤ t`, and
a validator's own block is in hand the moment it is built, `b ≤ t`. Both
disjuncts are needed: the first is what `converges` moves between
validators, the second is what `holds_own` supplies. -/
def skewHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    b + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ b ≤ t)

/-- The view-level witness: `ugrowSkew` with `covers` split into
`converges` (network) and `references` (protocol). -/
def ugrowSkewView (N : ℕ) : ViewSync (Ugrow N) {1, 2, 3} N where
  blk v n := 4 * n + (v : ℕ)
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 0
  delay := 2
  rounds_le := (ugrowSkew N).rounds_le
  blk_mem := (ugrowSkew N).blk_mem
  blk_creator := (ugrowSkew N).blk_creator
  blk_round := (ugrowSkew N).blk_round
  waits _ _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 4 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  latest_mem _ _ := ⟨3, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _
  holds := skewHolds N
  holds_own v hv n hn := by
    have hv4 := v.isLt
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, Or.inr ⟨?_, by omega⟩⟩
    omega
  holds_mono v s t hst := by
    intro b hb
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t _ := by
    intro b hb
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, Or.inl (by omega)⟩
  references v hv n hn a ha har := by
    have hv4 := v.isLt
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [ugrow_block, growBlock_round] at har
    simp only [ugrow_block, mem_growBlock_refs]
    omega

/-- **Reference coverage, from view convergence.** The witness satisfies
the view-level assumption, and `SynchronisedOn` follows — the derivation
of §6.8 with its network premise stated over views rather than over
references. -/
theorem ugrowSkewView_synchronised (N : ℕ) :
    SynchronisedOn (Ugrow N) {1, 2, 3} 0 :=
  (ugrowSkewView N).synchronisedOn_of_converges (by decide) (D := 2)
    (fun v hv w hw n _ _ => by
      obtain ⟨_, _⟩ := mem_T_bounds hv
      obtain ⟨_, _⟩ := mem_T_bounds hw
      show (w : ℕ) + 4 * n ≤ ((v : ℕ) + 4 * n) + 2
      omega)
    (le_refl 0) (fun n _ => by show 2 + 2 ≤ 4; omega)

/-- The reduction is definitional on the timing data, so every quantitative
result of `Timing.lean` reads off the view-level witness unchanged. -/
example (N : ℕ) : (ugrowSkewView N).toTiming.delay = 2 := rfl
example (N : ℕ) : (ugrowSkewView N).toTiming.built 1 0 = 1 := rfl

#print axioms ugrowSkewView_synchronised
#print axioms LeanDag.ViewSync.covers_of_converges

end LeanDagTest
