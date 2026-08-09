import LeanDag.ViewSync
import LeanDagTest.Growth

/-!
# What the view-convergence route cannot do without

Three hypotheses of §6.9 are shown here to be load-bearing, each by a
model in which everything else holds and the conclusion fails: the bound
in `converges`, the starting round `R`, and the reliable set `T`. All
three run on one construction, `Uomit x`, which is `Ugrow` with validator
`x`'s blocks withheld from everyone else's references.

## The bound

`ViewSync.convergesWithin_iff_bounded` factors the network assumption into
a qualitative half — holdings converge at all — and a quantitative one —
from `gst` on the lag is at most `delay`. The development argues that the
second half cannot be dropped: a lag that merely exists cannot be ordered
against a build time, and that comparison is what `hbackoff` performs.

This file makes the argument a theorem, in the only form a necessity claim
can take: a model in which everything *except* the bound holds, and
coverage fails.

`Ugap` is `Ugrow` with one block per round withheld — validator `2`'s, from
everyone but validator `2`. The withheld blocks arrive eventually, after
every build in the run, so holdings do converge; they simply converge too
late to be referenced. Every protocol clause is satisfied, which the
`ViewGrowth` instance certifies field by field, and `ConvergesEventually`
holds from time `0`. Yet `SynchronisedOn (Uomit 2 N) Correct R` fails for
every `R` below the horizon.

The instance carries `gst = 4 * N + 5`, a time after every build in the
run, so `converges` is true of it but vacuously — which is the point.
`synchronisedOn_of_converges` demands `gst ≤ R`, and at such an `R`
coverage is vacuous for want of blocks above it. Nothing is contradicted;
what is shown is that the qualitative half alone carries none of the
weight.
-/

namespace LeanDagTest

open LeanDag

/-- The references of `Ugap`'s block `b`: the round below, less validator
`2`'s block — unless `b`'s own author is validator `2`, who must reference
its own previous block to satisfy the self-parent clause. -/
def omitRefs (x : Fin 4) (b : ℕ) : Finset ℕ :=
  if b % 4 = (x : ℕ) then Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4))
  else (Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4))).erase (4 * (b / 4) - 4 + (x : ℕ))

theorem mem_omitRefs {x : Fin 4} {b i : ℕ} :
    i ∈ omitRefs x b ↔
      (4 * (b / 4) - 4 ≤ i ∧ i < 4 * (b / 4)) ∧
        (b % 4 = (x : ℕ) ∨ i ≠ 4 * (b / 4) - 4 + (x : ℕ)) := by
  unfold omitRefs
  by_cases h : b % 4 = (x : ℕ)
  · simp only [h, if_true, Finset.mem_Ico, true_or, and_true, if_pos]
  · simp only [if_neg h, Finset.mem_erase, Finset.mem_Ico]
    constructor
    · rintro ⟨hne, hlo, hhi⟩; exact ⟨⟨hlo, hhi⟩, Or.inr hne⟩
    · rintro ⟨⟨hlo, hhi⟩, hor⟩
      exact ⟨hor.resolve_left h, hlo, hhi⟩

/-- The DAG of the round-robin scheme, with validator `x` excluded from
everyone else's references.

Only the two clauses the reference set controls are proved here; the rest
of validity is `rrUniverse`'s, since the block layout is the shared one. -/
def Uomit (x : Fin 4) (N : ℕ) : BlockUniverse (Fin 4) ℕ Unit :=
  rrUniverse N (omitRefs x)
    (fun b i hi => (mem_omitRefs.mp hi).1)
    (by
      -- the three validators other than `x` are always referenced
      intro i h
      have hsub : (Finset.univ.erase x) ⊆
          creators (rrBlock (omitRefs x)) (rrBlock (omitRefs x) i) := by
        intro y hy
        rw [Finset.mem_erase] at hy
        have hyx : (y : ℕ) ≠ (x : ℕ) := fun hc => hy.1 (Fin.ext hc)
        have hylt := y.isLt
        have hxlt := x.isLt
        simp only [creators, creatorsOf, rrBlock_refs, Finset.mem_image]
        refine ⟨4 * (i / 4) - 4 + (y : ℕ), ?_, ?_⟩
        · rw [mem_omitRefs]; omega
        · apply Fin.ext
          simp only [rrBlock_creator_val]
          omega
      have hcard : (Finset.univ.erase x).card = 3 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ x), Finset.card_univ]
        rfl
      have := Finset.card_le_card hsub
      omega)
    (by
      -- `x` is exempt from its own erasure, so every author keeps a parent
      intro i h
      have hxlt := x.isLt
      rw [mem_omitRefs]
      by_cases h2 : i % 4 = (x : ℕ)
      · exact ⟨by omega, Or.inl h2⟩
      · exact ⟨by omega, Or.inr (by omega)⟩)

@[simp] theorem uomit_ids (x : Fin 4) (N : ℕ) :
    (Uomit x N).ids = Finset.range (4 * (N + 1)) := rfl
@[simp] theorem uomit_block (x : Fin 4) (N : ℕ) :
    (Uomit x N).block = rrBlock (omitRefs x) := rfl

/-- **Coverage fails whenever the omitted validator is inside the set.**
`y`'s block of round `R+1` does not reference `x`'s block of round `R`.
This is the shared negative fact behind both witnesses below. -/
theorem uomit_not_synchronisedOn {N : ℕ} {x y : Fin 4} (hxy : y ≠ x)
    {T : Finset (Fin 4)} (hx : x ∈ T) (hy : y ∈ T) (R : ℕ) (hR : R < N) :
    ¬ SynchronisedOn (Uomit x N) T R := by
  intro hsync
  have hxlt := x.isLt
  have hylt := y.isLt
  have hyx : (y : ℕ) ≠ (x : ℕ) := fun hc => hxy (Fin.ext hc)
  have hbmem : (4 * (R + 1) + (y : ℕ)) ∈ (Uomit x N).ids := by
    simp only [uomit_ids, Finset.mem_range]; omega
  have hamem : (4 * R + (x : ℕ)) ∈ (Uomit x N).ids := by
    simp only [uomit_ids, Finset.mem_range]; omega
  have hbc : ((Uomit x N).block (4 * (R + 1) + (y : ℕ))).creator = y := by
    apply Fin.ext; simp only [uomit_block, rrBlock_creator_val]; omega
  have hac : ((Uomit x N).block (4 * R + (x : ℕ))).creator = x := by
    apply Fin.ext; simp only [uomit_block, rrBlock_creator_val]; omega
  have := hsync R (le_refl R) _ hbmem
    (by simp only [uomit_block, rrBlock_round]; omega)
    (by rw [hbc]; exact hy) _ hamem
    (by simp only [uomit_block, rrBlock_round]; omega)
    (by rw [hac]; exact hx)
  simp only [uomit_block, rrBlock_refs, mem_omitRefs] at this
  omega

/-- What `v` holds at time `t`: everything except validator `2`'s blocks,
which reach the others only at `4 * N + 5` — after every build in the run,
since the last is at `3 + 4 * N`. -/
def gapHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    b % 4 ≠ 2 ∨ (v : ℕ) = 2 ∨ 4 * N + 5 ≤ t

/-- **Every protocol clause, and convergence with a bound placed beyond the
run.** The instance exists to certify the clauses field by field; its
`gst` is deliberately after every build, so `converges` holds without
saying anything about the run. -/
def ugapGrowth (N : ℕ) : ViewGrowth (Uomit 2 N) (Correct : Finset (Fin 4)) 0 N where
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 4 * N + 5
  delay := 1
  rounds_le b hb := by
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round]
    omega
  waits _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 4 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  latest_mem _ _ := ⟨3, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _
  holds := gapHolds N
  holds_sub v t := by
    intro b hb
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range] at hb
    simp only [uomit_ids, Finset.mem_range]
    exact hb.1
  holds_own v _ n _ b hb hbc hbr := by
    have hv := v.isLt
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round] at hbr
    have hbc' : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa using this
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range]
    refine ⟨hb, ?_⟩
    by_cases h2 : (v : ℕ) = 2
    · exact Or.inr (Or.inl h2)
    · exact Or.inl (by omega)
  holds_mono v s t hst := by
    intro b hb
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨hb.1, ?_⟩
    rcases hb.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (by omega))
  converges v _ w _ t ht := by
    intro b hb
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, Or.inr (Or.inr (by omega))⟩
  references v _ n hn c hc hcc hcr a ha har := by
    have hv := v.isLt
    simp only [uomit_ids, Finset.mem_range] at hc
    simp only [uomit_block, rrBlock_round] at hcr har
    have hcc' : c % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hcc
      simpa using this
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [uomit_block, rrBlock_refs, mem_omitRefs]
    -- the build is at `v + 4 * (n+1) ≤ 3 + 4 * N`, before the late arrival
    have hlate : ¬ (4 * N + 5 ≤ (v : ℕ) + 4 * (n + 1)) := by omega
    refine ⟨by omega, ?_⟩
    by_cases h2 : (v : ℕ) = 2
    · exact Or.inl (by omega)
    · rcases ha.2 with h | h | h
      · exact Or.inr (by omega)
      · exact absurd h h2
      · exact absurd h hlate
  base v _ := by
    have hv := v.isLt
    refine ⟨(v : ℕ), ?_, ?_, ?_⟩
    · simp only [uomit_ids, Finset.mem_range]; omega
    · apply Fin.ext; simp only [uomit_block, rrBlock_creator_val]; omega
    · simp only [uomit_block, rrBlock_round]; omega
  builds v hv n _ hn _ :=
    rrUniverse_populatedOn _ _ _ _ _ _ (show n + 1 ≤ N by omega) v hv

/-- **Convergence without a bound, from time `0`.** Holdings do converge:
whatever anyone holds, everyone holds by `4 * N + 5`. No GST, no `delay`. -/
theorem ugapGrowth_convergesEventually (N : ℕ) :
    ConvergesEventually (ugapGrowth N).holds (Correct : Finset (Fin 4)) := by
  intro v _ w _ t
  refine ⟨4 * N + 5, ?_⟩
  intro b hb
  simp only [ugapGrowth, gapHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
  exact ⟨hb.1, Or.inr (Or.inr (by omega))⟩

/-- **And coverage fails anyway**, at every round the horizon leaves room
for: validator `1`'s block of round `R+1` does not reference validator
`2`'s block of round `R`, and both authors are correct. -/
theorem ugap_not_synchronisedOn {N : ℕ} (R : ℕ) (hR : R < N) :
    ¬ SynchronisedOn (Uomit 2 N) (Correct : Finset (Fin 4)) R :=
  uomit_not_synchronisedOn (x := 2) (y := 1) (by decide) (by decide) (by decide) R hR

/-- **The separation.** Every protocol clause holds, holdings converge from
time `0`, and coverage fails at every round below the horizon. So the
qualitative half of the network assumption does not yield
`SynchronisedOn`: the bound in `converges` is doing the work, and
`convergesWithin_iff_bounded` is a factoring of a genuine conjunction
rather than a restatement of one half. -/
theorem bound_is_necessary {N : ℕ} (hN : 0 < N) :
    ConvergesEventually (ugapGrowth N).holds (Correct : Finset (Fin 4)) ∧
      ¬ SynchronisedOn (Uomit 2 N) (Correct : Finset (Fin 4)) 0 :=
  ⟨ugapGrowth_convergesEventually N, ugap_not_synchronisedOn 0 hN⟩

/-! ## The starting round is forced

`viewsConvergeOn_toDelivery` concludes from `R` on, under `gst ≤ R`. This
model shows that side condition cannot be dropped: it is a genuine
`ViewGrowth` whose `gst` lies beyond the run, and the untimed condition
fails outright on the delivery it induces. Validator `2` holds its own
round-`0` block when it builds, and validator `1` does not.

So the `R`-relativisation of the bridge in §6.9 is forced by the
structure rather than chosen for convenience. -/
theorem ugap_not_viewsConvergeOn {N : ℕ} (hN : 0 < N) :
    ¬ ViewsConvergeOn (ugapGrowth N).toDelivery (Correct : Finset (Fin 4)) 0 := by
  intro h
  have h2 : (2 : Fin 4) ∈ (Correct : Finset (Fin 4)) := by decide
  have h1 : (1 : Fin 4) ∈ (Correct : Finset (Fin 4)) := by decide
  have hb : (2 : ℕ) ∈ (ugapGrowth N).toDelivery.held 2 0 := by
    rw [ViewGrowth.mem_toDelivery]
    refine ⟨?_, ?_, h2⟩
    · simp only [ugapGrowth, gapHolds, Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, Or.inr (Or.inl rfl)⟩
    · simp only [uomit_block, rrBlock_round]
  have hbc : ((Uomit 2 N).block 2).creator ∈ (Correct : Finset (Fin 4)) := by
    have : ((Uomit 2 N).block 2).creator = (2 : Fin 4) := by
      apply Fin.ext; simp only [uomit_block, rrBlock_creator_val]; rfl
    rw [this]; exact h2
  have hcon := h 2 h2 1 h1 0 (Nat.zero_le _) 2 hb hbc
  rw [ViewGrowth.mem_toDelivery] at hcon
  have := hcon.1
  simp only [ugapGrowth, gapHolds, Finset.mem_filter, Finset.mem_range] at this
  rcases this.2 with hx | hx | hx
  · exact hx rfl
  · exact absurd hx (by decide)
  · omega

/-! ## The reliable set is forced

The bridge derives `ViewsConvergeOn T R`, never `ViewsConverge`. That is
not an artefact of how `toDelivery` treats validators outside `T`: with a
proper subset `T ⊊ Correct`, coverage over `T` is *derivable* while
coverage over `Correct` is *false*, and the second statement is about the
DAG alone, independent of any delivery.

`Uomit 3` withholds validator `3`'s blocks from everyone's references.
Taking `T = {1, 2}` — two correct validators, with the correct validator
`3` outside — every clause holds at `gst = 0` with a real bound of `1`,
so unlike the model above the network assumption is satisfied properly
rather than vacuously. -/

theorem mem_T12_bounds {v : Fin 4} (hv : v ∈ ({1, 2} : Finset (Fin 4))) :
    1 ≤ (v : ℕ) ∧ (v : ℕ) ≤ 2 := by fin_cases hv <;> exact ⟨by decide, by decide⟩

/-- What `v` holds: everything except validator `3`'s blocks, which reach
nobody but `3` itself. No time dependence — the starvation is permanent,
so no bound is at issue here. -/
def starveHolds (N : ℕ) (v : Fin 4) (_t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b => b % 4 ≠ 3 ∨ (v : ℕ) = 3

/-- **A structure over a proper subset of `Correct`**, satisfied at
`gst = 0` and `delay = 1`.

A `ViewSync` rather than a `ViewGrowth`: `T` has two members and is
therefore not a quorum, so production is not derivable here — correctly,
since two validators cannot form one. Coverage needs no quorum, and it is
coverage the claim is about. -/
def ustarveSync (N : ℕ) : ViewSync (Uomit 3 N) ({1, 2} : Finset (Fin 4)) N where
  blk v n := 4 * n + (v : ℕ)
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 0
  delay := 1
  rounds_le b hb := by
    simp only [uomit_ids, Finset.mem_range] at hb
    simp only [uomit_block, rrBlock_round]
    omega
  blk_mem v hv n hn := by
    obtain ⟨_, _⟩ := mem_T12_bounds hv
    simp only [uomit_ids, Finset.mem_range]; omega
  blk_creator v hv n _ := by
    obtain ⟨_, _⟩ := mem_T12_bounds hv
    apply Fin.ext; simp only [uomit_block, rrBlock_creator_val]; omega
  blk_round v hv n _ := by
    obtain ⟨_, _⟩ := mem_T12_bounds hv
    simp only [uomit_block, rrBlock_round]; omega
  waits _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 2 + 4 * n
  built_le_latest v hv _ _ := by obtain ⟨_, _⟩ := mem_T12_bounds hv; omega
  latest_mem _ _ := ⟨2, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _
  holds := starveHolds N
  holds_own v hv n hn := by
    obtain ⟨h1, h2⟩ := mem_T12_bounds hv
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, Or.inl (by omega)⟩
  holds_mono v s t _ := by
    intro b hb
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact hb
  converges v hv w hw t _ := by
    obtain ⟨_, hv2⟩ := mem_T12_bounds hv
    obtain ⟨_, _⟩ := mem_T12_bounds hw
    intro b hb
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨hb.1, Or.inl ?_⟩
    rcases hb.2 with h | h
    · exact h
    · omega
  references v hv n hn a ha har := by
    obtain ⟨h1, h2⟩ := mem_T12_bounds hv
    simp only [uomit_block, rrBlock_round] at har
    simp only [starveHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [uomit_block, rrBlock_refs, mem_omitRefs]
    refine ⟨by omega, Or.inr ?_⟩
    rcases ha.2 with h | h
    · omega
    · omega

/-- **Coverage over `T` is derived** — the network assumption is met
properly here, at `gst = 0` with a real bound, so the route of §6.9 runs
to completion. -/
theorem ustarve_synchronisedOn (N : ℕ) :
    SynchronisedOn (Uomit 3 N) ({1, 2} : Finset (Fin 4)) 0 :=
  (ustarveSync N).synchronisedOn_of_converges (by decide) (D := 1)
    (fun v hv w hw n _ _ => by
      obtain ⟨_, _⟩ := mem_T12_bounds hv
      obtain ⟨_, _⟩ := mem_T12_bounds hw
      change (w : ℕ) + 4 * n ≤ ((v : ℕ) + 4 * n) + 1
      omega)
    (le_refl 0) (fun n _ => by change 1 + 1 ≤ 4; omega)

/-- **And coverage over `Correct` is false.** Validator `3` is correct and
outside `T`, and nobody references its blocks. -/
theorem ustarve_not_synchronisedOn {N : ℕ} (hN : 0 < N) :
    ¬ SynchronisedOn (Uomit 3 N) (Correct : Finset (Fin 4)) 0 :=
  uomit_not_synchronisedOn (x := 3) (y := 1) (by decide) (by decide) (by decide) 0 hN

/-- **The reliable set cannot be widened.** With `T ⊊ Correct`, the timed
structure yields coverage over `T` and coverage over `Correct` fails — a
statement about the DAG, so the relativisation is a property of the
setting and not of how `toDelivery` was defined.

`ViewsConverge` over the induced delivery fails a fortiori, and for the
same reason: validator `3` builds on nothing anyone else can see. -/
theorem reliable_set_is_forced {N : ℕ} (hN : 0 < N) :
    ({1, 2} : Finset (Fin 4)) ⊂ (Correct : Finset (Fin 4)) ∧
      SynchronisedOn (Uomit 3 N) ({1, 2} : Finset (Fin 4)) 0 ∧
      ¬ SynchronisedOn (Uomit 3 N) (Correct : Finset (Fin 4)) 0 :=
  ⟨by decide, ustarve_synchronisedOn N, ustarve_not_synchronisedOn hN⟩

#print axioms ustarve_synchronisedOn
#print axioms reliable_set_is_forced
#print axioms ugap_not_viewsConvergeOn
#print axioms ugapGrowth_convergesEventually
#print axioms ugap_not_synchronisedOn
#print axioms bound_is_necessary

end LeanDagTest
