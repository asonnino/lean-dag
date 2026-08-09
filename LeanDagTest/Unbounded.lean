import LeanDag.ViewSync
import LeanDagTest.Growth

/-!
# The bound is necessary

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
holds from time `0`. Yet `SynchronisedOn (Ugap N) Correct R` fails for
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
def gapRefs (b : ℕ) : Finset ℕ :=
  if b % 4 = 2 then Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4))
  else (Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4))).erase (4 * (b / 4) - 4 + 2)

theorem mem_gapRefs {b i : ℕ} :
    i ∈ gapRefs b ↔
      (4 * (b / 4) - 4 ≤ i ∧ i < 4 * (b / 4)) ∧ (b % 4 = 2 ∨ i ≠ 4 * (b / 4) - 4 + 2) := by
  unfold gapRefs
  by_cases h : b % 4 = 2
  · simp only [h, if_true, Finset.mem_Ico, true_or, and_true, if_pos]
  · simp only [if_neg h, Finset.mem_erase, Finset.mem_Ico]
    constructor
    · rintro ⟨hne, hlo, hhi⟩; exact ⟨⟨hlo, hhi⟩, Or.inr hne⟩
    · rintro ⟨⟨hlo, hhi⟩, hor⟩
      exact ⟨hor.resolve_left h, hlo, hhi⟩

/-- Block `b` sits at round `b / 4`, is authored by validator `b % 4`, and
references the round below except for validator `2`'s block. -/
def gapBlock (b : ℕ) : Block (Fin 4) ℕ Unit where
  round := b / 4
  creator := ⟨b % 4, by omega⟩
  refs := gapRefs b
  payload := ()

@[simp] theorem gapBlock_round (b : ℕ) : (gapBlock b).round = b / 4 := rfl
@[simp] theorem gapBlock_creator_val (b : ℕ) : ((gapBlock b).creator : ℕ) = b % 4 := rfl
@[simp] theorem gapBlock_refs (b : ℕ) : (gapBlock b).refs = gapRefs b := rfl

/-- The DAG of `Ugrow`'s shape, with validator `2` excluded from everyone
else's references. -/
def Ugap (N : ℕ) : BlockUniverse (Fin 4) ℕ Unit where
  ids := Finset.range (4 * (N + 1))
  block := gapBlock
  complete := by
    intro i hi j hj
    rw [Finset.mem_range] at hi ⊢
    rw [gapBlock_refs, mem_gapRefs] at hj
    omega
  valid := by
    intro i _
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [gapBlock_refs, mem_gapRefs] at hj
      simp only [gapBlock_round]
      omega
    · intro j hj k hk hjk
      rw [gapBlock_refs, mem_gapRefs] at hj hk
      have : (j % 4) = (k % 4) := by
        have := congrArg (fun (v : Fin 4) => (v : ℕ)) hjk
        simpa using this
      omega
    · -- validators `0`, `1` and `3` are always referenced, and three is a quorum
      intro h
      simp only [gapBlock_round] at h
      have hsub : ({0, 1, 3} : Finset (Fin 4)) ⊆ creators gapBlock (gapBlock i) := by
        intro x hx
        have hx2 : (x : ℕ) ≠ 2 := by fin_cases hx <;> decide
        have hxlt := x.isLt
        simp only [creators, creatorsOf, gapBlock_refs, Finset.mem_image]
        refine ⟨4 * (i / 4) - 4 + (x : ℕ), ?_, ?_⟩
        · rw [mem_gapRefs]; omega
        · apply Fin.ext
          simp only [gapBlock_creator_val]
          omega
      have hcard : ({0, 1, 3} : Finset (Fin 4)).card = 3 := by decide
      have := Finset.card_le_card hsub
      have hf : Faults.f (Fin 4) = 1 := rfl
      have hn : Fintype.card (Fin 4) = 4 := rfl
      omega
    · -- self-parent: the erased id is validator `2`'s, and `2` never erases
      intro h
      simp only [gapBlock_round] at h
      refine ⟨4 * (i / 4) - 4 + i % 4, ?_, ?_⟩
      · rw [gapBlock_refs, mem_gapRefs]
        by_cases h2 : i % 4 = 2
        · exact ⟨by omega, Or.inl h2⟩
        · exact ⟨by omega, Or.inr (by omega)⟩
      · apply Fin.ext
        simp only [gapBlock_creator_val]
        omega
  no_equivocation := by
    intro i _ j _ _ hc hr
    have hv : (i % 4) = (j % 4) := by
      have := congrArg (fun (v : Fin 4) => (v : ℕ)) hc
      simpa using this
    simp only [gapBlock_round] at hr
    omega

@[simp] theorem ugap_ids (N : ℕ) : (Ugap N).ids = Finset.range (4 * (N + 1)) := rfl
@[simp] theorem ugap_block (N : ℕ) : (Ugap N).block = gapBlock := rfl

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
def ugapGrowth (N : ℕ) : ViewGrowth (Ugap N) (Correct : Finset (Fin 4)) 0 N where
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 4 * N + 5
  delay := 1
  rounds_le b hb := by
    simp only [ugap_ids, Finset.mem_range] at hb
    simp only [ugap_block, gapBlock_round]
    omega
  waits _ _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 4 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  latest_mem _ _ := ⟨3, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _
  holds := gapHolds N
  holds_sub v t := by
    intro b hb
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range] at hb
    simp only [ugap_ids, Finset.mem_range]
    exact hb.1
  holds_own v _ n _ b hb hbc hbr := by
    have hv := v.isLt
    simp only [ugap_ids, Finset.mem_range] at hb
    simp only [ugap_block, gapBlock_round] at hbr
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
    simp only [ugap_ids, Finset.mem_range] at hc
    simp only [ugap_block, gapBlock_round] at hcr har
    have hcc' : c % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hcc
      simpa using this
    simp only [gapHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [ugap_block, gapBlock_refs, mem_gapRefs]
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
    · simp only [ugap_ids, Finset.mem_range]; omega
    · apply Fin.ext; simp only [ugap_block, gapBlock_creator_val]; omega
    · simp only [ugap_block, gapBlock_round]; omega
  builds v _ n _ hn _ := by
    have hv := v.isLt
    refine ⟨4 * (n + 1) + (v : ℕ), ?_, ?_, ?_⟩
    · simp only [ugap_ids, Finset.mem_range]; omega
    · apply Fin.ext; simp only [ugap_block, gapBlock_creator_val]; omega
    · simp only [ugap_block, gapBlock_round]; omega

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
    ¬ SynchronisedOn (Ugap N) (Correct : Finset (Fin 4)) R := by
  intro hsync
  have hmem : (4 * (R + 1) + 1) ∈ (Ugap N).ids := by
    simp only [ugap_ids, Finset.mem_range]; omega
  have hamem : (4 * R + 2) ∈ (Ugap N).ids := by
    simp only [ugap_ids, Finset.mem_range]; omega
  have := hsync R (le_refl R) _ hmem
    (by simp only [ugap_block, gapBlock_round]; omega)
    (by
      have : ((Ugap N).block (4 * (R + 1) + 1)).creator = (1 : Fin 4) := by
        apply Fin.ext; simp only [ugap_block, gapBlock_creator_val]; omega
      rw [this]; decide)
    _ hamem (by simp only [ugap_block, gapBlock_round]; omega)
    (by
      have : ((Ugap N).block (4 * R + 2)).creator = (2 : Fin 4) := by
        apply Fin.ext; simp only [ugap_block, gapBlock_creator_val]; omega
      rw [this]; decide)
  simp only [ugap_block, gapBlock_refs, mem_gapRefs] at this
  omega

/-- **The separation.** Every protocol clause holds, holdings converge from
time `0`, and coverage fails at every round below the horizon. So the
qualitative half of the network assumption does not yield
`SynchronisedOn`: the bound in `converges` is doing the work, and
`convergesWithin_iff_bounded` is a factoring of a genuine conjunction
rather than a restatement of one half. -/
theorem bound_is_necessary {N : ℕ} (hN : 0 < N) :
    ConvergesEventually (ugapGrowth N).holds (Correct : Finset (Fin 4)) ∧
      ¬ SynchronisedOn (Ugap N) (Correct : Finset (Fin 4)) 0 :=
  ⟨ugapGrowth_convergesEventually N, ugap_not_synchronisedOn 0 hN⟩

#print axioms ugapGrowth_convergesEventually
#print axioms ugap_not_synchronisedOn
#print axioms bound_is_necessary

end LeanDagTest
