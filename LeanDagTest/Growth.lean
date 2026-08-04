import Mathlib
import LeanDag.Liveness

/-!
# `Ugrow` — a witness family for `Live`

`liveness.md` §4.4, §7. The non-vacuity check for the liveness primitives.

Every other model in `LeanDagTest` is a `Fin n` of fixed height, checked by
`decide`. None can serve here: `Live U N` demands blocks at every round up to
`N`, so a witness has to exist at *every* horizon, and `BlockId` has to be
infinite even though each `U.ids` is finite.

`Ugrow N` is the obvious such DAG over `Fin 4` validators (`f = 1`):

- `BlockId := ℕ`, with block `b` at round `b / 4`, authored by `b % 4`
- `ids := Finset.range (4 * (N + 1))` — rounds `0 … N`, four blocks each
- refs are the *whole* previous round, written `Finset.Ico (4 * r - 4) (4 * r)`

The `Ico` form is chosen so membership is an arithmetic fact `omega` can
discharge, and so the genesis case needs no branch: at `r = 0` truncated
subtraction makes it `Ico 0 0 = ∅`.

**Why this file exists.** The first draft of `Live` had no horizon, and was
*unsatisfiable* — L1 was proved against it and said nothing. It was caught by
sitting down to write this file. The staging rule that follows: a definition
gets a witness before anything is proved from it.
-/

namespace LeanDagTest

open LeanDag

instance : Faults (Fin 4) where
  f := 1
  byzantine := {0}
  card_validators := by decide
  card_byzantine := by decide

/-- Block `b` sits at round `b / 4`, is authored by validator `b % 4`, and
references every block of the round below. -/
def growBlock (b : ℕ) : Block (Fin 4) ℕ Unit where
  round := b / 4
  creator := ⟨b % 4, by omega⟩
  refs := Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4))
  payload := ()

@[simp] theorem growBlock_round (b : ℕ) : (growBlock b).round = b / 4 := rfl

@[simp] theorem growBlock_creator_val (b : ℕ) : ((growBlock b).creator : ℕ) = b % 4 := rfl

@[simp] theorem growBlock_refs (b : ℕ) :
    (growBlock b).refs = Finset.Ico (4 * (b / 4) - 4) (4 * (b / 4)) := rfl

theorem mem_growBlock_refs {b i : ℕ} :
    i ∈ (growBlock b).refs ↔ 4 * (b / 4) - 4 ≤ i ∧ i < 4 * (b / 4) :=
  Finset.mem_Ico

/-- The DAG grown to round `N`: four blocks per round, rounds `0` to `N`. -/
def Ugrow (N : ℕ) : BlockUniverse (Fin 4) ℕ Unit where
  ids := Finset.range (4 * (N + 1))
  block := growBlock
  complete := by
    intro i hi j hj
    rw [Finset.mem_range] at hi ⊢
    rw [mem_growBlock_refs] at hj
    omega
  valid := by
    intro i _
    refine ⟨?_, ?_, ?_⟩
    · intro j hj
      rw [mem_growBlock_refs] at hj
      simp only [growBlock_round]
      omega
    · intro j hj k hk hjk
      rw [mem_growBlock_refs] at hj hk
      have : (j % 4) = (k % 4) := by
        have := congrArg (fun (v : Fin 4) => (v : ℕ)) hjk
        simpa using this
      omega
    · intro h
      simp only [growBlock_round] at h
      -- the four ids of the round below carry four distinct authors
      have hcard : (creators growBlock (growBlock i)).card = 4 := by
        rw [creators, creatorsOf, Finset.card_image_of_injOn, growBlock_refs,
          Nat.card_Ico]
        · omega
        · intro a ha b hb hab
          rw [Finset.mem_coe, mem_growBlock_refs] at ha hb
          have : (a % 4) = (b % 4) := by
            have := congrArg (fun (v : Fin 4) => (v : ℕ)) hab
            simpa using this
          omega
      have hf : Faults.f (Fin 4) = 1 := rfl
      omega
  no_equivocation := by
    intro i _ j _ _ hc hr
    have hv : (i % 4) = (j % 4) := by
      have := congrArg (fun (v : Fin 4) => (v : ℕ)) hc
      simpa using this
    simp only [growBlock_round] at hr
    omega

@[simp] theorem ugrow_ids (N : ℕ) : (Ugrow N).ids = Finset.range (4 * (N + 1)) := rfl

@[simp] theorem ugrow_block (N : ℕ) : (Ugrow N).block = growBlock := rfl

/-! ## `Ugrow N` satisfies `Live` at horizon `N`

Both fields come down to naming the right id: validator `v`'s round-`r` block
is `4 * r + v`. -/

theorem ugrow_populated {N r : ℕ} (hr : r ≤ N) : Populated (Ugrow N) r := by
  intro v _
  have hv := v.isLt
  refine ⟨4 * r + (v : ℕ), ?_, ?_, ?_⟩
  · simp only [ugrow_ids, Finset.mem_range]
    omega
  · apply Fin.ext
    simp only [ugrow_block, growBlock_creator_val]
    omega
  · simp only [ugrow_block, growBlock_round]
    omega

/-- **The witness.** `Live` is satisfiable at *every* horizon — which is the
form the claim has to take, since no single `Finset` universe can be tall
enough for all of them. -/
theorem ugrow_live (N : ℕ) : Live (Ugrow N) N where
  genesis := ugrow_populated (Nat.zero_le N)
  builds _ hr _ := ugrow_populated hr

/-- And it is synchronised from round 0: a `Ugrow` block references the
*whole* round below, so honest-to-honest coverage is immediate. This is what
rules out `Live` and `Synchronised` being jointly unsatisfiable, which would
leave L4–L6 vacuous however satisfiable each was alone. -/
theorem ugrow_synchronised (N : ℕ) : Synchronised (Ugrow N) 0 := by
  intro n _ b _ hbr _ a _ har _
  simp only [ugrow_block, growBlock_round] at hbr har
  simp only [ugrow_block, mem_growBlock_refs]
  omega

/-! ## The family is genuinely unbounded

Each `Ugrow N` is finite, but the heights are cofinal — which is what "the
DAG grows without bound" means once `U.ids` is a `Finset` (§4.4). -/

theorem ugrow_card (N : ℕ) : (Ugrow N).ids.card = 4 * (N + 1) := by
  simp

example : ∀ N, ∃ M, N < (Ugrow M).ids.card := fun N => ⟨N, by
  rw [ugrow_card]; omega⟩

-- Concretely: `Ugrow 5` is a six-round DAG, and validator 3 is at its top.
example : (Ugrow 5).ids.card = 24 := by decide
example : (growBlock 23).round = 5 := by decide
example : ((growBlock 23).creator : ℕ) = 3 := by decide

/-! ## L1 against the witness

The point of the family is that L1 now says something. These also pin the
horizon down as **tight**: L1 reaches round `N` and stops, and it stops
because there is genuinely nothing above. -/

/-- **L1 applied.** Every correct validator has a block at the top round. -/
example (N : ℕ) : Populated (Ugrow N) N := no_stall (ugrow_live N) N (le_refl N)

/-- And at every round below it. -/
example (N r : ℕ) (h : r ≤ N) : Populated (Ugrow N) r := no_stall (ugrow_live N) r h

/-- The quorum corollary, which L4 will consume. -/
example (N r : ℕ) (h : r ≤ N) : 2 * Faults.f (Fin 4) + 1 ≤ (authorsAt (Ugrow N) r).card :=
  card_authorsAt_of_live (ugrow_live N) h

/-- **The horizon is tight, not slack.** One round further and the conclusion
is false — so L1's bound `r ≤ N` is doing real work rather than being a
conservative guess. -/
theorem ugrow_not_populated_succ (N : ℕ) : ¬ Populated (Ugrow N) (N + 1) := by
  intro h
  obtain ⟨b, hb, _, hbr⟩ := h 1 (by decide)
  simp only [ugrow_ids, Finset.mem_range] at hb
  simp only [ugrow_block, growBlock_round] at hbr
  omega

/-- L0 also applies, and agrees: `Ugrow N` is dense below its frontier. -/
example (N : ℕ) (hN : 0 < N) : 2 * Faults.f (Fin 4) + 1 ≤ (authorsAt (Ugrow N) 0).card :=
  card_authorsAt_of_lt (U := Ugrow N) (r := N) (n := 0) hN
    (i := 4 * N)
    (by simp only [ugrow_ids, Finset.mem_range]; omega)
    (by simp only [ugrow_block, growBlock_round]; omega)

#print axioms ugrow_live
#print axioms ugrow_synchronised
#print axioms no_stall
#print axioms ugrow_not_populated_succ

end LeanDagTest
