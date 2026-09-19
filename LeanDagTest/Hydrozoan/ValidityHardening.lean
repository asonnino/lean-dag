import LeanDag.Hydrozoan.Validity.Proof
import LeanDagTest.Hydrozoan.LivenessHardening
/-!
# Witness: validity, hardened

`Validity.lean` runs on `fourReplicas`, where every quorum is `3` and
`T = Correct`. This file separates them, on the eight-replica
configuration of `LivenessHardening`: `T6 = {1, …, 6}` is a proper subset
of `Correct` of exactly quorum size, and the correct replica 7 authors a
genesis that no block references.

* `DeliversBlock` end-to-end at `T6`: a strengthening of `T ⊆ Correct` to
  `T = Correct`, or of population or synchrony to all of `Correct`, fails
  here.
* Replica 7's block meets every hypothesis but `creator ∈ T` and is not
  delivered: validity is claimed of the synchronised quorum, not of
  every correct replica, and the statement says so.
* `T6` does not fill round 4: a strengthening of the population range's
  upper end from `slotRound k + 2` to `+ 3` fails here.
-/

namespace LeanDagTest

namespace Hydrozoan

open LeanDag LeanDag.Hydrozoan Hydrozoan.PrefixAgreement Hydrozoan.Delivery Hydrozoan.Validity

set_option maxRecDepth 4096

/-- `U12` of `LivenessHardening` with a round 3, and a genesis by the
correct replica 7, which nothing references: ids 0–5, 6–11, 12–17, 18–23
are rounds 0–3 by replicas 1–6, each round referencing all of the one
below; id 24 is replica 7's. -/
def lk12x : Fin 25 → Block (Fin 8) (Fin 25) := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨(i : ℕ) + 1, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) < 12 then
    { round := 1, creator := ⟨(i : ℕ) - 5, by omega⟩, refs := {0, 1, 2, 3, 4, 5}, payload := () }
  else if h : (i : ℕ) < 18 then
    { round := 2, creator := ⟨(i : ℕ) - 11, by omega⟩, refs := {6, 7, 8, 9, 10, 11},
      payload := () }
  else if h : (i : ℕ) < 24 then
    { round := 3, creator := ⟨(i : ℕ) - 17, by omega⟩, refs := {12, 13, 14, 15, 16, 17},
      payload := () }
  else
    { round := 0, creator := ⟨7, by omega⟩, refs := ∅, payload := () }

def U12x : BlockUniverse (Fin 8) (Fin 25) where
  ids := Finset.univ
  block := lk12x
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- A quorum of the correct replicas, and not all of them. -/
abbrev T6 : Finset (Fin 8) := {1, 2, 3, 4, 5, 6}

theorem u12x_synchronised : SynchronisedOn U12x T6 0 := by
  intro n hn b hb hbr hbc a ha har hac
  have hmax : ∀ c : Fin 25, (U12x.block c).round ≤ 3 := by decide
  have hb2 := hmax b
  have hn2 : n = 0 ∨ n = 1 ∨ n = 2 := by omega
  clear hb2 hmax hn
  rcases hn2 with rfl | rfl | rfl <;> (revert b a; decide)

/-- Slots 0 and 1 commit their candidates `0` and `7`. -/
def g12 : ℕ → Option (Fin 25)
  | 0 => some 0
  | 1 => some 7
  | _ => none

theorem g12_decides : DecidesBelow U12x (View.full U12x) g12 2 := by
  intro k hk
  have hcase : k = 0 ∨ k = 1 := by omega
  rcases hcase with rfl | rfl
  · exact Decided.directCommit (by decide) (Or.inr (by decide))
  · exact Decided.directCommit (by decide) (Or.inr (by decide))

/-- The causal history of `L`, in identifier order. -/
def lin12 (L : Fin 25) : List (Fin 25) :=
  (List.finRange 25).filter (fun x => x ∈ history U12x L)
theorem lin12_listsHistory : ListsHistory U12x lin12 := fun _ hL x h =>
  List.mem_filter.mpr ⟨List.mem_finRange x, decide_eq_true ((mem_history_iff hL).mpr h)⟩
theorem lin12_listsWithin : ListsWithin U12x lin12 := fun _ hL _ hx =>
  history_subset_ids hL (of_decide_eq_true (List.mem_filter.mp hx).2)

theorem u12x_pop : ∀ r, (U12x.block 3).round < r →
    r ≤ Slots.slotRound (Validator := Fin 8) 1 + 2 → PopulatedOn U12x T6 r := by
  intro r h1 h2
  change 0 < r at h1
  change r ≤ 1 * (1 / 1) + 2 at h2
  have : r = 1 ∨ r = 2 ∨ r = 3 := by omega
  rcases this with rfl | rfl | rfl <;> decide

-- End-to-end at a proper subset of `Correct`, of exactly quorum size.
example : (3 : Fin 25) ∈ delivered (authorRound U12x.block) lin12 g12 2 :=
  (Validity.holds (Fin 8) (Fin 25) U12x).2 T6 0 1 3
    (by decide) (by decide) u12x_synchronised (by decide) (by decide) (by decide)
    (by decide) (by decide) u12x_pop lin12 lin12_listsHistory lin12_listsWithin
    (View.full U12x) g12 2 (by omega) g12_decides

-- A correct replica outside `T`: its block meets every other hypothesis
-- and is not delivered — `creator ∈ T` is load-bearing, and validity is
-- `T`'s, not `Correct`'s.
example : (U12x.block 24).creator ∈ (Correct : Finset (Fin 8)) ∧ (U12x.block 24).creator ∉ T6 ∧
    (U12x.block 24).round = 0 ∧
    (24 : Fin 25) ∉ delivered (authorRound U12x.block) lin12 g12 2 := by decide
-- `T` does not fill round 4, one past slot 1's decision round, and
-- `Correct` does not fill round 1: the population range is not wider than
-- stated, and is not asked of `Correct`.
example : ¬ PopulatedOn U12x T6 4 ∧ ¬ PopulatedOn U12x (Correct : Finset (Fin 8)) 1 ∧
    T6.card = q (Fin 8) := by decide
example : delivered (authorRound U12x.block) lin12 g12 2 = [0, 1, 2, 3, 4, 5, 7] := by decide

end Hydrozoan

end LeanDagTest
