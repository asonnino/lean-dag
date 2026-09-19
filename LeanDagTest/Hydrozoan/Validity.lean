import LeanDag.Hydrozoan.Validity.Proof
import LeanDagTest.Hydrozoan.EventualDecision
/-!
# Witness: validity, applied

On `U10` (`EventualDecision.lean`: the low-fault `Fin 4` configuration,
replica 1 crashed, leader `k % 4`, the three correct replicas filling
rounds 0–7 and referencing each other). The block is `3`, replica 0's
round-1 block; the committing slot is `2`, led by replica 2 with
candidate `7`.

* **`DeliversBlock` end-to-end, fully concrete**: every hypothesis
  discharged — synchrony from round 0 and from round 1, the exact
  boundary of `R ≤ round x`; population over rounds 2–4 — on the verdict
  assignment `g10`, under `lin10`, the listing of causal histories in
  identifier order, which is not a toy: block `3` is delivered, and the
  delivered sequence is pinned by `decide`. (`lin10` filters the
  identifiers rather than sorting the history, as `historyListing` does,
  so that `decide` can evaluate it; the two list the same blocks, which
  is checked.)
* **`RunDelivers` under a block's own id**: the same run, the other key
  the statement names.
* **Any view**: the same application on `V10p`, a strictly partial view
  holding rounds 0–4 — the statement asks no coverage of the view.
* **A slot several rounds above, and a horizon past `k + 1`**: replica
  2's genesis `1` is delivered through slot 3, three rounds up — the
  inductive step of the reach lemma, over population of the rounds in
  between — and block `3` through slot 2 at horizon 4. A strengthening
  of `round x < slotRound k` to adjacency, or of `k < n` to `n = k + 1`,
  fails here.
* **The listing hypotheses are load-bearing**: under a listing of the
  leader alone, the same assignment delivers the leaders and not `3`
  (`ListsHistory`); and on `U10j`, where a junk identifier outside the
  universe shares block `3`'s key, a listing of histories that also
  lists the junk delivers the key through it and not block `3`
  (`ListsWithin`) — the one way `RunDelivers` and `DeliversBlock` come
  apart for a correct author.
* **The slot must lie above the block**: block `6` meets every other
  hypothesis at slot 2 and sits at the slot's round; slot 2's candidate
  does not reach it and it is not delivered.
* **`validityProgress` end-to-end**: every hypothesis discharged on the
  pipelined schedule, over `ℕ` identifiers and any caught-up view. Its
  bound is opaque (existential) and at least 10 on this schedule, so a
  finite identifier type too small to fill the rounds below it would
  make the clause vacuous; the concrete guards are the applications
  above.

Disclosed: on `fourReplicas` every quorum is `3` and `T = Correct`, so a
strengthening exchanging `T` for `Correct` survives this file;
`ValidityHardening.lean` kills it on the eight-replica configuration,
with a correct author outside `T` whose block is not delivered. Both
universes populate every round, so a strengthening of the population
range's lower end (`round x < r` to `round x ≤ r`) survives.
-/

namespace LeanDagTest

namespace Hydrozoan

open LeanDag LeanDag.Hydrozoan Hydrozoan.PrefixAgreement Hydrozoan.Delivery Hydrozoan.Validity

/-- Slots 0 and 2 commit their candidates `0` and `7`; slot 1, led by the
crashed replica, is skipped. -/
def g10 : ℕ → Option (Fin 24)
  | 0 => some 0
  | 2 => some 7
  | _ => none

/-- `g10` decides below 3 in the full view. -/
theorem vfull10_g10 : DecidesBelow U10 (View.full U10) g10 3 := by
  intro k hk
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · exact Decided.directCommit (by decide) (Or.inr (by decide))
  · exact Decided.directSkip (by decide)
  · exact Decided.directCommit (by decide) (Or.inr (by decide))

/-- The causal history of `L`, in identifier order. -/
def lin10 (L : Fin 24) : List (Fin 24) :=
  (List.finRange 24).filter (fun x => x ∈ history U10 L)

theorem lin10_listsHistory : ListsHistory U10 lin10 := fun _ hL x h =>
  List.mem_filter.mpr ⟨List.mem_finRange x, decide_eq_true ((mem_history_iff hL).mpr h)⟩

theorem lin10_listsWithin : ListsWithin U10 lin10 := fun _ hL _ hx =>
  history_subset_ids hL (of_decide_eq_true (List.mem_filter.mp hx).2)

-- The block: replica 0's round-1 block. The slot: led by replica 2, at
-- round 2.
example : (U10.block 3).creator = 0 ∧ (U10.block 3).round = 1 ∧ IsLeaderBlock U10 2 7 := by
  decide

-- The correct replicas fill rounds 2–4: above the block, up to slot 2's
-- decision round.
theorem u10_populated_above : ∀ r, (U10.block 3).round < r →
    r ≤ Slots.slotRound (Validator := Fin 4) 2 + 2 →
    PopulatedOn U10 (Correct : Finset (Fin 4)) r := by
  intro r h1 h2
  change 1 < r at h1
  change r ≤ 1 * (2 / 1) + 2 at h2
  have : r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with rfl | rfl | rfl <;> decide

-- End-to-end: DeliversBlock applied with every hypothesis discharged
-- concretely, under the listing of causal histories.
example : (3 : Fin 24) ∈ delivered (authorRound U10.block) lin10 g10 3 :=
  (Validity.holds (Fin 4) (Fin 24) U10).2 (Correct : Finset (Fin 4)) 0 2 3
    (by decide) (by decide) u10_synchronised (by decide) (by decide) (by decide)
    (by decide) (by decide) u10_populated_above
    lin10 lin10_listsHistory lin10_listsWithin
    (View.full U10) g10 3 (by omega) vfull10_g10

-- The same at R = 1 = the block's round — the exact boundary of
-- `R ≤ round x`, killing a strengthening to strict inequality.
example : (3 : Fin 24) ∈ delivered (authorRound U10.block) lin10 g10 3 :=
  (Validity.holds (Fin 4) (Fin 24) U10).2 (Correct : Finset (Fin 4)) 1 2 3
    (by decide) (by decide) (fun n _ => u10_synchronised n (Nat.zero_le n))
    (by decide) (by decide) (by decide) (by decide) (by decide) u10_populated_above
    lin10 lin10_listsHistory lin10_listsWithin
    (View.full U10) g10 3 (by omega) vfull10_g10

-- What is delivered: slot 0's genesis leader, then slot 2's leader with
-- the history it flushes — block 3 among it.
example : delivered (authorRound U10.block) lin10 g10 3 =
    [0, 1, 2, 3, 4, 5, 7] := by decide

-- RunDelivers under a block's own id, the other key the statement names.
example : ∃ c ∈ delivered id lin10 g10 3, id c = (3 : Fin 24) :=
  (Validity.holds (Fin 4) (Fin 24) U10).1 (Correct : Finset (Fin 4)) 0 2 3
    (by decide) (by decide) u10_synchronised (by decide) (by decide) (by decide)
    (by decide) (by decide) u10_populated_above _ id
    lin10 lin10_listsHistory
    (View.full U10) g10 3 (by omega) vfull10_g10

-- The two listings hold the same blocks.
example : ∀ L x, x ∈ lin10 L ↔ x ∈ historyListing U10 L := by
  simp [lin10, historyListing]

/-- A strictly partial view: rounds 0–4. -/
def V10p : View U10 where
  ids := Finset.univ.filter (fun i : Fin 24 => (i : ℕ) < 15)
  subset_ids := by decide
  complete := by decide

example : V10p.ids ⊂ U10.ids := by decide

/-- `g10` decides below 3 in the partial view too. -/
theorem v10p_g10 : DecidesBelow U10 V10p g10 3 := by
  intro k hk
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · exact Decided.directCommit (by decide) (Or.inr (by decide))
  · exact Decided.directSkip (by decide)
  · exact Decided.directCommit (by decide) (Or.inr (by decide))

-- Any view: the same application on the partial view.
example : (3 : Fin 24) ∈ delivered (authorRound U10.block) lin10 g10 3 :=
  (Validity.holds (Fin 4) (Fin 24) U10).2 (Correct : Finset (Fin 4)) 0 2 3
    (by decide) (by decide) u10_synchronised (by decide) (by decide) (by decide)
    (by decide) (by decide) u10_populated_above
    lin10 lin10_listsHistory lin10_listsWithin
    V10p g10 3 (by omega) v10p_g10

/-- `g10` extended through slot 3, which commits its candidate `11`. -/
def g10' : ℕ → Option (Fin 24)
  | 0 => some 0
  | 2 => some 7
  | 3 => some 11
  | _ => none

/-- `g10'` decides below 4 in the full view. -/
theorem vfull10_g10' : DecidesBelow U10 (View.full U10) g10' 4 := by
  intro k hk
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hcase with rfl | rfl | rfl | rfl
  · exact Decided.directCommit (by decide) (Or.inr (by decide))
  · exact Decided.directSkip (by decide)
  · exact Decided.directCommit (by decide) (Or.inr (by decide))
  · exact Decided.directCommit (by decide) (Or.inr (by decide))

-- The correct replicas fill rounds 1–5: above replica 2's genesis, up to
-- slot 3's decision round.
theorem u10_populated_1_5 : ∀ r, (U10.block 1).round < r →
    r ≤ Slots.slotRound (Validator := Fin 4) 3 + 2 →
    PopulatedOn U10 (Correct : Finset (Fin 4)) r := by
  intro r h1 h2
  change 0 < r at h1
  change r ≤ 1 * (3 / 1) + 2 at h2
  have : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

-- A slot three rounds above the block: replica 2's genesis 1 through slot
-- 3 — the reach lemma's inductive step, over rounds 1 and 2.
example : (U10.block 1).round + 3 = Slots.slotRound (Validator := Fin 4) 3 := by decide
example : (1 : Fin 24) ∈ delivered (authorRound U10.block) lin10 g10' 4 :=
  (Validity.holds (Fin 4) (Fin 24) U10).2 (Correct : Finset (Fin 4)) 0 3 1
    (by decide) (by decide) u10_synchronised (by decide) (by decide) (by decide)
    (by decide) (by decide) u10_populated_1_5
    lin10 lin10_listsHistory lin10_listsWithin
    (View.full U10) g10' 4 (by omega) vfull10_g10'

-- A horizon past k + 1: block 3 through slot 2, at horizon 4.
example : (3 : Fin 24) ∈ delivered (authorRound U10.block) lin10 g10' 4 :=
  (Validity.holds (Fin 4) (Fin 24) U10).2 (Correct : Finset (Fin 4)) 0 2 3
    (by decide) (by decide) u10_synchronised (by decide) (by decide) (by decide)
    (by decide) (by decide) u10_populated_above
    lin10 lin10_listsHistory lin10_listsWithin
    (View.full U10) g10' 4 (by omega) vfull10_g10'

example : delivered (authorRound U10.block) lin10 g10' 4 =
    [0, 1, 2, 3, 4, 5, 7, 6, 8, 11] := by decide

-- The listing hypothesis is load-bearing: a listing of the leader alone
-- is not one of causal histories, and delivers the leaders and not 3.
example : ¬ ListsHistory U10 (fun L => [L]) := fun h => by
  have := h 7 (by decide) 3 (Reaches.single (by decide))
  revert this; decide
example : delivered (authorRound U10.block) (fun L => [L]) g10 3 = [0, 7] := by decide

/-- `U10` with identifier 23 turned into junk outside the universe: it
denotes a second round-1 "block" of replica 0, sharing block 3's key. -/
def lk10j : Fin 24 → Block (Fin 4) (Fin 24) := fun i =>
  if (i : ℕ) = 23 then { round := 1, creator := 0, refs := ∅, payload := () } else lk10 i

def U10j : BlockUniverse (Fin 4) (Fin 24) where
  ids := Finset.univ.erase 23
  block := lk10j
  complete := by decide
  valid := by decide
  no_equivocation := by decide

theorem vfull10j_g10 : DecidesBelow U10j (View.full U10j) g10 3 := by
  intro k hk
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · exact Decided.directCommit (by decide) (Or.inr (by decide))
  · exact Decided.directSkip (by decide)
  · exact Decided.directCommit (by decide) (Or.inr (by decide))

/-- Causal histories, with the junk identifier listed first. -/
def lin10j (L : Fin 24) : List (Fin 24) :=
  23 :: (List.finRange 24).filter (fun x => x ∈ history U10j L)

theorem lin10j_listsHistory : ListsHistory U10j lin10j := fun _ hL x h =>
  List.mem_cons_of_mem _ (List.mem_filter.mpr
    ⟨List.mem_finRange x, decide_eq_true ((mem_history_iff hL).mpr h)⟩)

-- `ListsWithin` is load-bearing: the listing holds histories but also the
-- junk, and the filter then delivers block 3's key through the junk —
-- `RunDelivers` stands, `DeliversBlock`'s conclusion fails.
example : ¬ ListsWithin U10j lin10j := fun h => by
  have := h 0 (by decide) 23 (by decide)
  revert this; decide
example : ∃ c ∈ delivered (authorRound U10j.block) lin10j g10 3,
    authorRound U10j.block c = authorRound U10j.block 3 :=
  (Validity.holds (Fin 4) (Fin 24) U10j).1 (Correct : Finset (Fin 4)) 1 2 3
    (by decide) (by decide)
    (by intro n hn b hb hbr hbc a ha har hac
        have hmax : ∀ c : Fin 24, c ∈ U10j.ids → (U10j.block c).round ≤ 7 := by decide
        have hb2 := hmax b hb
        have hn2 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 := by omega
        clear hb2 hmax hn
        rcases hn2 with rfl | rfl | rfl | rfl | rfl | rfl <;> (revert b a; decide))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (by intro r h1 h2
        change 1 < r at h1
        change r ≤ 1 * (2 / 1) + 2 at h2
        have : r = 2 ∨ r = 3 ∨ r = 4 := by omega
        rcases this with rfl | rfl | rfl <;> decide)
    _ (authorRound U10j.block) lin10j lin10j_listsHistory
    (View.full U10j) g10 3 (by omega) vfull10j_g10
example : (3 : Fin 24) ∉ delivered (authorRound U10j.block) lin10j g10 3 ∧
    (23 : Fin 24) ∈ delivered (authorRound U10j.block) lin10j g10 3 := by decide

-- The slot must lie above the block: block 6 meets every other
-- hypothesis at slot 2 and sits at the slot's round; slot 2's candidate 7
-- does not reach it, and this horizon does not deliver it.
example : (U10.block 6).creator ∈ (Correct : Finset (Fin 4)) ∧
    (U10.block 6).round = Slots.slotRound (Validator := Fin 4) 2 ∧
    (6 : Fin 24) ∉ delivered (authorRound U10.block) lin10 g10 3 := by
  decide

-- End-to-end: the composed corollary, all hypotheses discharged, on any
-- caught-up view — past round 1 a slot whose horizon delivers every
-- correct block of rounds 0 to 1. Over `ℕ` identifiers: the bound is
-- opaque and at least 10 here, and a `Fin 24` could not fill the rounds
-- below it.
example : ∃ b, 1 < Slots.slotRound (Validator := Fin 4) b ∧
    ∀ (U : BlockUniverse (Fin 4) ℕ),
      SynchronisedOn U (Correct : Finset (Fin 4)) 0 →
      (∀ r, 0 ≤ r → r ≤ Slots.slotRound (Validator := Fin 4) (b + 3 - 1) + 2 →
        PopulatedOn U (Correct : Finset (Fin 4)) r) →
      ∀ V : View U, V.CoversUpto (Slots.slotRound (Validator := Fin 4) (b + 3 - 1) + 2) →
      ∃ g, DecidesBelow U V g (b + 1) ∧
        ∀ x ∈ U.ids, (U.block x).creator ∈ (Correct : Finset (Fin 4)) →
          (U.block x).round ≤ 1 →
          x ∈ delivered (authorRound U.block) (historyListing U) g (b + 1) := by
  obtain ⟨b, hb, hrest⟩ :=
    Validity.validityProgress (Fin 4) ℕ (Correct : Finset (Fin 4)) 0 1 3
      (by decide) (by decide) (by omega) spansEligible_four fairRun_four
  refine ⟨b, hb, fun U hsync hpop V hcov => ?_⟩
  obtain ⟨⟨g, hg⟩, hdel⟩ := hrest U hsync hpop V hcov
  exact ⟨g, hg, fun x hx hxc hxr => hdel g hg x hx hxc (Nat.zero_le _) hxr
    (historyListing U) (listsHistory_historyListing U) (listsWithin_historyListing U)⟩

end Hydrozoan

end LeanDagTest
