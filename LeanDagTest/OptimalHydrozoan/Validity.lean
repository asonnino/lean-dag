import LeanDag.OptimalHydrozoan.Validity.Proof
import LeanDagTest.OptimalHydrozoan.EventualDecision
/-!
# Witness: Optimal validity, applied

On the steady-state universe `OS` (`EventualDecision.lean`: replica `0`
Byzantine and silent after genesis, `T = {1, 2, 3}` filling rounds 1–6
and referencing each other, leader `(k + 3) % 4`). The block is `5`,
replica 2's round-1 block; the committing slot is `2`, led by replica 1
with candidate `7`.

* **`DeliversBlock` end-to-end, fully concrete**: every hypothesis
  discharged — synchrony from round 0 and from round 1, the exact
  boundary of `R ≤ round x`; population over rounds 2–4 — on the verdict
  assignment `gS`, under `linS`, the listing of causal histories in
  identifier order: block `5` is delivered, and the delivered sequence
  is pinned by `decide`. The Byzantine genesis `0`, which no correct
  block references, is not delivered.
* **`RunDelivers` under a block's own id**, the other key.
* **A slot several rounds above**: block `5` through slot 4, three rounds
  up — the reach lemma's inductive step — with slot 4's decision round 6
  the table's last, so the population range is not wider than stated.
* **`creator ∈ T` is load-bearing**: the Byzantine genesis `0` meets every
  other hypothesis and is not delivered.
* **The slot must lie above the block**: block `8` meets every other
  hypothesis at slot 2, sits at the slot's round, and is not delivered.
* **`R ≤ round x` is load-bearing**: on `UO`, where no round-1 block
  references replica 1's genesis — synchronised from round 1 and not
  from 0 — that genesis meets every other hypothesis at `R = 1` and is
  not delivered.
* **`validityProgress` end-to-end**, over `ℕ` identifiers and any
  caught-up view; its bound is opaque.

Disclosed, as for this universe's other witnesses: every quorum is `3`
and `T = Correct`, so a strengthening exchanging them survives.
-/

namespace LeanDagTest

namespace OptimalHydrozoan

open LeanDagTest.Hydrozoan

open LeanDag LeanDag.Hydrozoan LeanDag.OptimalHydrozoan Hydrozoan.Delivery Hydrozoan.Validity
open LeanDag.OptimalHydrozoan.PrefixAgreement (DecidesBelow)

/-- Slots 0 and 2 commit their candidates `3` and `7`; slot 1, led by the
Byzantine replica, is skipped. -/
def gS : ℕ → Option (Fin 22)
  | 0 => some 3
  | 2 => some 7
  | _ => none

/-- `gS` decides below 3 in the full view. -/
theorem vs_gS : DecidesBelow OS VS gS 3 := by
  intro k hk
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · exact DecidedOpt.directCommit (by decide) (Or.inl (by decide))
  · exact DecidedOpt.directSkip (by decide)
  · exact DecidedOpt.directCommit (by decide) (Or.inl (by decide))

/-- The causal history of `L`, in identifier order. -/
def linS (L : Fin 22) : List (Fin 22) :=
  (List.finRange 22).filter (fun x => x ∈ history US L)

theorem linS_listsHistory : ListsHistory US linS := fun _ hL x h =>
  List.mem_filter.mpr ⟨List.mem_finRange x, decide_eq_true ((mem_history_iff hL).mpr h)⟩

theorem linS_listsWithin : ListsWithin US linS := fun _ hL _ hx =>
  history_subset_ids hL (of_decide_eq_true (List.mem_filter.mp hx).2)

-- The block: replica 2's round-1 block. The slot: led by replica 1, at
-- round 2.
example : (US.block 5).creator = 2 ∧ (US.block 5).round = 1 ∧ IsLeaderBlock US 2 7 := by
  decide

-- `T` fills rounds 2–4: above the block, up to slot 2's decision round.
theorem us_populated_above : ∀ r, (US.block 5).round < r →
    r ≤ Slots.slotRound (Validator := Fin 4) 2 + 2 →
    PopulatedOn US {1, 2, 3} r := by
  intro r h1 h2
  change 1 < r at h1
  change r ≤ 2 + 2 at h2
  have : r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with rfl | rfl | rfl <;> decide

-- End-to-end: DeliversBlock applied with every hypothesis discharged
-- concretely, under the listing of causal histories.
example : (5 : Fin 22) ∈ delivered (authorRound US.block) linS gS 3 :=
  (OptimalHydrozoan.Validity.holds (Fin 4) (Fin 22) OS).2 {1, 2, 3} 0 2 5
    (by decide) (by decide) us_synchronised (by decide) (by decide) (by decide)
    (by decide) (by decide) us_populated_above
    linS linS_listsHistory linS_listsWithin VS gS 3 (by omega) vs_gS

-- The same at R = 1 = the block's round — the exact boundary of
-- `R ≤ round x`.
example : (5 : Fin 22) ∈ delivered (authorRound US.block) linS gS 3 :=
  (OptimalHydrozoan.Validity.holds (Fin 4) (Fin 22) OS).2 {1, 2, 3} 1 2 5
    (by decide) (by decide) (fun n _ => us_synchronised n (Nat.zero_le n))
    (by decide) (by decide) (by decide) (by decide) (by decide) us_populated_above
    linS linS_listsHistory linS_listsWithin VS gS 3 (by omega) vs_gS

-- What is delivered: slot 0's genesis leader, then slot 2's leader with
-- the history it flushes — block 5 among it, the Byzantine genesis 0 not.
example : delivered (authorRound US.block) linS gS 3 = [3, 1, 2, 4, 5, 6, 7] := by decide

-- RunDelivers under a block's own id, the other key the statement names.
example : ∃ c ∈ delivered id linS gS 3, id c = (5 : Fin 22) :=
  (OptimalHydrozoan.Validity.holds (Fin 4) (Fin 22) OS).1 {1, 2, 3} 0 2 5
    (by decide) (by decide) us_synchronised (by decide) (by decide) (by decide)
    (by decide) (by decide) us_populated_above _ id
    linS linS_listsHistory VS gS 3 (by omega) vs_gS

/-- `gS` extended through slots 3 and 4, which commit `11` and `15`. -/
def gS5 : ℕ → Option (Fin 22)
  | 0 => some 3
  | 2 => some 7
  | 3 => some 11
  | 4 => some 15
  | _ => none

theorem vs_gS5 : DecidesBelow OS VS gS5 5 := by
  intro k hk
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 := by omega
  rcases hcase with rfl | rfl | rfl | rfl | rfl
  · exact DecidedOpt.directCommit (by decide) (Or.inl (by decide))
  · exact DecidedOpt.directSkip (by decide)
  · exact DecidedOpt.directCommit (by decide) (Or.inl (by decide))
  · exact DecidedOpt.directCommit (by decide) (Or.inl (by decide))
  · exact DecidedOpt.directCommit (by decide) (Or.inl (by decide))

theorem us_pop_2_6 : ∀ r, (US.block 5).round < r →
    r ≤ Slots.slotRound (Validator := Fin 4) 4 + 2 → PopulatedOn US {1, 2, 3} r := by
  intro r h1 h2
  change 1 < r at h1
  change r ≤ 4 + 2 at h2
  have : r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;> decide

-- A slot three rounds above the block, at a horizon the run reaches:
-- the reach lemma's inductive step, over rounds 2 and 3.
example : (5 : Fin 22) ∈ delivered (authorRound US.block) linS gS5 5 :=
  (OptimalHydrozoan.Validity.holds (Fin 4) (Fin 22) OS).2 {1, 2, 3} 0 4 5
    (by decide) (by decide) us_synchronised (by decide) (by decide) (by decide)
    (by decide) (by decide) us_pop_2_6
    linS linS_listsHistory linS_listsWithin VS gS5 5 (by omega) vs_gS5
-- Slot 4's decision round 6 is the table's last: `T` does not fill round
-- 7, and a strengthening of `slotRound k + 2` to `+ 3` fails here.
example : ¬ PopulatedOn US {1, 2, 3} 7 := by decide

-- `creator ∈ T` is load-bearing: the Byzantine genesis 0 meets every
-- other hypothesis at slot 2 and is not delivered.
example : (0 : Fin 22) ∈ US.ids ∧ (US.block 0).creator ∉ ({1,2,3} : Finset (Fin 4)) ∧
    0 ≤ (US.block 0).round ∧ (US.block 0).round < Slots.slotRound (Validator := Fin 4) 2 ∧
    PopulatedOn US {1,2,3} 1 ∧
    (0 : Fin 22) ∉ delivered (authorRound US.block) linS gS 3 := by decide

-- The slot must lie above the block: block 8 meets every other
-- hypothesis at slot 2 and sits at the slot's round; slot 2's candidate 7
-- does not reach it, and this horizon does not deliver it.
example : (US.block 8).creator ∈ ({1, 2, 3} : Finset (Fin 4)) ∧
    (US.block 8).round = Slots.slotRound (Validator := Fin 4) 2 ∧
    (8 : Fin 22) ∉ delivered (authorRound US.block) linS gS 3 := by
  decide

/-- `lkS` with every round-1 block referencing the genesis blocks `0`, `2`,
`3` and not replica 1's genesis `1`. -/
def lkO : Fin 22 → Block (Fin 4) (Fin 22) := fun i =>
  if h : 4 ≤ (i : ℕ) ∧ (i : ℕ) < 7 then
    { round := 1, creator := ⟨(i : ℕ) - 3, by omega⟩, refs := {0, 2, 3}, payload := () }
  else lkS i

def UO : BlockUniverse (Fin 4) (Fin 22) where
  ids := Finset.univ
  block := lkO
  complete := by decide
  valid := by decide
  no_equivocation := by decide

def OO : OptUniverse (Fin 4) (Fin 22) := OptUniverse.ofNoEquivocation UO (by decide)
def VO : LeanDag.Hydrozoan.View OO.toBlockRecord := View.full UO

-- Synchronised from round 1 and not from round 0.
theorem uo_synchronised : SynchronisedOn UO {1, 2, 3} 1 := by
  intro n hn b hb hbr hbc a ha har hac
  have hmax : ∀ c : Fin 22, (UO.block c).round ≤ 6 := by decide
  have hb2 := hmax b
  have hn2 : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  clear hb2 hmax hn
  rcases hn2 with rfl | rfl | rfl | rfl | rfl <;> (revert b a; decide)

theorem vo_gS : DecidesBelow OO VO gS 3 := by
  intro k hk
  have hcase : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  rcases hcase with rfl | rfl | rfl
  · exact DecidedOpt.directCommit (by decide) (Or.inl (by decide))
  · exact DecidedOpt.directSkip (by decide)
  · exact DecidedOpt.directCommit (by decide) (Or.inl (by decide))

/-- The causal history of `L`, in identifier order. -/
def linO (L : Fin 22) : List (Fin 22) :=
  (List.finRange 22).filter (fun x => x ∈ history UO L)

example : ¬ SynchronisedOn UO {1, 2, 3} 0 := fun h => by
  have := h 0 (Nat.le_refl 0) 4 (by decide) (by decide) (by decide) 1 (by decide) (by decide)
    (by decide)
  revert this; decide

-- `R ≤ round x` is load-bearing: replica 1's genesis meets every other
-- hypothesis at R = 1, slot 2, and is not delivered.
example : (UO.block 1).creator ∈ ({1,2,3} : Finset (Fin 4)) ∧ (UO.block 1).round = 0 ∧
    PopulatedOn UO {1,2,3} 1 ∧
    (1 : Fin 22) ∉ delivered (authorRound UO.block) linO gS 3 := by decide
example : delivered (authorRound UO.block) linO gS 3 = [3, 0, 2, 4, 5, 6, 7] := by decide

-- End-to-end: the composed corollary, all hypotheses discharged, on any
-- caught-up view. Over `ℕ` identifiers: the bound is opaque and large,
-- and a `Fin 22` could not fill the rounds below it. The listing is
-- abstract — the Optimal arc assumes no order on identifiers to sort by.
example : ∃ b, 1 < Slots.slotRound (Validator := Fin 4) b ∧
    ∀ (U : OptUniverse (Fin 4) ℕ),
      SynchronisedOn U.toBlockRecord {1, 2, 3} 0 →
      (∀ r, 0 ≤ r → r ≤ Slots.slotRound (Validator := Fin 4) (b + 3 - 1) + 2 →
        PopulatedOn U.toBlockRecord {1, 2, 3} r) →
      ∀ V : LeanDag.Hydrozoan.View U.toBlockRecord,
        V.CoversUpto (Slots.slotRound (Validator := Fin 4) (b + 3 - 1) + 2) →
      ∃ g, DecidesBelow U V g (b + 1) ∧
        ∀ x ∈ U.ids, (U.block x).creator ∈ ({1, 2, 3} : Finset (Fin 4)) →
          (U.block x).round ≤ 1 →
        ∀ lin, ListsHistory U.toBlockRecord lin → ListsWithin U.toBlockRecord lin →
          x ∈ delivered (authorRound U.block) lin g (b + 1) := by
  obtain ⟨b, hb, hrest⟩ :=
    OptimalHydrozoan.Validity.validityProgress (Fin 4) ℕ {1, 2, 3} 0 1 3
      (by decide) (by decide) (by omega) spansEligible_fourOpt fairRun_fourOpt
  refine ⟨b, hb, fun U hsync hpop V hcov => ?_⟩
  obtain ⟨⟨g, hg⟩, hdel⟩ := hrest U hsync hpop V hcov
  exact ⟨g, hg, fun x hx hxc hxr => hdel g hg x hx hxc (Nat.zero_le _) hxr⟩

end OptimalHydrozoan

end LeanDagTest
