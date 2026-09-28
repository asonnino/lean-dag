import LeanDagTest.Steelhead.BlueBottlePair
/-!
# Steelhead counterexample: dissemination at the synchronous kind of the `5f + 1` pair

SH-MM6d, and SH-BB6d at the asynchronous kind, say that a candidate one reliable block references
one round up commits once the reliable quorum is synchronised from that round and populates the
wave: the vote round lies above the referencing round, so synchrony carries the candidate into
every reliable vote. At the synchronous kind of BlueBottle's pair the rule is Odontoceti's, whose
vote round is the referencing round itself, and there the same hypotheses do not commit. This file
exhibits it on six validators with `f = 1`.

`dis6` has two rounds. Every round-`1` block references five blocks of round `0`: validators `0`
and `1` reference `{0, 1, 2, 3, 4}`, the others `{1, 2, 3, 4, 5}`. Slot `0` is validator `0`'s,
synchronous under `pairSlots`, and its only block is block `0`. The reliable set is the five
correct validators; one of them, validator `1`, references the candidate one round up. The
decision round is round `1`, the reliable set populates it, and it is synchronised from round `1`
since nothing lies above. The candidate has two supporters, validators `0` and `1`, short of the
quorum of five, and no slot above could anchor it, so the full view does not commit it.
-/

namespace LeanDagTest

set_option maxRecDepth 4096

open LeanDag LeanDag.Steelhead

/-- Block `6m + v` is validator `v`'s round-`m` block. -/
def dis6Blk : Fin 12 → Block (Fin 6) (Fin 12) Unit := fun i =>
  if h : (i : ℕ) < 6 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if (i : ℕ) < 8 then
    { round := 1, creator := ⟨(i : ℕ) - 6, by omega⟩, refs := {0, 1, 2, 3, 4}, payload := () }
  else
    { round := 1, creator := ⟨(i : ℕ) - 6, by have := i.isLt; omega⟩, refs := {1, 2, 3, 4, 5},
      payload := () }

/-- Two rounds, the candidate referenced one round up by validators `0` and `1` only. -/
def dis6 : BlockUniverse (Fin 6) (Fin 12) Unit where
  ids := Finset.univ
  block := dis6Blk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- The composite's direct commit on `dis6` is decidable, the field being each half's own test. -/
instance dis6CommitDecidable (V : View (Fin 6) (Fin 12) Unit dis6) (L : Fin 12) (r κ : ℕ) :
    Decidable ((blueBottlePairAnchored (Fin 6) (Fin 12) Unit).Commit dis6 V L r κ) :=
  (blueBottlePairAnchored (Fin 6) (Fin 12) Unit).decCommit dis6 V L r κ

/-- No block of `dis6` lies above round `1`. -/
theorem dis6_round_le : ∀ b : Fin 12, (dis6.block b).round ≤ 1 := by decide

/-- **SH-BB6d's hypotheses hold at slot `0`**, of the synchronous kind: the correct validators are
a quorum, block `0` is the leader's only block at round `0`, validator `1`'s round-`1` block `7`
references it, the quorum is synchronised from round `1` and populates the decision round `1`, and
the full view holds it. -/
theorem dis6_hypotheses :
    pairSlots.kind 0 = 0 ∧ quorumCard (Fin 6) ≤ full6Correct.card ∧
      IsLeaderBlock (S := pairSlots) dis6 0 0 ∧
      (∀ L' ∈ dis6.ids, (dis6.block L').round = pairSlots.slotRound 0 →
        (dis6.block L').creator = pairSlots.leader 0 → L' = 0) ∧
      (7 : Fin 12) ∈ dis6.ids ∧ (dis6.block 7).round = pairSlots.slotRound 0 + 1 ∧
      (dis6.block 7).creator ∈ full6Correct ∧ (0 : Fin 12) ∈ (dis6.block 7).refs ∧
      SynchronisedOn dis6 full6Correct (pairSlots.slotRound 0 + 1) ∧
      (blueBottlePairAnchored (Fin 6) (Fin 12) Unit).decisionRound (S := pairSlots) 0 = 1 ∧
      PopulatedOn dis6 full6Correct 1 ∧
      (View.full dis6).CoversUpto
        ((blueBottlePairAnchored (Fin 6) (Fin 12) Unit).decisionRound (S := pairSlots) 0) := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    fun n hn b _ hbr _ _ _ _ _ => ?_, by decide, by decide, View.coversUpto_full _ _⟩
  have := dis6_round_le b
  change 1 ≤ n at hn
  omega

/-- **And slot `0` is not committed**: two supporters one round up are short of the quorum, and no
block lies high enough to anchor the slot. -/
theorem dis6_slot0_not_committed :
    ¬ (blueBottlePairAnchored (Fin 6) (Fin 12) Unit).Decided (S := pairSlots) dis6
      (View.full dis6) 0 (some 0) := by
  intro h
  cases h with
  | directCommit _ hc => exact absurd hc (by decide)
  | @indirectCommit k j A L i _ helig hj _ _ _ _ _ _ =>
    have hA := AnchoredRule.isLeaderBlock_of_decided (S := pairSlots) hj
    have he := (blueBottlePairAnchored (Fin 6) (Fin 12) Unit).eligible_iff (S := pairSlots) |>.mp
      helig
    have hr := dis6_round_le A
    rw [hA.2.1] at hr
    change _ ≤ 1 at hr
    change 0 + 1 + 1 ≤ _ at he
    omega

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms dis6_hypotheses
#print axioms dis6_slot0_not_committed

end LeanDagTest
