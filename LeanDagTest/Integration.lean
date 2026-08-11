import LeanDag.Integration.Coverage
import LeanDag.Integration.ScheduleShape
import LeanDag.Integration.Joiner
import LeanDag.Integration.Stack
import LeanDag.Integration.Lifecycle
import LeanDag.Integration.Retention
import LeanDag.Integration.ReGenesis
import LeanDag.Integration.Exposure
import LeanDagTest.SafeSkip

/-!
# The integration lemmas, witnessed

The house rule applies with particular force to a *negative* result:
`not_synchronisedOn_skipFill` (I5) refutes coverage under the Safe Skip
fill, and a refutation whose hypotheses cannot be met refutes nothing.
This file discharges them on `Ucrash`, the crashed round-robin family
of `LeanDagTest/SafeSkip.lean`, so the failure is exhibited rather than
merely asserted.

The instantiation is the natural one, not a contrived one: the reliable
set is everybody once validator `3` is restored — exactly the set SS2
(`skipFill_populatedOn`) hands to the liveness account — the gap round
is the one the message fills, and the block above it is an ordinary
round-`2` block of a validator that never crashed.
-/

namespace LeanDagTest

open LeanDag LeanDag.Integration

/-- The fill of `Ucrash 2` targeting round `1`: validator `3` crashed
after its genesis block and rejoins with one message. -/
abbrev skTight : SkipMsg (Ucrash 2) := ucrashMsg 2 1 (by omega)

-- The fill's parameters, on data: the gap is the single round `1`.
example : skTight.v1 = 3 := rfl
example : skTight.r = 1 := rfl
example : skTight.r0 = 0 := by simp [SkipMsg.r0, ucrashMsg]

/-- Block `8` is validator `0`'s round-`2` block — old, reliable, and
sitting directly above the filled round. -/
example : ((Ucrash 2).block 8).round = 2 ∧ ((Ucrash 2).block 8).creator = 0 := by
  decide

/-- **I5 bites.** Coverage genuinely fails in the extension: with the
recovering validator counted reliable, no round-`2` block references
the block the fill supplies at round `1`, because no old block can
reference a fresh identifier. This is the same fact SS3 uses to prove
the fill cannot conjure a commit. -/
theorem ucrash_not_synchronisedOn :
    ¬ SynchronisedOn skTight.skipFill (Finset.univ : Finset (Fin 4)) 0 :=
  not_synchronisedOn_skipFill skTight (k := 1) (b := 8)
    (hv1 := Finset.mem_univ _) (hk1 := by simp [SkipMsg.r0, ucrashMsg])
    (hk2 := le_refl _) (hk := Nat.zero_le _)
    (hb := by decide) (hbround := by decide) (hbc := Finset.mem_univ _)

/-- And the positive form holds where it should: strictly above the
fill, every block is old and coverage transfers unchanged. Vacuously
true of `Ucrash 2` past round `1`, which is the honest reading — the
family stops there — but the *statement* is the one liveness consumes
after recovery. -/
example (hs : SynchronisedOn (Ucrash 2) (Finset.univ : Finset (Fin 4)) 0) :
    SynchronisedOn skTight.skipFill (Finset.univ : Finset (Fin 4)) 2 :=
  synchronisedOn_skipFill_above skTight hs (Nat.zero_le _) (by decide)

#print axioms LeanDag.Integration.addGenesis
#print axioms LeanDag.Integration.dosValid_addGenesis
#print axioms LeanDag.Integration.history_B1_subset_fill
#print axioms LeanDag.Integration.regenesis_converges
#print axioms LeanDag.Integration.populatedOn_addGenesis
#print axioms LeanDag.Integration.no_blocks_of_no_genesis
#print axioms LeanDag.Integration.severed_of_pruned_anchor
#print axioms LeanDag.Integration.anchor_pruned
#print axioms LeanDag.Integration.chopMsg
#print axioms LeanDag.Integration.outage_bounded_by_lag
#print axioms LeanDag.Integration.hB1uniq_of_crash
#print axioms LeanDag.Integration.crash_recovery_hybrid
#print axioms LeanDag.Integration.lifecycle
#print axioms LeanDag.Integration.honestNoEquiv_stack
#print axioms LeanDag.Integration.synchronisedOn_stack
#print axioms LeanDag.Integration.hybrid_agree_stack
#print axioms LeanDag.Integration.slotsChop_slotsOf
#print axioms LeanDag.Integration.joiner_assign_agree
#print axioms LeanDag.Integration.epochOf_add_of_dvd
#print axioms LeanDag.Integration.honestNoEquiv_chop
#print axioms LeanDag.Integration.honestNoEquiv_skipFill
#print axioms LeanDag.Integration.synchronisedOn_chop
#print axioms LeanDag.Integration.not_synchronisedOn_skipFill
#print axioms LeanDag.Integration.synchronisedOn_skipFill_above
#print axioms LeanDag.Integration.fairScheduleOn_chop
#print axioms LeanDag.Integration.spansEligible_chop
#print axioms ucrash_not_synchronisedOn

end LeanDagTest
