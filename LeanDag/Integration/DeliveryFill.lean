import LeanDag.Integration.Exposure
import LeanDag.DoS.Novelty

/-!
# I15 — the delivery layer, and the storage budgets under the fill

The arc's last open composition. Report §8.4's budgets range over a
`Delivery U`, not over `U`, so they cannot be *stated* for the fill
until the fill has a delivery structure of its own — the dependency
report §15.1 records for layer D. Garbage collection has `chopD`;
Safe Skip had nothing.

The construction is smaller than it looks, and the reason is worth
stating. A `Delivery` records what validators **held and accepted when
they built their blocks**, and nobody received the fill at the time:
the filled blocks are a retroactive reconstruction of what the
recovering validator would have produced. So the transformer changes
nothing at all — the same `held`, the same `accepted`, retargeted to
the extended universe.

That leaves one obligation with content. `Delivery.includes` demands
that a correct validator reference everything it accepted, and it now
quantifies over the *filled* blocks too. A filled block is obliged to
reference what `v1` accepted at the round below — so the transformer
needs `v1` to have accepted nothing while it was down, which is what
being down means, and which report §12's `hgap` already asserts for
production. Stating it for acceptance as well is the honest cost.

With the transformer in place the budgets transfer with no arithmetic:
every accepted block is old, and an old block's cone is unchanged
(`history_skipFill_old`), so views and novelty are literally the same
finite sets.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **I15a — the delivery transformer.** The fill's delivery structure
is the original's: the recovering validator's blocks were never
delivered to anyone, being reconstructed after the fact.

`hdown` is the hypothesis `Delivery.includes` forces — the recovering
validator accepted nothing while it was down. It is the acceptance-side
counterpart of `hgap`, which says the same of production. -/
def skipFillD (sk : SkipMsg U) (D : Delivery U)
    (hdown : ∀ m, sk.r0 ≤ m → m < sk.r → D.accepted sk.v1 m = ∅) :
    Delivery sk.skipFill where
  held := D.held
  held_spec := by
    intro v n i hi
    obtain ⟨h1, h2⟩ := D.held_spec v n i hi
    exact ⟨sk.ids_subset_skipFill h1, by rw [sk.skipFill_block_old h1]; exact h2⟩
  accepted := D.accepted
  accepted_sub := D.accepted_sub
  accepted_inj := by
    intro v n i hi j hj hij
    have hio := (D.held_spec v n i (D.accepted_sub v n hi)).1
    have hjo := (D.held_spec v n j (D.accepted_sub v n hj)).1
    rw [sk.skipFill_block_old hio, sk.skipFill_block_old hjo] at hij
    exact D.accepted_inj v n i hi j hj hij
  accepts_correct := by
    intro v hv n a ha hac
    have hao := (D.held_spec v n a ha).1
    rw [sk.skipFill_block_old hao] at hac
    exact D.accepts_correct v hv n a ha hac
  includes := by
    intro v hv n b hb hbc hbr
    rcases Finset.mem_union.mp hb with ho | hf
    · -- an old block references what it accepted, as before
      rw [sk.skipFill_block_old ho] at hbc hbr ⊢
      exact D.includes v hv n b ho hbc hbr
    · -- a filled block: the recovering validator accepted nothing
      obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
      have hR0 : sk.r0 = (U.block sk.B1).round := rfl
      rw [sk.skipFill_block_fresh] at hbc hbr
      simp only [SkipMsg.fillBlock] at hbc hbr
      subst hbc
      rw [hdown n (by omega) (by omega)]
      exact Finset.empty_subset _

variable (sk : SkipMsg U) (D : Delivery U)
variable {hdown : ∀ m, sk.r0 ≤ m → m < sk.r → D.accepted sk.v1 m = ∅}

/-- Accepted blocks are old, so their cones are unchanged and the
accumulated view is literally the same finite set. -/
theorem viewUpto_skipFillD (v : Validator) :
    ∀ n, viewUpto (skipFillD sk D hdown) v n = viewUpto D v n := by
  intro n
  induction n with
  | zero =>
      show (D.accepted v 0).biUnion (history sk.skipFill)
        = (D.accepted v 0).biUnion (history U)
      refine Finset.biUnion_congr rfl (fun b hb => ?_)
      exact history_skipFill_old sk (D.held_spec v 0 b (D.accepted_sub v 0 hb)).1
  | succ n ih =>
      show viewUpto (skipFillD sk D hdown) v n
          ∪ (D.accepted v (n + 1)).biUnion (history sk.skipFill)
        = viewUpto D v n ∪ (D.accepted v (n + 1)).biUnion (history U)
      rw [ih]
      refine congrArg _ (Finset.biUnion_congr rfl (fun b hb => ?_))
      exact history_skipFill_old sk
        (D.held_spec v (n + 1) b (D.accepted_sub v (n + 1) hb)).1

/-- **I15b — the budget transfers.** Novelty is measured over the cone
of an accepted block against the accumulated view, and both are
unchanged, so the author-blind budget holds of the fill's delivery at
the same constant. -/
theorem uniformBudget_skipFillD {T : ℕ} (hu : UniformBudget D T) :
    UniformBudget (skipFillD sk D hdown) T := by
  intro v hv n b hb
  have hbo : b ∈ U.ids :=
    (D.held_spec v (n + 1) b (D.accepted_sub v (n + 1) hb)).1
  have : novelty sk.skipFill (viewUpto (skipFillD sk D hdown) v n) b
      = novelty U (viewUpto D v n) b := by
    unfold novelty
    rw [viewUpto_skipFillD sk D v n, history_skipFill_old sk hbo]
  rw [this]
  exact hu v hv n b hb

/-- **I15c — the reference discipline does not transfer, and the
failure is the mechanism's own.** `RefsAccepted` is the converse of
`includes`: a correct validator references *only* what it accepted. A
filled block references the donor's blocks, which the recovering
validator did not accept — it was down. So the discipline fails at
every filled block.

This is not a defect of the transformer but a description of what Safe
Skip does. The fill asserts references on `v1`'s behalf for rounds it
slept through; `RefsAccepted` says a validator cites only what reached
it. The two cannot both hold of a retroactive reconstruction under the
delivery structure that records what actually arrived.

The alternative is to model recovery as *acceptance at recovery time* —
`v1` obtains the donor's blocks when it rejoins, and accepts exactly
what its filled blocks cite. Both `includes` and `RefsAccepted` then
hold by construction, `accepted_inj` following from the P2 clause
`skipFill` already proves for `fillBlock`. What that model does not
give away is the budget: the novelty of the newly accepted blocks is
then a property of the fill, to be checked as in report §15.7 rather
than inherited. Which model is right is a specification question about
what a `Delivery` is meant to record, and it is recorded here rather
than settled. -/
theorem not_refsAccepted_skipFillD (hne : sk.r0 < sk.r)
    (hv1 : sk.v1 ∈ (Correct : Finset Validator)) :
    ¬ RefsAccepted (skipFillD sk D hdown) := by
  intro hra
  have hR0 : sk.r0 = (U.block sk.B1).round := rfl
  have hmem : sk.fresh (sk.r0 + 1) ∈ sk.skipFill.ids :=
    Finset.mem_union_right _
      (sk.mem_freshIds.mpr ⟨sk.r0 + 1, by omega, by omega, rfl⟩)
  have hsub := hra sk.v1 hv1 sk.r0 (sk.fresh (sk.r0 + 1)) hmem
    (by rw [sk.skipFill_block_fresh]; rfl)
    (by rw [sk.skipFill_block_fresh]; rfl)
  -- the anchor is cited by the fill, and was accepted by nobody in the gap
  have hB1mem : sk.B1 ∈ (sk.skipFill.block (sk.fresh (sk.r0 + 1))).refs := by
    rw [sk.skipFill_block_fresh]
    simp only [SkipMsg.fillBlock, SkipMsg.prev]
    exact Finset.mem_insert_self _ _
  have hin : sk.B1 ∈ D.accepted sk.v1 sk.r0 := hsub hB1mem
  rw [hdown sk.r0 (le_refl _) hne] at hin
  exact absurd hin (Finset.notMem_empty _)

end Integration

end LeanDag
