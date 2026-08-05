import LeanDag.Exposure
import LeanDag.Liveness
import LeanDag.CommonCore

/-!
# Liveness survives exclusion

`dos-equivocation-and-growth.md` §8, **D15b**, and §13 S8.

D15a says each caught equivocator costs one unit of the margin over the quorum,
and that at the fault bound a block must reference every correct block of the
round below. This file is the other half, and the one that settles the design:
**exclusion can never make the quorum threshold unreachable.**

The reason is the one `card_correct` was always for. Correct validators are
never exposed (D15), so they are admissible to every block, forever; and there
are at least `2f+1` of them. So the correct population's blocks are, on their
own, an admissible quorum for anybody — whatever has been excluded, and however
much of the fault budget has been spent.

**The threshold does not change; the pool it is drawn from does.**

Note the hypothesis. `card_correct` counts correct *validators*, not their
blocks, so something has to say they built: `Populated U n`. That places the
result — it is the induction step of L1 under the condition, not a standalone
claim that building always succeeds. Before `R` the adversary can withhold, and
the step does not fire; after `R`, `EventuallyDelivers` supplies it. Which is
why, under the condition, L1 holds from `R` rather than from round 0.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {b : BlockId} {n : ℕ}

/-- Decidable on concrete data: `PopulatedOn` is a bounded quantifier over two
`Finset`s, so a model can settle it by `decide`. Stated here rather than beside
the definition because it is the witnesses of §8 that need it. -/
instance decidablePopulatedOn (T : Finset Validator) (r : ℕ) :
    Decidable (PopulatedOn U T r) :=
  inferInstanceAs (Decidable (∀ v ∈ T, ∃ b ∈ U.ids,
    (U.block b).creator = v ∧ (U.block b).round = r))

omit [DecidableEq BlockId] in
/-- A populated round carries every correct validator among its correct blocks'
authors. -/
theorem correct_subset_creators_correctBlocksAt (h : Populated U n) :
    (Correct : Finset Validator) ⊆ creatorsOf U.block (correctBlocksAt U n) := by
  intro v hv
  obtain ⟨i, hi, hic, hir⟩ := h v hv
  exact mem_creatorsOf.mpr ⟨i, mem_correctBlocksAt.mpr ⟨hi, hir, by rw [hic]; exact hv⟩, hic⟩

omit [DecidableEq BlockId] in
/-- The correct blocks of a populated round carry a quorum of authors. -/
theorem card_creators_correctBlocksAt (h : Populated U n) :
    2 * F.f + 1 ≤ (creatorsOf U.block (correctBlocksAt U n)).card :=
  le_trans card_correct (Finset.card_le_card (correct_subset_creators_correctBlocksAt h))

/-- No correct block's author is ever excluded — D15, in the form a builder
needs. -/
theorem creator_notMem_exposedTo_of_mem_correctBlocksAt (hb : b ∈ U.ids) {i : BlockId}
    (hi : i ∈ correctBlocksAt U n) : (U.block i).creator ∉ exposedTo U b := by
  intro hmem
  exact (mem_exposedTo.mp hmem).not_correct hb (mem_correctBlocksAt.mp hi).2.2

/-- **D15b — the threshold is met by the correct set alone.**

Given a populated round `n`, its correct blocks are an admissible quorum for
*every* block `b`: they carry `2f+1` distinct authors, and not one of those
authors is exposed to `b`, whoever else is.

So a validator that has heard from the correct population can always build,
and exclusion never starves it. What the adversary can force is the pool down
to exactly `Correct` (D15a) — which is precisely the situation
`|Correct| ≥ 2f+1` was there to survive. -/
theorem correctBlocksAt_admissible_quorum (h : Populated U n) (hb : b ∈ U.ids) :
    2 * F.f + 1 ≤ (creatorsOf U.block (correctBlocksAt U n)).card ∧
      ∀ i ∈ correctBlocksAt U n, (U.block i).creator ∉ exposedTo U b :=
  ⟨card_creators_correctBlocksAt h, fun _ hi =>
    creator_notMem_exposedTo_of_mem_correctBlocksAt hb hi⟩

/-- The same, phrased as the DoS condition permits it: a block whose references
are correct round-`n` blocks satisfies the reference constraint outright,
because the constraint only ever forbids exposed authors. -/
theorem dosValid_refs_of_correctBlocksAt (hb : b ∈ U.ids)
    (hrefs : ∀ i ∈ (U.block b).refs, i ∈ correctBlocksAt U n) :
    ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator := by
  intro i hi hexp
  exact creator_notMem_exposedTo_of_mem_correctBlocksAt hb (hrefs i hi)
    (mem_exposedTo.mpr hexp)

/-! ## The acceptance policy, and where the quorum comes from after `R`

`Delivery` is deliberately free of the DoS vocabulary — it says what arrived
and what was built on, in either regime. The condition enters as a *policy* on
a given delivery: a correct validator declines to build on authors its own next
block would expose. -/

/-- The policy: nothing a correct validator accepts is exposed to the block it
goes on to build. -/
def DoSAccepting (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    ∀ i ∈ D.accepted v n, ¬ ExposedIn U b (U.block i).creator

/-- The tight half of `includes`: a correct validator references *exactly* what
it accepted, no more. `Delivery.includes` gives the other inclusion, and D3's
sharp bound wants both. -/
def ReferencesAccepted (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted v n

/-- **The condition is implementable.** A correct validator following the
policy produces blocks that satisfy the DoS reference constraint.

Only the correct half of `DoSValid` is derivable, and necessarily so: no
delivery assumption constrains what a Byzantine validator publishes. That the
condition is a *validity* rule is what covers the other half — a Byzantine
block breaking it is not in the universe at all. -/
theorem not_exposedIn_refs_of_policy (D : Delivery U) (hacc : DoSAccepting D)
    (href : ReferencesAccepted D) {b : BlockId} (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator)) :
    ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator := by
  intro i hi
  rcases Nat.eq_zero_or_pos (U.block b).round with hr | hr
  · -- a genesis block references nothing
    rw [(U.valid b hb).refs_empty_of_round_zero hr] at hi
    exact absurd hi (Finset.notMem_empty i)
  · obtain ⟨n, hn⟩ : ∃ n, (U.block b).round = n + 1 := ⟨(U.block b).round - 1, by omega⟩
    exact hacc _ hbc n b hb rfl hn i (href _ hbc n b hb rfl hn hi)

omit [DecidableEq BlockId] in
/-- **Where the quorum comes from after `R`** — and the settled answer to the
plan's Q1.

`Live.builds` needs a quorum of *accepted* creators. After `R` that is not an
extra assumption: `EventuallyDelivers` puts every correct block in every
correct validator's hands, `Delivery.accepts_correct` accepts them, and a
populated round supplies `2f+1` of them. `DeliversQuorum` is therefore a
**consequence** from `R` on, not a hypothesis.

Before `R` it is not, and that is exactly the cost the condition carries: L1
holds from `R` rather than from round 0. -/
theorem card_creators_accepted_of_eventuallyDelivers {R : ℕ} (D : Delivery U)
    (hd : EventuallyDelivers D R) (hn : R ≤ n) (hpop : Populated U n)
    {v : Validator} (hv : v ∈ (Correct : Finset Validator)) :
    2 * F.f + 1 ≤ (creatorsOf U.block (D.accepted v n)).card := by
  refine le_trans card_correct (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨a, ha, hac, har⟩ := hpop w hw
  have hheld : a ∈ D.held v n := hd n hn v hv a ha har (by rw [hac]; exact hw)
  exact mem_creatorsOf.mpr ⟨a, D.accepts_correct v hv n a hheld (by rw [hac]; exact hw), hac⟩

end LeanDag
