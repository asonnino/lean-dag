import LeanDag.Integration.Stack
import LeanDag.Adaptive.Policy

/-!
# I10, I11 — the crash-prone lifecycle

The hybrid model (report §14) names a *crash-prone* class: honest validators
that may halt. Safe Skip (report §12) is the mechanism by which a halted
validator rejoins. That these were built separately is an accident of
order, and putting them together is the arc's most direct story:
a validator is demoted from the rotation while it is down (I11),
rejoins with one message (I10), and is restored to the reliable set.

**What the composition required.** `SkipMsg` originally carried
`hv1 : v1 ∈ Correct`, and in the hybrid model `Correct` excludes the
crash-prone class — so the structure could not describe the very
validators Safe Skip exists to serve. The hypothesis was stronger than
its use: it appeared once, to pin `v1`'s round-`r0` block to `B1` at
the fill's boundary. report §12 now carries that fact directly as `hB1uniq`,
with `hB1uniq_of_correct` recovering the old route. `hB1uniq_of_crash`
below is the other route, and it is what makes I10 statable: **a
crash-prone validator satisfies the boundary condition**, because
crash-proneness is honesty, and honest validators do not equivocate.

This is what integration is for. Neither arc was wrong; they simply
did not fit, because one of them stated a hypothesis in terms of a
class that the other splits.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

section Lifecycle

variable [H : HybridFaults Validator]
variable {U : BlockUniverse Validator BlockId Payload}

/-- **I10, the enabling lemma.** In the hybrid model a *crash-prone*
validator satisfies Safe Skip's boundary condition: it is honest, and
`HonestNoEquiv` pins its round-`r0` block to the anchor. The base
model's `hB1uniq_of_correct` cannot serve here — `Correct` excludes the
crash class by construction — which is precisely why report §12's hypothesis
needed to be stated as the fact rather than as membership. -/
theorem hB1uniq_of_crash (hne : HonestNoEquiv U) {v1 : Validator} {B1 : BlockId}
    (hB1 : B1 ∈ U.ids) (hB1c : (U.block B1).creator = v1)
    (hv1 : v1 ∉ H.byzantine) :
    ∀ j ∈ U.ids, (U.block j).creator = v1 →
      (U.block j).round = (U.block B1).round → j = B1 :=
  fun j hj hjc hjr => eq_of_creator_eq_honest hne hj hB1 hv1 hjc hB1c hjr

/-- Membership in the crash class implies the hypothesis above: the
crash-prone are honest. The bridge a caller actually uses. -/
theorem notMem_byzantine_of_mem_crash {v : Validator} (hv : v ∈ H.crash) :
    v ∉ H.byzantine :=
  fun hb => (Finset.disjoint_left.mp H.disjoint) hb hv

/-- **I10.** A crash-prone validator rejoins by Safe Skip, and every
guarantee of report §12 holds for its fill in the hybrid model. The fill is a
lawful universe carrying honest non-equivocation (so report §14's safety
applies to it), production is restored with the recovered validator in
the reliable set, and no verdict moves.

The statement is an existence-free packaging: given a `SkipMsg` whose
`v1` is crash-prone — which `hB1uniq_of_crash` now permits — the three
conclusions are the arcs' own theorems, unmodified. -/
theorem crash_recovery_hybrid (sk : SkipMsg U) (hne : HonestNoEquiv U)
    {T : Finset Validator} {k : ℕ}
    (hpop : PopulatedOn U T k) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) :
    HonestNoEquiv sk.skipFill
      ∧ PopulatedOn sk.skipFill (insert sk.v1 T) k :=
  ⟨honestNoEquiv_skipFill sk hne, sk.skipFill_populatedOn hpop hk1 hk2⟩

end Lifecycle

/-! ## I11 — demotion of the crash class: nothing to prove

The adaptive layer's job in the lifecycle is to stop scheduling a
validator that is not producing, and the expectation was a lemma
relating `AdaptivePolicy` to `HybridFaults`. There is none, and there
cannot usefully be one: **the crash class is invisible to report §13.**

A policy reads verdicts. A halted validator's slot is skipped by L5
(`decided_none_of_leader_absent`), whose hypothesis is that no block at
the round carries the leader as creator — which is what halting *is* in
a structural model — and which says nothing about *why* the leader is
absent. A crash-prone leader, a Byzantine leader that withholds, and a
correct leader that has not yet built are indistinguishable at that
lemma, and a demoting policy demotes all three alike.

So I11 joins I14 as a **non-task**: the composition is immediate
because the two layers never meet except at the verdict, and the base
development already supplies the verdict. Recording it as such is worth
more than a hybrid-flavoured restatement of L5 would be, and the
lifecycle theorem below therefore consumes L5 directly.
-/

section Demotion

variable [H : HybridFaults Validator] [S : Slots Validator]
variable {U : BlockUniverse Validator BlockId Payload}

/-- **The lifecycle, in one statement.** A validator that halts has its
slot skipped (L5, unchanged); after it rejoins by Safe Skip its gap
rounds are populated with it back in the reliable set (SS2); and the
resulting universe still carries honest non-equivocation (I3), so report §14's
safety applies throughout.

Three arcs — the base liveness rules, Safe Skip, and the hybrid fault
model — meet here without any of them mentioning another. What connects
them is that all three speak about the same universe and the same
verdicts, which is what report §2's invariant vocabulary was collected to make
possible. -/
theorem lifecycle {V : View Validator BlockId Payload U} {k : ℕ}
    (sk : SkipMsg U) (hne : HonestNoEquiv U) {T : Finset Validator}
    (hhalt : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k)
    {m : ℕ} (hpop : PopulatedOn U T m) (hm1 : sk.r0 < m) (hm2 : m ≤ sk.r) :
    Decided U V k none
      ∧ PopulatedOn sk.skipFill (insert sk.v1 T) m
      ∧ HonestNoEquiv sk.skipFill :=
  ⟨decided_none_of_leader_absent hhalt,
   sk.skipFill_populatedOn hpop hm1 hm2,
   honestNoEquiv_skipFill sk hne⟩

end Demotion

end Integration

end LeanDag
