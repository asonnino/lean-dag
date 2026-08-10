import LeanDag.Integration.Coverage
import LeanDag.Integration.ScheduleShape
import LeanDag.Hybrid.Decision

/-!
# I16 — the composition capstone

The document's thesis is that named invariants plus preservation
lemmas make composition free. The cells proved so far are the
*ingredients*; this file is the claim itself, and it is what tells us
whether the linear strategy actually paid.

The stack under test is a validator running four mechanisms at once: it
recovered from a crash by Safe Skip (§12), later garbage-collected
below a horizon (§9), reads the result under the hybrid fault model
(§14), and runs an adaptive schedule (§13). Nothing below proves
anything new about any of them — every proof is a chain of existing
lemmas, which is the point.

**The order matters, and asymmetrically.** Fill-then-truncate is
unconditional: `chop (skipFill U) G` is well formed for every horizon,
because the fill has already happened when the cut is made. The reverse
needs the anchor retained — a `SkipMsg` for `chop U G` requires
`B1 ∈ (chop U G).ids`, hence `G ≤ round B1` — which is I7's condition,
appearing here as an asymmetry rather than an obstacle. The order
proved here is the deployment order: a validator fills the gap when it
recovers, and prunes later.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

section Stack

variable [H : HybridFaults Validator]
variable {U : BlockUniverse Validator BlockId Payload}
variable {G : ℕ}

/-- **The stacked universe**: filled, then truncated. -/
abbrev stack (sk : SkipMsg U) (G : ℕ) : BlockUniverse Validator BlockId Payload :=
  chop sk.skipFill G

/-- **I16a.** Honest non-equivocation survives the whole stack — I3 then
I2, with no new argument. This is what lets the hybrid safety
development be used by a validator that both recovered and pruned. -/
theorem honestNoEquiv_stack (sk : SkipMsg U) (hne : HonestNoEquiv U) :
    HonestNoEquiv (stack sk G) :=
  honestNoEquiv_chop (honestNoEquiv_skipFill sk hne)

/-- **I16b.** Coverage survives the stack above the fill and the cut —
I5-positive then I4. The two offsets compose exactly as their
statements suggest: the fill demands strictly above `sk.r`, the
truncation shifts by `G`. -/
theorem synchronisedOn_stack (sk : SkipMsg U) {T : Finset Validator} {R R' R'' : ℕ}
    (hs : SynchronisedOn U T R) (hR : R ≤ R') (hfill : sk.r < R')
    (hcut : R' ≤ G + R'') :
    SynchronisedOn (stack sk G) T R'' :=
  synchronisedOn_chop (synchronisedOn_skipFill_above sk hs hR hfill) hcut

/-- **I16c.** Production survives the stack — SS2 then the truncation's
own rebasing. The reliable set gains the recovered validator at the
fill; the horizon renumbers the round. A gap round `G + m` of the
original is round `m` of the stack. -/
theorem populated_stack (sk : SkipMsg U) {T : Finset Validator} {m : ℕ}
    (hpop : PopulatedOn U T (G + m)) (hk1 : sk.r0 < G + m) (hk2 : G + m ≤ sk.r) :
    PopulatedOn (stack sk G) (insert sk.v1 T) m := by
  intro v hv
  obtain ⟨b, hb, hbc, hbr⟩ := sk.skipFill_populatedOn hpop hk1 hk2 v hv
  refine ⟨b, mem_chop_ids.mpr ⟨hb, by omega⟩, ?_, ?_⟩
  · rw [chop_block_eq, chopBlock_creator]; exact hbc
  · rw [chop_block_eq, chopBlock_round]; omega

/-- **I16d — the payoff.** Hybrid agreement holds in the stacked
universe: a validator that recovered from a crash by Safe Skip and then
pruned below a horizon still cannot disagree with anyone about a slot's
verdict, at any admissible threshold.

Every hypothesis is one of §14's own, discharged for the stack by
`honestNoEquiv_stack`; the theorem body is `Hybrid.decided_unique`
applied to a different universe. Nothing about the fill or the cut is
re-proved, which is the thesis of this document in one statement. -/
theorem hybrid_agree_stack [LinearOrder BlockId] [S : Slots Validator]
    (sk : SkipMsg U) (hne : HonestNoEquiv U) {k : ℕ}
    (hk : Hybrid.Admissible Validator k)
    {V₁ V₂ : View Validator BlockId Payload (stack sk G)} {s : ℕ}
    {v₁ v₂ : Option BlockId}
    (h₁ : Hybrid.Decided k (stack sk G) V₁ s v₁)
    (h₂ : Hybrid.Decided k (stack sk G) V₂ s v₂) : v₁ = v₂ :=
  Hybrid.decided_agree (honestNoEquiv_stack sk hne) hk h₁ h₂

end Stack

/-! ## The schedule layer stacks for free

The schedule invariants do not interact with the universe transformers
at all — `Slots.chop` and `slotsOf` are functions of a `Slots` instance
and nothing else — so the layer-S results of I13/I15 apply to a
validator running any stack of universe transformers whatsoever, with
no compatibility lemma needed. This is not a triviality worth hiding:
it is the reason §2's layering was the right decomposition, and it is
why the composition matrix is far smaller than the arc count suggests.

The statement below is the schedule half of the stack, and its proof is
the layer-S lemma unchanged. -/

section Schedule

variable [F : Faults Validator] [S : Slots Validator] {G d c : ℕ}
variable {T : Finset Validator}

/-- **I16e.** A validator running the stack still has a fair, spanning
schedule inside its truncation, for any universe transformers applied
beneath — the schedule layer is independent of them. -/
theorem schedule_stack (hd : G ≤ S.slotRound d)
    (hfair : FairRunOn (S := S) T c)
    (hspan : SpansEligible (Validator := Validator) (S := S) c) :
    FairRunOn (S := S.chop G d hd) T c ∧
      SpansEligible (Validator := Validator) (S := S.chop G d hd) c :=
  ⟨fairRunOn_chop S hd hfair, spansEligible_chop S hd hspan⟩

end Schedule

end Integration

end LeanDag
