import LeanDag.Integration.Stack

/-!
# The invariant bundle the transformations preserve

The preservation results are stated one condition at a time — production
under truncation, non-equivocation under each transformation, coverage under
each, and the schedule-shape conditions — because that is how they are
proved and how a reader checks them. Stated that way, though, the
composition capstone has to rehearse the list and its offsets again, and the
statement of what a validator running several mechanisms has is spread over
six names.

This file names the safety-side pair as one predicate, `SoundOn`:

* **non-equivocation** — no correct validator has two blocks at a round;
* **coverage from `R`** — the structural synchrony the commit rules consume.

and proves that the pair survives each transformation, with the offsets in
the statement rather than in the prose around it. Nothing new is proved: each
field is the corresponding preservation lemma, and `hybrid_agree_of_soundOn`
is `hybrid_agree_stack` reading its hypothesis off the bundle.

**Production is deliberately not in the bundle.** It behaves differently
under the two transformations: truncation rebases its horizon, while the
fill *enlarges* the reliable set on the gap rounds rather than preserving it
(`skipFill_populatedOn`). Folding that into a conjunction would hide the one
asymmetry in the arc worth stating.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

section Sound

variable [H : HybridFaults Validator]
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {G R R' R'' : ℕ}

/-- **What a universe must still supply after being transformed.** The two
conditions every safety result of the hybrid arc consumes: correct validators
do not equivocate, and the DAG is covered from round `R` on. -/
structure SoundOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (R : ℕ) : Prop where
  /-- No correct validator has two blocks at one round. -/
  honest : HonestNoEquiv U
  /-- Every `T`-authored block references every `T`-authored block of the
  round below, from `R` on. -/
  covered : SynchronisedOn U T R

/-- **Truncation preserves it, shifting the synchrony round by the cut.** -/
theorem soundOn_chop (h : SoundOn U T R) (hGR : R ≤ G + R') :
    SoundOn (chop U G) T R' :=
  ⟨honestNoEquiv_chop h.honest, synchronisedOn_chop h.covered hGR⟩

/-- **The fill preserves it, above the gap.** The synchrony round must clear
the filled round: inside the gap the fill supplies blocks that reference
nothing, which is exactly what `not_synchronisedOn_skipFill` refutes. -/
theorem soundOn_skipFill (sk : SkipMsg U) (h : SoundOn U T R)
    (hR : R ≤ R') (hfill : sk.r < R') :
    SoundOn sk.skipFill T R' :=
  ⟨honestNoEquiv_skipFill sk h.honest,
   synchronisedOn_skipFill_above sk h.covered hR hfill⟩

/-- **The stack preserves it**, the offsets composing exactly as the two
statements above suggest: the fill demands a synchrony round strictly past
its target, and the truncation shifts by the cut. -/
theorem soundOn_stack (sk : SkipMsg U) (h : SoundOn U T R)
    (hR : R ≤ R') (hfill : sk.r < R') (hcut : R' ≤ G + R'') :
    SoundOn (stack sk G) T R'' :=
  ⟨honestNoEquiv_stack sk h.honest, synchronisedOn_stack sk h.covered hR hfill hcut⟩

/-- **The capstone, from the bundle.** A validator that has recovered from a
crash and pruned its history still has a sound universe, and two views of it
cannot disagree about a verdict — at any admissible threshold, with no new
argument. -/
theorem hybrid_agree_of_soundOn [LinearOrder BlockId] [S : Slots Validator]
    (sk : SkipMsg U) (h : SoundOn U T R) {k : ℕ}
    (hk : Hybrid.Admissible Validator k)
    {V₁ V₂ : View Validator BlockId Payload (stack sk G)} {s : ℕ}
    {v₁ v₂ : Option BlockId}
    (h₁ : Hybrid.Decided k (stack sk G) V₁ s v₁)
    (h₂ : Hybrid.Decided k (stack sk G) V₂ s v₂) : v₁ = v₂ :=
  hybrid_agree_stack sk h.honest hk h₁ h₂

end Sound

end Integration

end LeanDag
