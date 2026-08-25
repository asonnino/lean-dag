import LeanDag.BlackMarlin.Order.Statement

/-!
# Black Marlin — the delivered order at a validator's view, stated

BMV1 and BMV2 conclude `B ∈ history U L`: membership in what a validator
delivers, not position in the sequence it delivers. The position is
fixed by the descent, and `black-marlin.md` §15 left that open. This
settles it, in both directions. Three claims:

* **BMT1, `ReliableAnchorPins`** — two records that flush at a round
  whose anchor is *reliable* flush the same block, whatever views they
  came from. Not an agreement argument: there is only one such block in
  the universe, non-equivocation having ruled out a second;
* **BMT2, `AgreeOnReliableStretch`** — so agreement descends from a
  reliably anchored round through any stretch the record flushes at,
  with no hypothesis about how either validator got there;
* **BMT3, `OrderAgreesWhenAnchorsReliable`** — and where every anchor
  below a round is reliable, two records flushing at the same rounds
  deliver the **same list**.

## Which is exactly as far as it goes

BMT3's hypothesis cannot be weakened to allow one Byzantine anchor
below, and the failure is not confined to the equivocator's own blocks.
In the execution of `black-marlin.md` §13 the two records deliver `5`
before `7` and `7` before `5`. Both are authored by *reliable*
validators, neither has a twin, and the filter of L27 never touches
either. What orders them is which segment they fall in, and the segments
differ because the two descents took different twins a round below.

So Definition 1's **Total order** fails, and it fails on honest blocks.
That is independent of which twin the filter prefers, so no rule for
choosing among twins repairs it — only a rule that makes the two
descents agree, which is §14's repair, and §15 records that it has no
live implementation.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace ViewOrder

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **BMT1, a reliable anchor pins every record.** The block flushed at
such a round is that round's anchor, and its author is correct, so
`no_equivocation` leaves one candidate in the whole universe. No view
enters the argument. -/
def ReliableAnchorPins (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (ρ : ℕ) (L₁ L₂ : BlockId),
    Rot.anchor ρ ∈ (Correct : Finset Validator) →
    f₁.block ρ = some L₁ → f₂.block ρ = some L₂ → L₁ = L₂

/-- **BMT2, and agreement descends from it.** BMD3 needs a round the two
records agree at; a reliably anchored round both flush at is one, by
BMT1, with nothing assumed about either validator's view. -/
def AgreeOnReliableStretch (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (ρ d : ℕ),
    Rot.anchor (ρ + d) ∈ (Correct : Finset Validator) →
    (f₁.block (ρ + d)).isSome → (f₂.block (ρ + d)).isSome →
    (∀ i, 0 < i → i ≤ d → (f₁.block (ρ + i)).isSome) →
    f₁.block ρ = f₂.block ρ

/-- **BMT3, and the delivered lists coincide.** Where no Byzantine
validator anchors a round below `n`, two records that flush at the same
rounds deliver one list — Definition 1's Total order, unconditionally,
on that stretch.

The hypothesis is tight. `LeanDagTest/BlackMarlin/Divergence` exhibits
two records with a single Byzantine anchor below them that deliver two
reliably authored blocks in opposite orders. -/
def OrderAgreesWhenAnchorsReliable (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (τ : TopoSort U) (n : ℕ),
    (∀ σ, σ < n → Rot.anchor σ ∈ (Correct : Finset Validator)) →
    (∀ σ, σ < n → ((f₁.block σ).isSome ↔ (f₂.block σ).isSome)) →
    deliverSeq U f₁ τ n = deliverSeq U f₂ τ n

/-- The delivered order of the Black Marlin commit rule where the
rotation names reliable validators, over every fault configuration,
rotation and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    ReliableAnchorPins U ∧ AgreeOnReliableStretch U ∧ OrderAgreesWhenAnchorsReliable U

end ViewOrder

end BlackMarlin

end LeanDag
