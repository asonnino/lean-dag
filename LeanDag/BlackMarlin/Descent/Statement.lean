import LeanDag.BlackMarlin.Model.Descent

/-!
# Black Marlin — the descent computed, stated

`Ledger/Statement.lean` takes the record `commit`'s descent leaves as
given and carries BMD3's stretch as a hypothesis. This phase computes the
descent instead, and the hypothesis goes away (`black-marlin.md` §11).
Five claims:

* **BME1, `DescendSound`** — the choice of L21–L24 is an anchor of the
  universe strictly below `B`, at the highest anchor round its cone
  reaches;
* **BME2, `DescendTotal`** — and it is made whenever an anchor lies
  below, so the descent stops only where there is nothing left to visit.
  L20's guard is `𝒜 ≠ ∅` where L21–L24 need `maxAnchor(𝒜) ≠ ∅`; this
  states the condition that is actually required;
* **BME3, `RecordIsFlush`** — the record generated from an anchor
  satisfies the three conditions of `Flush`, so BMD6's ledger results
  apply to it. `step` and `dense` are derived here rather than assumed;
* **BME4, `Suffix`** — the record below a block the descent visited *is*
  that block's own record. This is the reason the descent's agreement is
  a consequence: the choice at each round reads only the block above,
  which L24's metric — `|round(A) − round(maxAnchor(strong(A)))|`, a
  function of the candidate and its own cone — makes shared;
* **BME5, `AgreeBelow`** — so two records that reach the same block at a
  round agree at **every** round below it, with no hypothesis about the
  rounds in between. This closes BMD3.

**What is modelled, and what is chosen.** `𝒟` is dropped: the delivered
set only removes what an earlier descent visited, so the anchors a
validator flushes over all its commits are one chain read from its
highest commit down. And "break ties deterministically" is read as the
`≤`-least survivor under a `LinearOrder` on identifiers — hash order, in
a deployment — as the Odontoceti and Mahi-Mahi arcs read their canonical
choices. Nothing below depends on which rule it is, only that it is
shared and reads the candidate alone.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Descent

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **BME1, the choice is sound.** -/
def DescendSound (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B A : BlockId), B ∈ U.ids → descend U B = some A →
    A ∈ U.ids ∧ IsAnchorBlock U A ∧ A ∈ strongOf U B ∧
      (U.block A).round = maxAnchorRound U (strongOf U B) ∧
      (U.block A).round < (U.block B).round

/-- **BME2, and total where an anchor lies below.** -/
def DescendTotal (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B : BlockId), (anchorsOf U (strongOf U B)).Nonempty → (descend U B).isSome

/-- **BME3, the record is a flush record.** The three conditions
`Flush` asks for, here derived from the descent rather than assumed of
it. -/
def RecordIsFlush (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B : BlockId), B ∈ U.ids → IsAnchorBlock U B →
    (∀ (ρ : ℕ) (L : BlockId), flushRecord U B ρ = some L → IsAnchor U ρ L) ∧
    (∀ (ρ : ℕ) (L M : BlockId), flushRecord U B ρ = some L →
      flushRecord U B (ρ + 1) = some M → L ∈ (U.block M).refs) ∧
    (∀ (ρ : ℕ) (M : BlockId), flushRecord U B (ρ + 1) = some M →
      (coneAnchors U M ρ).Nonempty → (flushRecord U B ρ).isSome)

/-- **BME4, the record below a visited block is that block's own.** -/
def Suffix (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B M : BlockId) (σ ρ : ℕ), B ∈ U.ids →
    flushRecord U B σ = some M → ρ ≤ σ →
    flushRecord U B ρ = flushRecord U M ρ

/-- **BME5, agreement with no definedness hypothesis.** Two descents that
reach the same block at a round agree at every round below it, whatever
happens between — which is what BMD3 has to assume of an abstract
record. -/
def AgreeBelow (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (B₁ B₂ M : BlockId) (σ ρ : ℕ), B₁ ∈ U.ids → B₂ ∈ U.ids →
    flushRecord U B₁ σ = some M → flushRecord U B₂ σ = some M → ρ ≤ σ →
    flushRecord U B₁ ρ = flushRecord U B₂ ρ

/-- The descent of `commit`, over every fault configuration, rotation and
block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    DescendSound U ∧ DescendTotal U ∧ RecordIsFlush U ∧ Suffix U ∧ AgreeBelow U

end Descent

end BlackMarlin

end LeanDag
