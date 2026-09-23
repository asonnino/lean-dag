import LeanDag.Steelhead.Model.Pair
/-!
# The `5f + 1` pair — statement

The interface (SH16a, SH16b) instantiated at BlueBottle's two variants:
Odontoceti, the partially synchronous one, at wave two, and Async
BlueBottle at wave three, on one `n ≥ 5f + 1` committee. This is the
second of the paper's two pairs, and the one the discharge table of the
paper's Appendix B leaves open for clauses A2 and A3. Five claims:

* **SH-BB3, handover** — SH3's analogue: a direct commit in one view is
  committed by every view that finds the slot an anchor, whichever rule
  decided that anchor, and no view skips it. Unlike the `3f + 1` pair
  this passes through the tie-break rather than around it, the rung's
  link not being unique per slot at either wave;
* **SH-BB16a, the halves satisfy the clauses** — every rule of the family
  satisfies the anchored relation's laws at its own wave, of which
  `commit_link` is the paper's clause A2, a direct commit linked from
  every eligible anchor, and `skip_link` is clause A3, a direct skip
  leaving no anchor anything to link. Odontoceti supplies them at wave
  two and Async BlueBottle at wave three, each from its own arc,
  consumed read-only;
* **SH-BB16b, the pair's rule agrees** — SH16a and SH16b at this family:
  `blueBottlePairAnchored` satisfies the laws, and two views deciding one
  slot reach the same verdict whatever routes they took and whichever of
  the two rules decided the slot or its anchors. The paper's Theorem 1
  for the `5f + 1` pair, and SH2's analogue;
* **SH-BB16d, the pair is a family** — the two agree on the rung count, one,
  and on the tie-break, the least candidate. That is everything the
  interface asks of a pair beyond the laws, and it is what makes the two
  rules composable at all: the relation reads the rung count and the tie
  without reference to a slot, so a pair disagreeing on either is outside
  Theorem 1 however lawful each half is;
* **SH-BB16e, the pair reads two waves** — the wave offsets are one and two,
  so an anchor sits at `r + 2` above a synchronous slot and at `r + 3`
  above an asynchronous one, and the two differ. The family is therefore
  not a constant wave in disguise, and unlike `mahiMahiPair` its two
  members are two predicate families and not one read at two numbers.

Odontoceti and Async BlueBottle are consumed read-only; nothing of either
arc is restated here. Theorem 2 at the pair is `Liveness/Statement.lean`
beside this file.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [S : Slots Validator]

/-- **SH-BB3, handover.** -/
def PairHandover (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (L : BlockId),
    -- L is slot k's candidate, directly committed in V₁ under the rule of k's own kind
    IsLeaderBlock U k L →
    (blueBottlePairAnchored Validator BlockId Payload).Commit U V₁ L (S.slotRound k) (S.kind k) →
    -- then any anchor V₂ finds for k commits L ...
    (∀ (j : ℕ) (A : BlockId),
      k < j → (blueBottlePairAnchored Validator BlockId Payload).Eligible (S := S) k j →
      (blueBottlePairAnchored Validator BlockId Payload).Decided (S := S) U V₂ j (some A) →
      (∀ m, k < m → m < j →
        (blueBottlePairAnchored Validator BlockId Payload).Eligible (S := S) k m →
        (blueBottlePairAnchored Validator BlockId Payload).Decided (S := S) U V₂ m none) →
      (blueBottlePairAnchored Validator BlockId Payload).Decided (S := S) U V₂ k (some L)) ∧
    -- ... and V₂ never skips k
    ¬ (blueBottlePairAnchored Validator BlockId Payload).Decided (S := S) U V₂ k none

/-- **SH-BB16a, the halves satisfy the clauses.** -/
def HalvesLawful (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] : Prop :=
  ∀ κ, (blueBottlePair Validator BlockId Payload κ).Laws

/-- **SH-BB16b, the pair's rule agrees.** -/
def PairAgreement (U : BlockUniverse Validator BlockId Payload) : Prop :=
  (blueBottlePairAnchored Validator BlockId Payload).Laws ∧
    ∀ (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (v₁ v₂ : Option BlockId),
      (blueBottlePairAnchored Validator BlockId Payload).Decided (S := S) U V₁ k v₁ →
      (blueBottlePairAnchored Validator BlockId Payload).Decided (S := S) U V₂ k v₂ →
      v₁ = v₂

/-- **SH-BB16d, the pair is a family.** -/
def PairAgreesOnRungsAndTie (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults5 Validator] [LinearOrder BlockId] : Prop :=
  (∀ κ, (blueBottlePair Validator BlockId Payload κ).rungs =
      (blueBottlePair Validator BlockId Payload 0).rungs) ∧
    (∀ κ, (blueBottlePair Validator BlockId Payload κ).tie =
      (blueBottlePair Validator BlockId Payload 0).tie)

/-- **SH-BB16e, the pair reads two waves.** -/
def PairWavesDiffer (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] : Prop :=
  -- the synchronous kind reads Odontoceti's wave two and every other kind Async BlueBottle's
  -- wave three, as offsets one and two
  (blueBottlePairAnchored Validator BlockId Payload).waveAt 0 = 1 ∧
    (∀ κ, κ ≠ 0 → (blueBottlePairAnchored Validator BlockId Payload).waveAt κ = 2) ∧
    -- so an anchor sits at r + 2 above a synchronous slot and at r + 3 above an asynchronous one
    (∀ [S : Slots Validator] (k j : ℕ),
      (blueBottlePairAnchored Validator BlockId Payload).Eligible (S := S) k j ↔
        S.slotRound k + (if S.kind k = 0 then 2 else 3) ≤ S.slotRound j) ∧
    -- and the two waves differ, so the family is not a constant wave in disguise
    (blueBottlePairAnchored Validator BlockId Payload).waveAt 0 ≠
      (blueBottlePairAnchored Validator BlockId Payload).waveAt 1

/-- The `5f + 1` pair, over every fault configuration and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] (U : BlockUniverse Validator BlockId Payload)
    [Slots Validator],
    PairHandover U ∧ HalvesLawful Validator BlockId Payload ∧ PairAgreement U ∧
      PairAgreesOnRungsAndTie Validator BlockId Payload ∧ PairWavesDiffer Validator BlockId Payload

end BlueBottlePair

end Steelhead

end LeanDag
