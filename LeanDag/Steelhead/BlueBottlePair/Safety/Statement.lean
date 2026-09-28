import LeanDag.Steelhead.Model.Pair
/-!
# The `5f + 1` pair's conservativity — statement

Theorem 5 at BlueBottle's two variants: at either end of the dial the
pair is one of its halves alone. One claim:

* **SH-BB4, conservativity** — at a schedule whose every slot is
  synchronous, `p = ∞`, the pair's composite decides exactly as
  Odontoceti; at one whose every slot is asynchronous, `p = 1`, exactly as
  Async BlueBottle. SH4 at the family, whose rung count and tie-break
  agree (SH-BB16d).

The pair's agreement and handover are SH-BB16b and SH-BB3
(`Statement.lean`); its certificate lemmas are its halves' own, O1 to O4
and ABB1 to ABB4, which its laws (SH-BB16a) consume.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Safety

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH-BB4, conservativity.** -/
def Conservative (U : BlockUniverse Validator BlockId Payload) : Prop :=
  -- every slot synchronous: the pair decides as Odontoceti ...
  ((∀ k, S.kind k = 0) → ∀ (V : View Validator BlockId Payload U) (k : ℕ) (v : Option BlockId),
    (blueBottlePairAnchored Validator BlockId Payload).Decided U V k v ↔
      (Odontoceti.odontocetiAnchored Validator BlockId Payload).Decided U V k v) ∧
  -- ... every slot asynchronous, as at period one: as Async BlueBottle
  ((∀ k, S.kind k = 1) → ∀ (V : View Validator BlockId Payload U) (k : ℕ) (v : Option BlockId),
    (blueBottlePairAnchored Validator BlockId Payload).Decided U V k v ↔
      (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload).Decided U V k v)

/-- The `5f + 1` pair's conservativity, over every fault configuration, schedule and block
universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload),
    Conservative U

end Safety

end BlueBottlePair

end Steelhead

end LeanDag
