import LeanDag.Steelhead.Model.Clauses
import LeanDag.Steelhead.Model.Compose
import LeanDag.Steelhead.Model.Chain
/-!
# Safety at any lawful rule — statement

The paper's Theorem 1 and Corollary 1 for any rule of its interface, and
Theorem 5's conservativity for any family (`steelhead.md` §3). Every claim
reads its rule only through the anchored relation's laws, which are the
paper's clauses A2 and A3 in the relation's terms, and the tie-break's
choice; the two pairs' instances are in `MahiMahiPair/Safety/` and
`BlueBottlePair/`. Four claims:

* **SH2, agreement** — two views deciding one slot reach the same verdict,
  by any routes, at any lawful rule;
* **SH3, handover** — a direct commit in one view is committed by every
  view that finds an anchor for the slot, and no view skips it: the
  anchor's rungs have a choice, and a lawful rule decides a slot one way;
* **SH4, conservativity** — at a schedule that gives every slot one kind
  `κ`, the composite of a family decides exactly as the family's rule at
  `κ`, provided the family agrees on its rung count and tie-break: the
  composite reads every datum of a slot from the slot's rule. So the dial
  at either end is one of the two rules alone;
* **SH5a, chain agreement** — the chain's verdicts agree across views: SH2
  at the chain schedule, one slot per round led by the round's coin
  leader.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Safety

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH2, agreement.** -/
def Agreement (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (v₁ v₂ : Option BlockId),
    R.Laws → R.Decided U V₁ k v₁ → R.Decided U V₂ k v₂ → v₁ = v₂

/-- **SH3, handover.** -/
def Handover (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (L : BlockId),
    -- the rule is lawful and its tie-break has a choice
    R.Laws → LeastLinked R →
    -- L is slot k's candidate, directly committed in V₁
    IsLeaderBlock U k L → R.Commit U V₁ L (S.slotRound k) (S.kind k) →
    -- then any anchor V₂ finds for k commits L ...
    (∀ (j : ℕ) (A : BlockId),
      k < j → R.Eligible k j → R.Decided U V₂ j (some A) →
      (∀ m, k < m → m < j → R.Eligible k m → R.Decided U V₂ m none) →
      R.Decided U V₂ k (some L)) ∧
    -- ... and V₂ never skips k
    ¬ R.Decided U V₂ k none

/-- **SH4, conservativity.** -/
def ComposeConservative (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (rules : ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct) (κ : ℕ),
    -- the family agrees on its rung count and tie-break
    (∀ r, (rules r).rungs = (rules 0).rungs) → (∀ r, (rules r).tie = (rules 0).tie) →
    -- the schedule gives every slot the kind κ
    (∀ k, S.kind k = κ) →
    -- then the composite decides as the rule of that kind
    ∀ (V : View Validator BlockId Payload U) (k : ℕ) (v : Option BlockId),
      (compose rules).Decided U V k v ↔ (rules κ).Decided U V k v

/-- **SH5a, chain agreement.** -/
def ChainAgreement (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (coin : ℕ → Validator) (V₁ V₂ : View Validator BlockId Payload U) (r : ℕ)
    (v₁ v₂ : Option BlockId),
    R.Laws → R.Decided (S := chainSlots coin) U V₁ r v₁ →
    R.Decided (S := chainSlots coin) U V₂ r v₂ → v₁ = v₂

/-- Safety at any rule, over every fault configuration, schedule, block universe and anchored
rule the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct),
    Agreement U R ∧ Handover U R ∧ ComposeConservative U ∧ ChainAgreement U R

end Safety

end Steelhead

end LeanDag
