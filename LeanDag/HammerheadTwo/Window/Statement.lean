import LeanDag.HammerheadTwo.Model.Window

/-!
# HH2 — the window is agreed

The paper's Window Agreement lemma (`hammerhead-two.md` §6): two honest
validators that commit the anchor compute the same window. In this
development the window a validator measures on is the anchor's causal
history, and the claim is that this history is *determined by the
anchor*: whichever view holds the anchor holds its whole history — A2,
`BaseRule.Laws.view_complete` — so restricting the history to the
validator's own view changes nothing, and two validators restricting it
to their two views obtain one set.

* **HH2a, the history is in view** — a view holding `A` holds
  `historyFrom (block U) A`.
* **HH2b, window agreement** — two views holding `A` restrict its history
  to the same set.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace HammerheadTwo

namespace Window

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **HH2a, the history is in view**: a view holding a block holds its
whole causal history. A2 is what carries it — views are closed under
references, and the history is what references reach. -/
def HistoryInView (R : BaseRule Validator BlockId Payload) : Prop :=
  ∀ (U : R.Universe) (V : R.View U) (A : BlockId),
    A ∈ R.viewIds V → historyFrom (R.block U) A ⊆ R.viewIds V

/-- **HH2b, window agreement**: two validators holding the anchor compute
the same window — the anchor's history restricted to either view is the
history itself, so the two restrictions coincide. -/
def WindowAgreement (R : BaseRule Validator BlockId Payload) : Prop :=
  ∀ (U : R.Universe) (V₁ V₂ : R.View U) (A : BlockId),
    A ∈ R.viewIds V₁ → A ∈ R.viewIds V₂ →
    historyFrom (R.block U) A ∩ R.viewIds V₁ = historyFrom (R.block U) A ∩ R.viewIds V₂

/-- The window is agreed, for every base rule satisfying the laws. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload), R.Laws →
    HistoryInView R ∧ WindowAgreement R

end Window

end HammerheadTwo

end LeanDag
