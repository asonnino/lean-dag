import LeanDag.FinWhale.Model.Decision

/-!
# FinWhale — a validator's view, and the rules relative to one

A **view** is part of the universe closed under references, and it is a
`Dag` in its own right: validity and non-equivocation are inherited from
the universe, and the view's completeness is its closure. `IsView` states
that and `restrict` builds the DAG.

`viewCommit` and `viewSkip` are the direct rules as a validator with that
view evaluates them, which is how the protocol actually runs — every
count of the rule taken over the blocks the validator holds. `View.lean`
proves what transports between a view and the universe and what does not.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload} {V : Finset BlockId}

/-- **A view**: part of the universe, closed under references. -/
structure IsView (D : Dag Validator BlockId Payload) (V : Finset BlockId) : Prop where
  /-- Only blocks that exist. -/
  subset : V ⊆ D.ids
  /-- And everything they reference. -/
  closed : ∀ i ∈ V, ∀ j ∈ (D.block i).refs, j ∈ V

/-- **A view is a DAG.** Validity and non-equivocation are inherited; the
view's completeness is its closure. -/
def restrict (D : Dag Validator BlockId Payload) (V : Finset BlockId) (hV : IsView D V) :
    Dag Validator BlockId Payload where
  ids := V
  block := D.block
  leader := D.leader
  complete := hV.closed
  valid := fun i hi => D.valid i (hV.subset hi)
  correct_single := fun i hi j hj => D.correct_single i (hV.subset hi) j (hV.subset hj)

variable {hV : IsView D V}

/-! ## The exclusions, on two views -/

/-- The direct commit rule as a validator with view `V` evaluates it. -/
def viewCommit (D : Dag Validator BlockId Payload) (V : Finset BlockId) (hV : IsView D V)
    (r : ℕ) (l : BlockId) : Prop :=
  l ∈ slotBlocks (restrict D V hV) r ∧ DirectCommit (restrict D V hV) l

/-- And the direct skip rule. -/
def viewSkip (D : Dag Validator BlockId Payload) (V : Finset BlockId) (hV : IsView D V)
    (r : ℕ) : Prop :=
  DirectSkip (restrict D V hV) r


end FinWhale

end LeanDag
