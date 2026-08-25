import LeanDagTest.BlackMarlin.Liveness
import LeanDag.BlackMarlin.ViewLiveness.Proof

/-!
# Black Marlin witnesses — liveness read at a validator's view

`black-marlin.md` §15. The universe-level results are witnessed in
`LeanDagTest/BlackMarlin/Liveness`; these are their view-level
counterparts on the same four-round model, plus the boundary.

The contrast is the point. BMV3 holds at round `2`, whose anchor is
reliable: a view holding the reliable blocks of round `3` sees the
support quorum, so the rule can be applied without waiting for anything
a Byzantine validator might withhold. There is no counterpart at a round
the equivocator anchors, and `LeanDagTest/BlackMarlin/Counting` supplies
the refusal — a view holding **every** reliable block, and everything
those reference, in which neither of the twins is supported.
-/

namespace LeanDagTest

namespace BlackMarlin

open LeanDag LeanDag.BlackMarlin

local instance bmRRv : Rotation (Fin 4) := Liveness.roundRobin 4 (by omega)

/-- **BMV1 on data**: above every round the rotation names one that every
reliable validator commits **on its own view**, in any sufficiently
grown DAG under any pace. Derived from `ViewLiveness.holds`. -/
example (r : ℕ) : ∃ r', r ≤ r' ∧ 0 ≤ r' ∧
    ViewLiveness.CommitsInViews (Validator := Fin 4) (Fin 16) Unit
      (Correct : Finset (Fin 4)) 0 r' :=
  (ViewLiveness.holds (Fin 4) (Fin 16) Unit).1 (Correct : Finset (Fin 4)) 0 r
    card_correct (Liveness.holds.2 4 (by omega))

/-- **BMV2 on data**: and such a round delivers, at every reliable view,
whatever any view committed below it. -/
example (ρ : ℕ) : ∃ r, ρ ≤ r ∧ 0 ≤ r ∧
    ViewLiveness.DeliversInViews (Validator := Fin 4) (Fin 16) Unit
      (Correct : Finset (Fin 4)) 0 ρ r :=
  (ViewLiveness.holds (Fin 4) (Fin 16) Unit).2.1 (Correct : Finset (Fin 4)) 0 ρ
    card_correct (Liveness.holds.2 4 (by omega))

/-- The round-`2` anchor is `10`, and its author is reliable. -/
example : IsAnchor Ufull 2 10 ∧
    Rotation.anchor (Validator := Fin 4) 2 ∈ (Correct : Finset (Fin 4)) := by decide

/-- **BMV3 on data**: so any view holding the reliable blocks of round
`3` sees the support quorum for it. No block of the equivocator is
needed, and no waiting. -/
example (V : View (Fin 4) (Fin 16) Unit Ufull)
    (hheld : ∀ b ∈ Ufull.ids, (Ufull.block b).creator ∈ (Correct : Finset (Fin 4)) →
      (Ufull.block b).round = 3 → b ∈ V.ids) :
    SupportedIn Ufull V 10 2 :=
  (ViewLiveness.holds (Fin 4) (Fin 16) Unit).2.2 Ufull (Correct : Finset (Fin 4)) 0 2 V 10
    card_correct ufull_synchronised (by omega) (ufull_populated (by omega))
    (by decide) (by decide) hheld

/-- Anti-vacuity, and the content of BMV3 on data: the **reliable**
supporters alone reach the quorum, so the equivocator's block at round
`3` is not needed even though it is there. -/
example : supporters Ufull 10 3 = {0, 1, 2, 3} ∧ quorumCard (Fin 4) = 3 ∧
    quorumCard (Fin 4) ≤ (supporters Ufull 10 3 ∩ (Correct : Finset (Fin 4))).card := by
  decide

#print axioms LeanDag.BlackMarlin.ViewLiveness.holds

end BlackMarlin

end LeanDagTest
