import LeanDagTest.AsyncBlueBottle.Model
import LeanDagTest.AsyncBlueBottle.Counting
import LeanDag.AsyncBlueBottle.Liveness.Statement
/-!
# Async BlueBottle witnesses — the clause on data

The unpredictable-leader clause of `Model/Unpredictable.lean` settled on
the universes of the earlier witnesses (`async-bluebottle.md` §6):

* **satisfiable** — on the fully connected `full6`, round-robin satisfies
  both forms of the clause;
* **refutable with a deterministic schedule** — on the aiming pattern
  `aim6`, round-robin violates the single-hit clause: the one window that
  matters names exactly the starved validator;
* **independent of fairness** — the same schedule satisfies the core's
  `FairScheduleOn Correct`, so the clause is not a consequence of
  fairness;
* **`SpansEligible` on data** — at one leader per round a run of three
  slots spans eligibility;
* **ABB9a on data** — a good leader's slot is committed from the full
  view.

The clause quantifies over every window below the horizon, which is not a
`decide`-able shape; each witness bounds the window index by `omega` on
the unfolded decision round and then decides the finitely many cases.
-/

namespace LeanDagTest

set_option maxRecDepth 4096

open LeanDag LeanDag.AsyncBlueBottle

/-- Round-robin from validator `1`, one leader per round, as in the other
witness files. -/
local instance abbSlotsL : Slots (Fin 6) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨(k + 1) % 6, by omega⟩)

/-! ## Satisfiable: `full6` under round-robin -/

-- Every slot of the first two rounds is good (four rounds reach decision
-- round `3`).
example : good full6 0 = Finset.univ := by decide
example : good full6 1 = Finset.univ := by decide

/-- The single-hit clause with windows of one: the only windows below the
horizon `3` are at `k = 0, 1`. -/
theorem full6_unpredictable : UnpredictableWithin full6 1 3 := by
  intro k hk
  have hk' : k ≤ 1 := by
    simp [AnchoredRule.decisionRound, asyncBlueBottleAnchored] at hk
    omega
  refine ⟨k, le_refl k, by omega, ?_⟩
  interval_cases k <;> decide

/-- The run form with runs of two: below the horizon `4` the only window
is `k = 0`, and slots `0, 1` are both good. -/
theorem full6_unpredictableRun : UnpredictableRunWithin full6 1 2 4 := by
  intro k hk
  have hk' : k = 0 := by
    simp [AnchoredRule.decisionRound, asyncBlueBottleAnchored] at hk
    omega
  subst hk'
  refine ⟨0, le_refl 0, by omega, ?_⟩
  intro i hi
  interval_cases i <;> decide

/-! ## Refutable with a deterministic schedule -/

-- On the aiming pattern, the window at `k = 0` contains only slot `0`,
-- whose round-robin leader is the starved validator.
example : (1 : Fin 6) ∉ good aim6 0 := by decide

theorem aim6_not_unpredictable : ¬ UnpredictableWithin aim6 1 3 := by
  intro h
  obtain ⟨k', hk1, hk2, hgood⟩ := h 0 (by decide)
  have : k' = 0 := by omega
  subst this
  exact absurd hgood (by decide)

/-! ## Independent of fairness -/

/-- Round-robin names a correct leader arbitrarily far out — the core's
fairness clause, on the same schedule the clause refutes. -/
example : FairScheduleOn (S := abbSlotsL) (Correct : Finset (Fin 6)) := by
  intro k
  refine ⟨6 * k, by omega, ?_⟩
  have hl : abbSlotsL.leader (6 * k) = (1 : Fin 6) := by
    apply Fin.ext
    simp
  rw [hl]
  decide

/-! ## `SpansEligible` on data -/

/-- At one leader per round, a run of three slots spans eligibility: slot
`i < b` has decision round `i + 2 < b + 2`, the round of the run's last
slot. -/
example : (asyncBlueBottleAnchored (Fin 6) (Fin 24) Unit).SpansEligible 3 := by
  intro b i hi
  simp [AnchoredRule.Eligible, EligibleAt, asyncBlueBottleAnchored]
  omega

/-! ## ABB9a on data -/

-- A good leader's slot is committed from the full view.
example : (1 : Fin 6) ∈ good full6 0 := by decide
example : AsyncBlueBottle.Decided full6 (View.full full6) 0 (some 1) :=
  Decided.directCommit (by decide) (by decide)

/-! ## Axioms -/

#print axioms full6_unpredictable
#print axioms full6_unpredictableRun
#print axioms aim6_not_unpredictable

end LeanDagTest
