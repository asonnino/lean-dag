import LeanDagTest.BlackMarlin.Agreement
import LeanDag.BlackMarlin.Ledger.Proof
import LeanDag.BlackMarlin.Descent.Proof
import Mathlib.Tactic.IntervalCases

/-!
# Black Marlin witnesses — the delivered order on data

`black-marlin.md` §11. The covered four-round model carries a flush
record — the four anchors of rounds `0` to `3` — and on it the descent's
candidate sets are singletons, which is BMD1 on data. `OutputAt` then
places a block at the round it enters the ledger at, and the anti-vacuity
is that it does not enter earlier.
-/

namespace LeanDagTest

namespace BlackMarlin

set_option maxRecDepth 2000000

open LeanDag LeanDag.BlackMarlin

/-- The rotation of BML5 at four validators, as in the other witnesses. -/
local instance bmRR3 : Rotation (Fin 4) := Liveness.roundRobin 4 (by omega)

/-! ## The descent has one candidate at each step -/

example : coneAnchors Ufull 5 0 = {0} := by decide
example : coneAnchors Ufull 10 1 = {5} := by decide
example : coneAnchors Ufull 15 2 = {10} := by decide

/-- Anti-vacuity: a cone two rounds deep is not a singleton by accident —
it holds the round-0 anchor as well, which is why the step matters. -/
example : (0 : Fin 16) ∈ coneAnchors Ufull 10 0 := by decide

/-- **BMD1′ on data**: at a round whose anchor is reliable the candidates
are a singleton however deep the cone — here validator `2` anchors round
`2` and is not Byzantine, so the round-3 anchor's cone holds exactly one
of its blocks. -/
example : ∀ X ∈ coneAnchors Ufull 15 2, ∀ Y ∈ coneAnchors Ufull 15 2, X = Y :=
  fun X hX Y hY =>
    (Ledger.holds (Fin 4) (Fin 16) Unit Ufull).2.1 2 15 X Y (by decide) hX hY

/-- The Byzantine validator is `0`, which anchors round `0`; that is the
only round of this model where a tie could arise at all. -/
example : Rotation.anchor (Validator := Fin 4) 0 ∉ (Correct : Finset (Fin 4)) ∧
    Rotation.anchor (Validator := Fin 4) 1 ∈ (Correct : Finset (Fin 4)) ∧
    Rotation.anchor (Validator := Fin 4) 2 ∈ (Correct : Finset (Fin 4)) ∧
    Rotation.anchor (Validator := Fin 4) 3 ∈ (Correct : Finset (Fin 4)) := by decide

/-! ## The record -/

/-- The anchor of round `ρ` is validator `ρ % 4`, whose block at that
round is id `4 * ρ + ρ % 4`; the model stops at round `3`. -/
def fullBlock : ℕ → Option (Fin 16)
  | 0 => some 0
  | 1 => some 5
  | 2 => some 10
  | 3 => some 15
  | _ => none

/-- The flush record of the covered four-round model. -/
def fullFlush : Flush Ufull where
  block := fullBlock
  isAnchor := by
    intro ρ L h
    match ρ with
    | 0 | 1 | 2 | 3 => simp only [fullBlock, Option.some.injEq] at h; subst h; decide
    | (n + 4) => simp [fullBlock] at h
  step := by
    intro ρ L M hL hM
    match ρ with
    | 0 | 1 | 2 =>
        simp only [fullBlock, Option.some.injEq] at hL hM
        subst hL; subst hM; decide
    | 3 => simp [fullBlock] at hM
    | (n + 4) => simp [fullBlock] at hL
  dense := by
    intro ρ M hM _
    match ρ with
    | 0 | 1 | 2 => decide
    | 3 => simp [fullBlock] at hM
    | (n + 4) => simp [fullBlock] at hM

example : fullFlush.block 0 = some 0 ∧ fullFlush.block 1 = some 5 ∧
    fullFlush.block 2 = some 10 ∧ fullFlush.block 3 = some 15 ∧
    fullFlush.block 4 = none := by decide

/-! ## The ledger -/

/-- **BMD6 on data**: validator `3`'s genesis block enters the ledger at
round `1`, with the round-1 anchor — the first flushed anchor whose cone
holds it. -/
example : OutputAt Ufull fullFlush 3 1 := by
  refine ⟨⟨5, by decide, (mem_history_iff (by decide)).mp (by decide)⟩, ?_⟩
  intro σ hσ L hL hr
  have hσ0 : σ = 0 := by omega
  subst hσ0
  have : L = 0 := by
    have : fullFlush.block 0 = some 0 := by decide
    rw [this] at hL
    exact (Option.some.inj hL).symm
  subst this
  exact absurd ((mem_history_iff (by decide)).mpr hr) (by decide)

/-- And so it is in the ledger from round `2` on, but not before. -/
example : (3 : Fin 16) ∈ ledgerSet Ufull fullFlush 2 :=
  (Ledger.holds (Fin 4) (Fin 16) Unit Ufull).2.2.2.2.2.2.2.2.2.2
    fullFlush 1 5 3 (by decide) ((mem_history_iff (by decide)).mp (by decide))


/-! ## The descent computed

`flushRecord` runs L21–L24 rather than assuming a record, so the four
anchors above are what it returns. -/

example : flushRecord Ufull 15 3 = some 15 ∧ flushRecord Ufull 15 2 = some 10 ∧
    flushRecord Ufull 15 1 = some 5 ∧ flushRecord Ufull 15 0 = some 0 := by decide

/-- The computed record is the one built by hand. -/
example : flushRecord Ufull 15 0 = fullFlush.block 0 ∧
    flushRecord Ufull 15 1 = fullFlush.block 1 ∧
    flushRecord Ufull 15 2 = fullFlush.block 2 ∧
    flushRecord Ufull 15 3 = fullFlush.block 3 ∧
    flushRecord Ufull 15 4 = fullFlush.block 4 := by decide

/-- **BME5 on data**: the descent from the round-3 anchor and the descent
from the round-1 anchor meet at round `1`, so they agree at round `0` —
with no hypothesis about what lies between. -/
example : flushRecord Ufull 15 0 = flushRecord Ufull 5 0 :=
  (Descent.holds (Fin 4) (Fin 16) Unit Ufull).2.2.2.2 15 5 5 1 0
    (by decide) (by decide) (by decide) (by decide) (by omega)

#print axioms LeanDag.BlackMarlin.Descent.holds

#print axioms LeanDag.BlackMarlin.Ledger.holds

end BlackMarlin

end LeanDagTest
