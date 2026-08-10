import LeanDag.Hybrid.Conservativity
import LeanDag.Schedule

/-!
# H10 — the hybrid bound is necessary

At the one-short committee `n = 5·fb + 3·fc` the admissible interval is
empty, and this file shows the emptiness is not an artefact of the
proof technique: **at every threshold `k`, agreement fails on data.**

The committee is `fb = 1, fc = 1, n = 8` — one validator short of the
bound `9`, with `q = 6` and the would-be interval `[4, 3]` empty. The
case split follows the interval's two ends:

* **`k ≤ 3`** (indirect safety fails): in `UtightA` the candidate is
  directly skipped — six blamers — while an anchor's cone carries three
  support authors (two honest, one Byzantine twin), so the indirect
  rule commits it. One view, two verdicts.
* **`k ≥ 4`** (link integrity fails): in `UtightB` the candidate is
  directly committed — six supporters — while a *valid* anchor packs
  its references with all three available blame authors, leaving only
  three support authors in its cone, below the threshold. The indirect
  rule skips what the direct rule committed.

In both universes the conflicting derivations come from the **same
(full) view**: at `n = 5·fb + 3·fc` the rule set itself is inconsistent,
not merely view-sensitive. Both universes are lawful — validity at
quorum `6`, non-equivocation over `Correct`, and `HonestNoEquiv` in
full: the only twins are the Byzantine validator's.

This is the refutation half of the paper's tight-bound claim (arXiv:
2607.04789, Theorem 1), in the house style of `bound_is_necessary`: the
sufficiency half is the arc's H1–H7, and this file shows one fewer
validator forfeits agreement at *every* threshold.
-/

namespace LeanDagTest

open LeanDag LeanDag.Hybrid

/-- The one-short committee: `n = 8 = 5·1 + 3·1`, expressible because
the class carries only the base bound (`3·(fb+fc)+1 = 7 ≤ 8`). -/
instance hyb8 : HybridFaults (Fin 8) where
  fb := 1
  fc := 1
  byzantine := {0}
  crash := {7}
  disjoint := by decide
  card_byzantine := by decide
  card_crash := by decide
  card_validators := by decide

-- The would-be interval `[2f+c+1, n−3f−2c] = [4, 3]` is empty.
example : Hybrid.q (Fin 8) = 6 := by decide
example : kTight (Fin 8) = 4 := by decide
example : kRel (Fin 8) = 3 := by decide

/-- **No threshold is admissible one validator short.** -/
theorem hyb8_no_admissible : ¬ ∃ k, Admissible (Fin 8) k := by
  rintro ⟨k, h1, h2⟩
  have hfb : HybridFaults.fb (Validator := Fin 8) = 1 := rfl
  have hfc : HybridFaults.fc (Validator := Fin 8) = 1 := rfl
  have hcard : Fintype.card (Fin 8) = 8 := rfl
  omega

/-- Both slots led by validator `1`; slot `s` proposes at round `2s`,
so slot `1` (round `2`) is an eligible anchor for slot `0` (round `0`)
with nothing eligible between. -/
instance hyb8Slots : Slots (Fin 8) :=
  Slots.uniformSingle 2 (by omega) (fun _ => 1)

/-! ## `UtightA` — skipped directly, committed indirectly (`k ≤ 3`) -/

/-- Round `1` blames the candidate six-strong (five honest blamers plus
the Byzantine blame-twin `8`) while three authors support it (the
leader `1`, the crash-prone `7`, and the Byzantine support-twin `9`);
the anchor `17` gathers all three supports into its cone. -/
def tightABlk : Fin 29 → Block (Fin 8) (Fin 29) Unit := fun i =>
  if h : (i : ℕ) < 8 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) = 8 then
    { round := 1, creator := 0, refs := {0, 2, 3, 4, 5, 6}, payload := () }
  else if h : (i : ℕ) = 9 then
    { round := 1, creator := 0, refs := {0, 1, 2, 3, 4, 5}, payload := () }
  else if h : (i : ℕ) = 10 then
    { round := 1, creator := 1, refs := {1, 2, 3, 4, 5, 6}, payload := () }
  else if h : (i : ℕ) < 16 then
    { round := 1, creator := ⟨(i : ℕ) - 9, by omega⟩,
      refs := {0, 2, 3, 4, 5, 6}, payload := () }
  else if h : (i : ℕ) = 16 then
    { round := 1, creator := 7, refs := {1, 2, 3, 4, 5, 7}, payload := () }
  else if h : (i : ℕ) = 17 then
    { round := 2, creator := 1, refs := {9, 10, 16, 11, 12, 13}, payload := () }
  else if h : (i : ℕ) < 23 then
    { round := 2, creator := ⟨(i : ℕ) - 16, by omega⟩,
      refs := {10, 11, 12, 13, 14, 15}, payload := () }
  else
    { round := 3, creator := ⟨(i : ℕ) - 22, by have := i.isLt; omega⟩,
      refs := {17, 18, 19, 20, 21, 22}, payload := () }

def UtightA : BlockUniverse (Fin 8) (Fin 29) Unit where
  ids := Finset.univ
  block := tightABlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

example : HonestNoEquiv UtightA := by decide

-- The direct skip: six blame authors at the decision round.
example : Hybrid.DirectSkipIn UtightA (View.full UtightA) 1 0 := by decide
-- The anchor's cone nonetheless carries three support authors.
example : (Hybrid.coneSupports UtightA 17 1 0 : Finset (Fin 8)).card = 3 := by
  decide
-- The anchor itself is directly committed at its own decision round.
example : Hybrid.DirectCommitIn UtightA (View.full UtightA) 17 2 := by decide

/-! ## `UtightB` — committed directly, skipped indirectly (`k ≥ 4`) -/

/-- Round `1` supports the candidate six-strong (five honest supporters
plus the Byzantine support-twin `8`) against three blame authors (`6`,
the crash-prone `7`, and the Byzantine blame-twin `9`); the *valid*
anchor `17` packs its six references with all three blame authors,
leaving three support authors in its cone. -/
def tightBBlk : Fin 29 → Block (Fin 8) (Fin 29) Unit := fun i =>
  if h : (i : ℕ) < 8 then
    { round := 0, creator := ⟨i, by omega⟩, refs := ∅, payload := () }
  else if h : (i : ℕ) = 8 then
    { round := 1, creator := 0, refs := {0, 1, 2, 3, 4, 5}, payload := () }
  else if h : (i : ℕ) = 9 then
    { round := 1, creator := 0, refs := {0, 2, 3, 4, 5, 6}, payload := () }
  else if h : (i : ℕ) < 15 then
    { round := 1, creator := ⟨(i : ℕ) - 9, by omega⟩,
      refs := {1, 2, 3, 4, 5, 6}, payload := () }
  else if h : (i : ℕ) = 15 then
    { round := 1, creator := 6, refs := {0, 2, 3, 4, 5, 6}, payload := () }
  else if h : (i : ℕ) = 16 then
    { round := 1, creator := 7, refs := {0, 2, 3, 4, 5, 7}, payload := () }
  else if h : (i : ℕ) = 17 then
    { round := 2, creator := 1, refs := {9, 15, 16, 10, 11, 12}, payload := () }
  else if h : (i : ℕ) < 23 then
    { round := 2, creator := ⟨(i : ℕ) - 16, by omega⟩,
      refs := {10, 11, 12, 13, 14, 15}, payload := () }
  else
    { round := 3, creator := ⟨(i : ℕ) - 22, by have := i.isLt; omega⟩,
      refs := {17, 18, 19, 20, 21, 22}, payload := () }

def UtightB : BlockUniverse (Fin 8) (Fin 29) Unit where
  ids := Finset.univ
  block := tightBBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

example : HonestNoEquiv UtightB := by decide

-- The direct commit: six support authors at the decision round.
example : Hybrid.DirectCommitIn UtightB (View.full UtightB) 1 0 := by decide
-- The valid anchor sees only three of them in its cone.
example : (Hybrid.coneSupports UtightB 17 1 0 : Finset (Fin 8)).card = 3 := by
  decide
example : Hybrid.DirectCommitIn UtightB (View.full UtightB) 17 2 := by decide

/-! ## H10 -/

/-- **H10: one validator short, agreement fails at every threshold.**
For each `k` there is a lawful universe — validity at quorum `6`,
`HonestNoEquiv` holding in full — in which one view derives both a
commit and a skip for slot `0`: the indirect rule contradicts the
direct rule it is meant to extend. The interval's two ends name the two
attacks, and one of them is always available. -/
theorem hybrid_bound_necessary (k : ℕ) :
    ∃ (U : BlockUniverse (Fin 8) (Fin 29) Unit) (L : Fin 29),
      HonestNoEquiv U ∧
      Hybrid.Decided k U (View.full U) 0 (some L) ∧
      Hybrid.Decided k U (View.full U) 0 none := by
  by_cases hk : k ≤ 3
  · -- indirect safety fails: skipped directly, committed indirectly
    refine ⟨UtightA, 1, by decide, ?_, ?_⟩
    · refine Decided.indirectCommit (j := 1) (A := 17) (by omega) (by decide)
        (Decided.directCommit (by decide) (by decide))
        (fun i h1 h2 _ => absurd h2 (by omega))
        (by decide) ?_ ?_
      · show k ≤ (Hybrid.coneSupports UtightA 17 1 0).card
        have h3 : (Hybrid.coneSupports UtightA 17 1 0).card = 3 := by decide
        omega
      · intro L' hL' _ hlt
        have hall : ∀ M : Fin 29, IsLeaderBlock UtightA 0 M → M = 1 := by
          decide
        have := hall L' hL'
        subst this
        exact absurd hlt (lt_irrefl _)
    · refine Decided.directSkip (fun L' hL' => ?_)
      have hall : ∀ M : Fin 29, IsLeaderBlock UtightA 0 M → M = 1 := by decide
      have := hall L' hL'
      subst this
      decide
  · -- link integrity fails: committed directly, skipped indirectly
    refine ⟨UtightB, 1, by decide,
      Decided.directCommit (by decide) (by decide), ?_⟩
    refine Decided.indirectSkip (j := 1) (A := 17) (by omega) (by decide)
      (Decided.directCommit (by decide) (by decide))
      (fun i h1 h2 _ => absurd h2 (by omega))
      (fun L' hL' => ?_)
    have hall : ∀ M : Fin 29, IsLeaderBlock UtightB 0 M → M = 1 := by decide
    have := hall L' hL'
    subst this
    show ¬ k ≤ (Hybrid.coneSupports UtightB 17 1 0).card
    have h3 : (Hybrid.coneSupports UtightB 17 1 0).card = 3 := by decide
    omega

#print axioms hyb8_no_admissible
#print axioms hybrid_bound_necessary

end LeanDagTest
