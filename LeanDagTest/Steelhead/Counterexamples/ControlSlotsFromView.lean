import LeanDagTest.Mysticeti.Model
import LeanDag.Steelhead.Model.Period
/-!
# Steelhead counterexample: control slots read from the view

Issue #35's step 6 on data: were a round a control slot whenever a validator's own view holds
enough shares to open its coin, two validators would scan different control slots and find
different anchors, and Theorem 4 would fail. Fixed by rule, as the arc and the implementation
have it (`is_control_round`, `controlSlots`), the control slots are the same in every view
(`steelhead.md` §7, finding 1).

The model carries no shares, so this file adds one as the block payload: a block's payload is
`true` when its author put a share for the coin of the round `wa − 1` below into it, where the
paper's protocol section has a share travel. One universe, `cv20`: five rounds `0..4` of the
committee of the other witnesses at wave `3`, every non-genesis block referencing the whole round
below, except that the round-`4` blocks of validators `1`, `2` and `3` omit validator `0`'s
round-`3` block. At round `3` validators `0`, `1` and `2` carry a share for round `1` and
validator `3` does not; at round `4` all four carry a share for round `2`. Two views, neither
inside the other: `cvV₁`, the causal history of the round-`3` blocks of validators `0`, `1`, `2`,
and `cvV₂`, that of the round-`4` blocks of validators `1`, `2`, `3`. On them:

* **read from the view**, round `1` is a control slot for `cvV₁`, which holds three of its
  shares, and not for `cvV₂`, which holds two; round `2` is one for `cvV₂` and not for `cvV₁`,
  which holds no round-`4` block. The two views enumerate different control slots of interval
  `0`: `[1]` and `[2]`;
* each view directly commits the coin's candidate at the round it counts, so **the scans anchor
  on different rounds**, `1` and `2`, and the windows and the periods derived from them part
  company: step 5 of #35 fails;
* **under the rule** at period `1` every round is a control slot in both views, round `1`'s
  candidate is directly committed in both, and interval `0`'s anchor is round `1` in both
  (`IntervalAnchor`), as SH10l makes general.

The committee is the standard witness one, validator `0` Byzantine and `f = 1`
(`LeanDagTest/Mysticeti/Model.lean`), so the quorum is `3`; the schedule is the coin schedule
`chainSlots cvCoin`, one slot per round led by the coin, every slot asynchronous.
-/

namespace LeanDagTest

open LeanDag LeanDag.Steelhead

set_option maxRecDepth 4096

/-- The coin: validator `(r + 1) % 4` at round `r`. -/
def cvCoin : ℕ → Fin 4 := fun r => ⟨(r + 1) % 4, by omega⟩

/-- The coin schedule: one slot per round led by the coin, every slot asynchronous, which is the
rule's control schedule at period `1`. -/
local instance cvSlots : Slots (Fin 4) := chainSlots cvCoin

/-! ## `cv20`: five rounds, with shares as the payload -/

/-- Block `4m + v` is validator `v`'s round-`m` block. Every non-genesis block references the
whole round below, except that the round-`4` blocks of validators `1`, `2`, `3` omit block `12`,
validator `0`'s round-`3` block. The payload is the share flag: `true` at blocks `12`, `13`, `14`
(a share for round `1`) and at the round-`4` blocks `16` to `19` (a share for round `2`). -/
def cvBlk : Fin 20 → Block (Fin 4) (Fin 20) Bool := fun i =>
  { round := (i : ℕ) / 4, creator := ⟨(i : ℕ) % 4, by omega⟩,
    refs := if (i : ℕ) < 4 then ∅ else
      Finset.univ.filter (fun j : Fin 20 => (j : ℕ) / 4 + 1 = (i : ℕ) / 4 ∧
        ¬ ((i : ℕ) / 4 = 4 ∧ (i : ℕ) % 4 ≠ 0 ∧ (j : ℕ) = 12)),
    payload := decide ((12 ≤ (i : ℕ) ∧ (i : ℕ) ≤ 14) ∨ 16 ≤ (i : ℕ)) }

def cv20 : BlockUniverse (Fin 4) (Fin 20) Bool where
  ids := Finset.univ
  block := cvBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

-- The omission and the shares, on data.
example : (cv20.block 16).refs = {12, 13, 14, 15} := by decide
example : (cv20.block 17).refs = {13, 14, 15} := by decide
example : (cv20.block 15).payload = false := by decide
example : (cv20.block 14).payload = true := by decide

/-- The causal history of the round-`3` blocks of validators `0`, `1`, `2`: rounds `0` to `2`
and blocks `12`, `13`, `14`. -/
def cvV₁ : View (Fin 4) (Fin 20) Bool cv20 where
  ids := Finset.univ.filter fun b : Fin 20 => (b : ℕ) ≤ 14
  subset_ids := by decide
  complete := by decide

/-- The causal history of the round-`4` blocks of validators `1`, `2`, `3`: rounds `0` to `2`,
blocks `13`, `14`, `15` and blocks `17`, `18`, `19`. -/
def cvV₂ : View (Fin 4) (Fin 20) Bool cv20 where
  ids := Finset.univ.filter fun b : Fin 20 =>
    (b : ℕ) ≤ 11 ∨ (13 ≤ (b : ℕ) ∧ (b : ℕ) ≤ 15) ∨ 17 ≤ (b : ℕ)
  subset_ids := by decide
  complete := by decide

-- Neither view lies inside the other.
example : ¬ cvV₁.ids ⊆ cvV₂.ids := by decide
example : ¬ cvV₂.ids ⊆ cvV₁.ids := by decide

/-! ## The control reading read from the view -/

/-- **A round carries a coin, read from a view**: the view holds a quorum of the blocks of round
`r + wa − 1` that carry a share, where the shares travel. No author equivocates, so the blocks
counted are as many as their authors. The reading issue #35 warns against. -/
abbrev viewCoin (V : View (Fin 4) (Fin 20) Bool cv20) (r : ℕ) : Prop :=
  quorumCard (Fin 4) ≤
    ((blocksAt cv20 (r + 2)).filter fun b => b ∈ V.ids ∧ (cv20.block b).payload = true).card

/-- The coin's candidate at round `r`: the block of validator `cvCoin r` at that round. -/
def cvCand (r : ℕ) : Fin 20 := ⟨(4 * r + (cvCoin r : ℕ)) % 20, Nat.mod_lt _ (by omega)⟩

/-- **The control slots of interval `0` read from a view**: its rounds `1` to `4` that carry a
coin in the view. -/
def viewControl (V : View (Fin 4) (Fin 20) Bool cv20) : List ℕ :=
  [1, 2, 3, 4].filter fun r => decide (viewCoin V r)

/-- **The anchor read from a view**: the first control slot of interval `0`, read from the view,
whose coin candidate the view directly commits. On `cv20` neither view holds a lower control slot
undecided, so this is where the scan of interval `0` stops. -/
def viewAnchor (V : View (Fin 4) (Fin 20) Bool cv20) : Option ℕ :=
  (viewControl V).find? fun r => decide (MahiMahi.DirectCommitIn cv20 V 3 (cvCand r) r)

-- Round `1` carries a coin in `cvV₁` and not in `cvV₂`; round `2` the other way round.
example : viewCoin cvV₁ 1 := by decide
example : ¬ viewCoin cvV₂ 1 := by decide
example : ¬ viewCoin cvV₁ 2 := by decide
example : viewCoin cvV₂ 2 := by decide

/-- **The views enumerate different control slots.** -/
theorem cv_control_differ : viewControl cvV₁ = [1] ∧ viewControl cvV₂ = [2] := by decide

-- Each view directly commits the candidate of the round it counts.
example : IsLeaderBlock cv20 1 (cvCand 1) := by decide
example : IsLeaderBlock cv20 2 (cvCand 2) := by decide
example : MahiMahi.DirectCommitIn cv20 cvV₁ 3 (cvCand 1) 1 := by decide
example : MahiMahi.DirectCommitIn cv20 cvV₂ 3 (cvCand 2) 2 := by decide

/-- **The views anchor on different rounds**, so the windows they replay and the periods they
derive differ: Theorem 4 fails under the view reading. -/
theorem cv_anchors_differ : viewAnchor cvV₁ = some 1 ∧ viewAnchor cvV₂ = some 2 := by decide

/-! ## The control reading by rule -/

-- At period `1` slot `1` of the scan of interval `0` is round `1`, in every view.
example : controlRound 4 4 0 1 1 = 1 := by decide
example : (controlSlots cvCoin 4 4 0 1).leader 1 = cvCoin 1 := by decide

/-- **Under the rule both views commit round `1`'s candidate**: the same control slot, the same
verdict, whatever else each view holds. -/
theorem cv_rule_commits :
    MahiMahi.DirectCommitIn cv20 cvV₁ 3 (cvCand 1) 1 ∧
      MahiMahi.DirectCommitIn cv20 cvV₂ 3 (cvCand 1) 1 := by decide

/-- **Under the rule interval `0`'s anchor is round `1` in `cvV₁`.** -/
theorem cv_rule_anchor₁ : IntervalAnchor 4 4 (MahiMahi.mahiMahiAnchored _ _ _ 3) cvCoin cv20 cvV₁ 0
    1 1 (cvCand 1) where
  pos := by decide
  mem := by decide
  commit := MahiMahi.Decided.directCommit (S := controlSlots cvCoin 4 4 0 1) (by decide) (by decide)
  below := fun i' h1 _ hi => absurd h1 (by interval_cases i'; decide)

/-- **And in `cvV₂`**, the view that would not even count round `1` a control slot when reading
its shares. -/
theorem cv_rule_anchor₂ : IntervalAnchor 4 4 (MahiMahi.mahiMahiAnchored _ _ _ 3) cvCoin cv20 cvV₂ 0
    1 1 (cvCand 1) where
  pos := by decide
  mem := by decide
  commit := MahiMahi.Decided.directCommit (S := controlSlots cvCoin 4 4 0 1) (by decide) (by decide)
  below := fun i' h1 _ hi => absurd h1 (by interval_cases i'; decide)

/-! ## Axioms

Nothing here should ever acquire an axiom beyond the standard three. -/

#print axioms cv20
#print axioms cv_control_differ
#print axioms cv_anchors_differ
#print axioms cv_rule_anchor₁
#print axioms cv_rule_anchor₂

end LeanDagTest
