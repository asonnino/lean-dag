import LeanDag.FinWhale.Model.Verdict
import Mathlib.Order.Interval.Finset.Nat

/-!
# FinWhale — the reverse pass, as a procedure

`Model/Verdict.lean` states the pass as a condition on a verdict
assignment. This file computes it. `slotVerdict` decides one slot from
the verdicts above it — a direct commit if there is one, a direct skip if
there is one, and otherwise the first slot above `r + 2` that is not
skipped, read through the tie-break — and `passFrom` threads that down
from the horizon, where nothing is decided, to slot `0`. `decOf` is the
result, a function of the DAG, the tie-break and the horizon.

`Pass.lean` proves it well-formed.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] [LinearOrder BlockId] {Payload : Type*}

/-- The blocks of a slot that are directly committed. At most one, by
`direct_commit_unique`. -/
def directCommits (D : Dag Validator BlockId Payload) (r : ℕ) : Finset BlockId :=
  (slotBlocks D r).filter (fun l => DirectCommit D l)

/-- The candidates for the anchor of `r`: the slots above `r + 2` and
below the horizon that the verdicts above do not skip. -/
def anchorCands (N : ℕ) (above : ℕ → Verdict BlockId) (r : ℕ) : Finset ℕ :=
  (Finset.Ioc (r + 2) N).filter (fun a => above a ≠ Verdict.skip)

/-- **The indirect verdict**: read the first non-skipped slot above
`r + 2` through the tie-break. Where there is none the slot stays
undecided, which is what an undecided anchor gives too. -/
def anchorVerdict (choose : BlockId → ℕ → Option BlockId) (N : ℕ)
    (above : ℕ → Verdict BlockId) (r : ℕ) : Verdict BlockId :=
  if hc : (anchorCands N above r).Nonempty then
    match above ((anchorCands N above r).min' hc) with
    | Verdict.commit A =>
        match choose A r with
        | some b => Verdict.commit b
        | none => Verdict.skip
    | _ => Verdict.undecided
  else Verdict.undecided

/-- **One slot's verdict, from the verdicts above it.** -/
def slotVerdict (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) (N : ℕ)
    (above : ℕ → Verdict BlockId) (r : ℕ) : Verdict BlockId :=
  if h : (directCommits D r).Nonempty then Verdict.commit ((directCommits D r).min' h)
  else if DirectSkip D r then Verdict.skip
  else anchorVerdict choose N above r

/-- **The pass, from slot `s` downward.** Slots below `s` are left
undecided; slot `s` is decided from the verdicts above it, and those are
what the pass from `s + 1` gives. -/
def passFrom (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) (N : ℕ) (s : ℕ) : ℕ → Verdict BlockId :=
  if h : N < s then fun _ => Verdict.undecided
  else fun r =>
    if r = s then slotVerdict D choose N (passFrom D choose N (s + 1)) s
    else passFrom D choose N (s + 1) r
termination_by N + 1 - s
decreasing_by all_goals omega

/-- **The verdicts of a validator whose view is `D`.** -/
def decOf (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) (N : ℕ) : ℕ → Verdict BlockId :=
  passFrom D choose N 0

variable {D : Dag Validator BlockId Payload} {choose : BlockId → ℕ → Option BlockId} {N : ℕ}


end FinWhale

end LeanDag
