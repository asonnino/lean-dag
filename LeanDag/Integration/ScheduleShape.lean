import LeanDag.GC.ChopDecided

/-!
# I13, I15 — the schedule layer survives truncation

The cells `integration.md`'s first draft missed entirely, and the
prerequisites for the joiner question (I9): a validator reasoning
inside a truncation needs *its* schedule to be fair and spanning, not
merely the original's.

Both proofs are pure arithmetic over `Slots.chop`, which re-indexes
slots from a base slot `d` and rebases rounds by `−G`:

    slotRound k = S.slotRound (d + k) − G      leader k = S.leader (d + k)

Fairness is the shift alone. Shape meets the wrinkle this arc keeps
paying — truncated subtraction is faithful only above the cut — and
pays it with the base-slot condition `G ≤ S.slotRound d`, which
monotonicity carries to every slot at or above `d`. That condition is
already in `Slots.chop`'s signature for its `keyed` clause; this is a
second use of it.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {T : Finset Validator} {G d c : ℕ}

/-- Every slot at or above the base slot has its round above the cut —
the fact that makes the rebasing subtraction faithful. -/
theorem le_slotRound_add (S : Slots Validator) (hd : G ≤ S.slotRound d) (k : ℕ) :
    G ≤ S.slotRound (d + k) :=
  le_trans hd (S.mono (Nat.le_add_right d k))

/-- **I13.** Truncation preserves schedule fairness: a reliable leader
arbitrarily far out in the original schedule is one arbitrarily far out
in the re-indexed one, found by shifting the search past the base
slot. -/
theorem fairScheduleOn_chop (S : Slots Validator) (hd : G ≤ S.slotRound d)
    (h : FairScheduleOn (S := S) T) :
    FairScheduleOn (S := S.chop G d hd) T := by
  intro k
  obtain ⟨m, hm, hlead⟩ := h (d + k)
  refine ⟨m - d, by omega, ?_⟩
  rw [Slots.chop_leader]
  have : d + (m - d) = m := by omega
  rw [this]
  exact hlead

/-- **I13, run form.** The same for runs of `c` consecutive
reliable-led slots, which is what the liveness capstones consume. -/
theorem fairRunOn_chop (S : Slots Validator) (hd : G ≤ S.slotRound d)
    (h : FairRunOn (S := S) T c) :
    FairRunOn (S := S.chop G d hd) T c := by
  intro k
  obtain ⟨m, hm, hrun⟩ := h (d + k)
  refine ⟨m - d, by omega, ?_⟩
  intro i hi
  rw [Slots.chop_leader]
  have : d + (m - d + i) = m + i := by omega
  rw [this]
  exact hrun i hi

/-- **I15.** Truncation preserves the spanning property. Eligibility is
a statement about rounds, which the truncation rebases by `−G`; the
base-slot condition keeps every round in play above the cut, where the
subtraction is faithful and the original inequality transfers. -/
theorem spansEligible_chop (S : Slots Validator) (hd : G ≤ S.slotRound d)
    (h : SpansEligible (Validator := Validator) (S := S) c) :
    SpansEligible (Validator := Validator) (S := S.chop G d hd) c := by
  intro b i hi
  -- the original spanning fact, at the shifted indices
  have horig := h (d + b) (d + i) (by omega)
  rw [eligible_iff (S := S)] at horig
  rw [eligible_iff (S := S.chop G d hd)]
  simp only [Slots.chop_slotRound]
  -- both rounds sit above the cut
  have hlow := le_slotRound_add S hd i
  have hhigh := le_slotRound_add S hd (b + c - 1)
  -- and the two index arithmetics agree, since `i < b` forces `b ≥ 1`
  have hidx : d + b + c - 1 = d + (b + c - 1) := by omega
  rw [hidx] at horig
  omega

end Integration

end LeanDag
