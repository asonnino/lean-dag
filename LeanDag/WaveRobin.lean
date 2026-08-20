import LeanDag.Schedule
import LeanDag.Liveness

/-!
# The wave-aligned rotation — fairness as a theorem

`FairRunOn` and `SpansEligible` are stated hypotheses: `Slots.leader` is
arbitrary and could name Byzantine validators for ever, so no fairness fact
can be a theorem about schedules in general. What *can* be a theorem is that
some schedule satisfies them — otherwise L10 is a bound on nothing. Until now
that was shown only on pinned committees (`pipeSlots` over `Fin 4`,
`nemoSlots` over `Fin 3`); the general-`f` pigeonhole for per-slot rotation
lives in `FairRunOn`'s docstring as prose, unproved.

This file discharges both hypotheses at every `n` and every fault
configuration, with no premise beyond the fault model. The trick is not to
prove the pigeonhole but to sidestep it: `waveRobin` rotates by **waves**,
the leader holding for three consecutive pipelined slots before the rotation
advances. One correct leader's wave is then a full correct 3-run all by
itself, it recurs every cycle, and the fault bound always supplies a correct
validator — so `FairRunOn Correct 3` needs nothing but `Correct.Nonempty`.
Per-slot rotation would instead need the arc-counting argument of
`FairRunOn`'s docstring, which is sound at `3f + 1` but strictly harder, and
fails outright under fault models that admit more faults (the hybrid bound).

One fair schedule is all satisfiability needs: the liveness theorems
quantify over every `Slots` instance, so any other fair schedule inherits
them. Leader election in a deployment remains a separate, pluggable concern.
See `pipelining-and-multi-leader.md` for the schedule generalisation this
instantiates.
-/

namespace LeanDag

/-- **The wave-aligned round-robin schedule** on `n` validators: pipelined
(one slot per round), with the leader holding for a whole wave — three
consecutive slots — before the rotation advances.

Built from `Slots.uniformSingle` rather than by hand, so the class fields
need no new proofs; only the electorate function is new. A `def` rather than an
`instance`, like `rrSlots` in the witness files: a second `Slots` instance
on the same type would make synthesis ambiguous, so every use passes
`(S := waveRobin n hn)` explicitly. -/
@[reducible]
def waveRobin (n : ℕ) (hn : 0 < n) : Slots (Fin n) :=
  Slots.uniformSingle 1 Nat.one_pos (fun k => ⟨k / 3 % n, Nat.mod_lt _ hn⟩)

/-- The schedule is pipelined: slot `k` is proposed at round `k`. -/
@[simp]
theorem waveRobin_slotRound {n : ℕ} {hn : 0 < n} (k : ℕ) :
    (waveRobin n hn).slotRound k = k := by
  simp

/-- The leader holds for a wave: slots `3v, 3v+1, 3v+2` of each rotation
cycle are led by validator `v`. -/
theorem waveRobin_leader_val {n : ℕ} {hn : 0 < n} (k : ℕ) :
    ((waveRobin n hn).leader k).val = k / 3 % n := rfl

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]

/-- The correct pool is nonempty — at least `2 F.f + 1 ≥ 1` members. All the
fault model contributes to wave-aligned fairness: one correct validator is
one recurring correct wave. -/
theorem correct_nonempty : (Correct : Finset Validator).Nonempty :=
  Finset.card_pos.mp (by
    have := two_f_add_one_le_card_correct (Validator := Validator)
    omega)

/-- **A fair schedule exists — wave-aligned rotation, unconditionally.**

The witness for slot `k` is the correct validator `v`'s wave in the `k`-th
rotation cycle: slot `3 * (v + n * k)` opens a wave led by `v`, lies past
`k`, and its three slots are all `v`-led. This is `FairRunOn` produced with
no premise at all, where per-slot rotation would need the pigeonhole
argument recorded on `FairRunOn` — which is exactly why the wave-aligned
schedule is the canonical witness. -/
theorem waveRobin_fairRun (n : ℕ) (hn : 0 < n) [F : Faults (Fin n)] :
    FairRunOn (S := waveRobin n hn) (Correct : Finset (Fin n)) 3 := by
  intro k
  obtain ⟨v, hv⟩ := correct_nonempty (Validator := Fin n)
  refine ⟨3 * (v.val + n * k), ?_, ?_⟩
  · have hk : k ≤ n * k := Nat.le_mul_of_pos_left k hn
    omega
  · intro i hi
    have hleader : (waveRobin n hn).leader (3 * (v.val + n * k) + i) = v := by
      apply Fin.ext
      rw [waveRobin_leader_val, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hi,
        Nat.add_zero, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt v.isLt]
    rw [hleader]
    exact hv

/-- **`SpansEligible 3`, the pipelined shape, at every `n`.** A run of three
consecutive slots reaches three rounds past everything below it — the same
arithmetic as `pipe_spansEligible`, freed of the committee. -/
theorem waveRobin_spansEligible (n : ℕ) (hn : 0 < n) :
    SpansEligible (Validator := Fin n) (S := waveRobin n hn) 3 := by
  intro b i hi
  simp only [eligible_iff, waveRobin_slotRound]
  omega

/-- The wave-aligned rotation is fair in the single-slot sense too, so L6 and
the `ViewPace` results apply to it unchanged. -/
theorem waveRobin_fairSchedule (n : ℕ) (hn : 0 < n) [F : Faults (Fin n)] :
    FairScheduleOn (S := waveRobin n hn) (Correct : Finset (Fin n)) :=
  FairRunOn.fairScheduleOn (S := waveRobin n hn) (by omega) (waveRobin_fairRun n hn)

end LeanDag
