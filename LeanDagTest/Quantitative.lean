import LeanDag.Quantitative
import LeanDagTest.Growth

/-!
# Quantitative liveness — the witnesses

`LeanDag/Quantitative.lean` adds three rated hypotheses. A rated hypothesis is
strictly stronger than the one it replaces, so the standing risk is that it is
strong enough to be **unsatisfiable** — in which case the bounds it buys are
bounds on nothing. That is how the horizon bug was found in `Live` and again in
`Timing`, so each of the three gets a witness here.

- `Rated` — `ugrowTiming`'s `2 ^ n` backoff qualifies, and it drives `R` down
  to an explicit `0`.
- `FairWithin` — needs a genuine **round-robin** schedule, which `fairSlots`
  (constant leader `1`) is not. `rrSlots` supplies one, and the window comes
  out at `f + 1 = 2`, matching the general bound.
- `BoundedSpacing` — `rrSlots` again, at `s = 3`.

`rrSlots` is a plain `def` rather than an `instance`: `Growth` already declares
`fairSlots : Slots (Fin 4)`, and a second instance on the same type would make
resolution ambiguous. Every use below passes `(S := rrSlots)` explicitly.
-/

namespace LeanDagTest

open LeanDag

/-! ## Part 1 — the rated backoff

`ugrowTiming` builds at `2 ^ n` with a timeout of `2 ^ n`. That is already
monotone and unbounded, which is what `exists_synchronisedOn_of_backoff` asks;
it is also **rated**, which is what pins `R`. -/

/-- `2 ^ n` outruns the round index, so the lockstep witness is rated. -/
theorem ugrowTiming_rated (N : ℕ) : Rated (ugrowTiming N).timeout :=
  fun _ => Nat.le_of_lt Nat.lt_two_pow_self

/-- **Q3 applied.** Coverage from an **explicit** round rather than from an
existential — and with no `Monotone` hypothesis anywhere.

Here `delay = 0`, `gst = 0` and the execution is lockstep so `D = 0`, which
collapses `max (max (D + delay) n₀) gst` to `0`. The point is not that the
number is small but that there *is* a number: the same theorem against
`ugrowSkew`'s constants would read `max (max 4 n₀) 0`. -/
theorem ugrow_synchronisedOn_of_rate (N : ℕ) :
    SynchronisedOn (Ugrow N) {1, 2, 3} 0 := by
  have h := synchronisedOn_of_rate (D := 0) (n₀ := 0) (ugrowTiming N) (by decide)
    (ugrowTiming_rated N) (le_refl _) (fun _ _ _ _ => le_refl _)
  simpa [ugrowTiming] using h

/-! ## Part 2 — the round-robin schedule

`fairSlots` names validator `1` at every slot, so it satisfies `FairWithin T 1`
trivially and exercises nothing. A real rotation is what makes the window
`f + 1` meaningful: at `f = 1` the single Byzantine validator `0` takes one slot
in four, so a `T`-leader is at most one slot away — never two. -/

/-- Round-robin over all four validators, slots every three rounds. -/
@[reducible] def rrSlots : Slots (Fin 4) where
  slotRound k := 3 * k
  leader k := ⟨k % 4, by omega⟩
  spacing _ := by omega

@[simp] theorem rrSlots_slotRound (k : ℕ) : rrSlots.slotRound k = 3 * k := rfl

theorem rrSlots_leader_val (k : ℕ) : (rrSlots.leader k).val = k % 4 := rfl

/-- Anything but validator `0` lies in the correct quorum. -/
theorem mem_T_of_val_ne {v : Fin 4} (h : v.val ≠ 0) :
    v ∈ ({1, 2, 3} : Finset (Fin 4)) := by
  fin_cases v <;> simp_all

/-- **The window is `f + 1 = 2`.** Validator `0` is the only non-`T` leader and
it recurs every four slots, so from any slot a `T`-leader is at most one step
away.

Tight in the sense the general statement predicts: at `f = 1` a run of `f = 1`
consecutive non-`T` leaders is possible, so the window cannot be `1`. -/
theorem rrSlots_fairWithin : FairWithin (S := rrSlots) ({1, 2, 3} : Finset (Fin 4)) 2 := by
  intro k
  by_cases h0 : k % 4 = 0
  · exact ⟨k + 1, by omega, by omega,
      mem_T_of_val_ne (by rw [rrSlots_leader_val]; omega)⟩
  · exact ⟨k, le_refl k, by omega,
      mem_T_of_val_ne (by rw [rrSlots_leader_val]; omega)⟩

/-- And it is fair in the unrated sense too, so L6 applies unchanged. -/
theorem rrSlots_fairSchedule : FairScheduleOn (S := rrSlots) ({1, 2, 3} : Finset (Fin 4)) :=
  FairWithin.fairScheduleOn (S := rrSlots) rrSlots_fairWithin

/-- Slots are exactly three rounds apart, so `s = 3` — and `Slots.spacing`
already forces `3 ≤ s`, making this the tightest legal value. -/
theorem rrSlots_boundedSpacing : BoundedSpacing (Validator := Fin 4) (S := rrSlots) 3 :=
  fun _ => by simp only [rrSlots_slotRound]; omega

/-! ## Both halves together

With `R = 0` from Part 1 and `w = 2`, `s = 3` from Part 2, the abstract bound
`slotRound (max k R) + s * w + 2` becomes the concrete horizon `3 * k + 8`. -/

/-- **Q4 applied.** For every slot `k` there is a committing slot `k'` at or
after it whose round is at most `3 * k + 6`, and every `Ugrow` grown to
`3 * k + 8` commits it.

Compare `ugrow_commits_recur`, which produces a `k'` and a horizon with no
bound on either. Both halves are in play: the synchrony round comes from
Part 1, the slot and round bounds from Part 2. -/
theorem ugrow_commits_by_round (k : ℕ) :
    ∃ k', k ≤ k' ∧ rrSlots.slotRound k' ≤ 3 * k + 6 ∧
      ∀ N, 3 * k + 8 ≤ N →
        ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) k' L ∧
          Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) k' (some L) := by
  obtain ⟨k', hk, hround, _, hcommit⟩ :=
    commits_recur_by_round (S := rrSlots) (BlockId := ℕ) (Payload := Unit)
      (T := {1, 2, 3}) (by decide) (by decide) rrSlots_fairWithin
      rrSlots_boundedSpacing 0 k
  simp only [rrSlots_slotRound] at hround
  refine ⟨k', hk, by simp only [rrSlots_slotRound]; omega, ?_⟩
  intro N hN
  exact hcommit (Ugrow N) (ugrowDelivery N) N (ugrow_live N) (ugrow_deliversQuorum N)
    (ugrow_synchronisedOn_of_rate N)
    (by simp only [rrSlots_slotRound]; omega)

-- Concretely: from slot 4, some slot at round ≤ 18 commits once the DAG
-- reaches round 20.
example : ∃ k', 4 ≤ k' ∧ rrSlots.slotRound k' ≤ 18 ∧
    ∀ N, 20 ≤ N → ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) k' L ∧
      Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) k' (some L) :=
  ugrow_commits_by_round 4

#print axioms ugrowTiming_rated
#print axioms ugrow_synchronisedOn_of_rate
#print axioms rrSlots_fairWithin
#print axioms rrSlots_boundedSpacing
#print axioms ugrow_commits_by_round

end LeanDagTest
