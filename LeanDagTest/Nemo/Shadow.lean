import LeanDag.Nemo.Liveness
import LeanDag.Common.Schedule

/-!
# Nemo-Nemo: commits at alternate rounds decide no slot between them

Three validators, validator `2` crashed before round 0. The schedule puts
validator `0` at every even round and validator `2` at every odd round, so
the even slots commit directly and the odd slots have no candidate. Each odd
slot `k` can be skipped only from an anchor above `k + 1`; the nearest one
is even, so the odd slot `k + 2` lies between and must be skipped first. At
the top of the DAG there is no anchor, so no odd slot is ever decided. The
schedule has no two consecutive live leaders, which is the `FairRunOn _ 2`
hypothesis of `Nemo.all_decided_below_of_fairRun` failing.
-/

namespace LeanDagTest

namespace NemoShadow

open LeanDag LeanDag.Nemo

/-- Blocks `2r` and `2r + 1` are the round-`r` blocks of validators `0` and
`1`, each referencing both blocks of round `r − 1`; rounds `0` to `6`. -/
def shBlk : Fin 14 → Block (Fin 3) (Fin 14) Unit := fun i =>
  { round := (i : ℕ) / 2,
    creator := ⟨(i : ℕ) % 2, by omega⟩,
    refs := if (i : ℕ) < 2 then ∅ else
      {⟨2 * ((i : ℕ) / 2 - 1), by omega⟩, ⟨2 * ((i : ℕ) / 2 - 1) + 1, by omega⟩},
    payload := () }

def Ush : Nemo.Universe (Fin 3) (Fin 14) Unit where
  ids := Finset.univ
  block := shBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

/-- One slot per round: validator `0` at even rounds, the crashed validator
`2` at odd rounds. -/
instance shSlots : Slots (Fin 3) :=
  Slots.uniformSingle 1 (by omega) (fun k => if k % 2 = 0 then 0 else 2)

@[simp] theorem shSlots_slotRound (k : ℕ) : shSlots.slotRound k = k := by simp

theorem shSlots_leader (k : ℕ) : shSlots.leader k = if k % 2 = 0 then 0 else 2 := rfl

/-- The even slots commit directly. -/
theorem sh_slot0 : Decided Ush (View.full Ush) 0 (some 0) :=
  Decided.directCommit (by decide) (by decide)

theorem sh_slot2 : Decided Ush (View.full Ush) 2 (some 4) :=
  Decided.directCommit (by decide) (by decide)

theorem sh_slot4 : Decided Ush (View.full Ush) 4 (some 8) :=
  Decided.directCommit (by decide) (by decide)

private theorem creator_ne_two : ∀ b : Fin 14, (Ush.block b).creator ≠ 2 := by decide

private theorem round_le_six : ∀ b : Fin 14, (Ush.block b).round ≤ 6 := by decide

/-- A slot with a candidate is even and at most `6`. -/
private theorem of_leaderBlock {k : ℕ} {L : Fin 14} (h : IsLeaderBlock Ush k L) :
    k % 2 = 0 ∧ k ≤ 6 := by
  obtain ⟨_, hr, hc⟩ := h
  rw [shSlots_slotRound] at hr
  refine ⟨?_, hr ▸ round_le_six L⟩
  by_contra hk
  rw [shSlots_leader, if_neg hk] at hc
  exact creator_ne_two L hc

/-- **No odd slot is decided**, in any view: a skip of slot `k` needs the
odd slot `k + 2` skipped first, and above round `6` there is no anchor. -/
theorem odd_undecided (V : View (Fin 3) (Fin 14) Unit Ush) (k : ℕ) (hk : k % 2 = 1)
    (v : Option (Fin 14)) : ¬ Decided Ush V k v := by
  intro h
  cases h with
  | directCommit hL _ => exact absurd (of_leaderBlock hL).1 (by omega)
  | directSkip h => exact h
  | indirectCommit _ _ _ _ _ _ hL _ _ => exact absurd (of_leaderBlock hL).1 (by omega)
  | @indirectSkip _ j _ hkj helig hj hmid _ =>
    have hA := (of_leaderBlock (AnchoredRule.isLeaderBlock_of_decided hj))
    rw [AnchoredRule.eligible_iff] at helig
    simp only [shSlots_slotRound, nemoAnchored_waveAt] at helig
    have hmid' := hmid (k + 2) (by omega) (by omega)
      (by rw [AnchoredRule.eligible_iff]; simp)
    exact odd_undecided V (k + 2) (by omega) none hmid'
termination_by 7 - k
decreasing_by omega

/-- The schedule never names two live leaders in a row. -/
theorem sh_not_fairRun : ¬ FairRunOn (S := shSlots) ({0, 1} : Finset (Fin 3)) 2 := by
  intro h
  obtain ⟨k', _, hk'⟩ := h 0
  have h0 := hk' 0 (by omega)
  have h1 := hk' 1 (by omega)
  rw [shSlots_leader] at h0 h1
  rcases Nat.mod_two_eq_zero_or_one k' with he | ho
  · rw [if_neg (by omega)] at h1
    exact absurd h1 (by decide)
  · rw [Nat.add_zero, if_neg (by omega)] at h0
    exact absurd h0 (by decide)

#print axioms odd_undecided
#print axioms sh_not_fairRun

end NemoShadow

end LeanDagTest
