import LeanDagTest.Growth

/-!
# Partial views — the non-degenerate witnesses

`liveness.md` §8 Q5. `Ugrow` and `ugrowTiming` show the liveness definitions
are *satisfiable*, but they satisfy them in the easiest possible way:

- `ugrowDelivery` sets `held v n` to **every** round-`n` block, so the
  delivery hop added by S2 never meets a genuinely partial view;
- `ugrowTiming` has `delay = 0` and zero drift, so S6's two-case induction
  only ever takes the **timeout-limited** branch.

Partial views are the normal case, not the exception, and a branch no witness
reaches is a branch where a mistake would hide. This file supplies both
missing cases over the same `Ugrow N` universe.
-/

namespace LeanDagTest

open LeanDag

/-! ## Rounds above the horizon are empty

Needed to discharge `DeliversQuorum`'s hypothesis, which is stated for every
`n` while `Ugrow N` only reaches `N`. -/

theorem ugrow_blocksAt_eq_empty {N n : ℕ} (h : N < n) : blocksAt (Ugrow N) n = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  rw [mem_blocksAt] at hi
  obtain ⟨him, hir⟩ := hi
  simp only [ugrow_ids, Finset.mem_range] at him
  simp only [ugrow_block, growBlock_round] at hir
  omega

theorem ugrow_le_of_authorsAt {N n : ℕ} (h : 0 < (authorsAt (Ugrow N) n).card) :
    n ≤ N := by
  by_contra hc
  rw [authorsAt, ugrow_blocksAt_eq_empty (by omega)] at h
  simp [creatorsOf] at h

/-! ## A genuinely partial view

The Byzantine validator (`0`) withholds, so correct validators hold only the
three correct blocks of each round — a strict subset, and exactly the quorum.

This is the case §3(b) and S5 are about: withholding is free for the
adversary, so no argument may count on Byzantine-authored blocks arriving. -/

/-- What a correct validator holds when validator `0` publishes nothing. -/
def ugrowHonest (N : ℕ) : Delivery (Ugrow N) where
  held _ n := (blocksAt (Ugrow N) n).filter (fun i => ¬ (4 ∣ i))
  held_spec _ _ i hi := mem_blocksAt.mp (Finset.mem_filter.mp hi).1
  includes := by
    intro _ _ n b _ _ hbr i hi
    obtain ⟨hi, _⟩ := Finset.mem_filter.mp hi
    rw [mem_blocksAt] at hi
    simp only [ugrow_block, growBlock_round] at hbr hi
    simp only [ugrow_block, mem_growBlock_refs]
    omega

/-- **The view really is partial.** Validator `0`'s round-`n` block exists in
the universe but is held by nobody. -/
theorem ugrowHonest_partial (N n : ℕ) (hn : n ≤ N) (v : Fin 4) :
    4 * n ∈ blocksAt (Ugrow N) n ∧ 4 * n ∉ (ugrowHonest N).held v n := by
  constructor
  · rw [mem_blocksAt]
    simp only [ugrow_ids, Finset.mem_range, ugrow_block, growBlock_round]
    omega
  · intro h
    obtain ⟨_, hdvd⟩ := Finset.mem_filter.mp h
    exact hdvd ⟨n, by ring⟩

/-- And it is still a quorum: the three correct authors remain. -/
theorem ugrowHonest_deliversQuorum (N : ℕ) : DeliversQuorum (ugrowHonest N) := by
  intro n hn v _
  have hnN : n ≤ N := ugrow_le_of_authorsAt (by omega)
  refine le_trans (by decide : 2 * Faults.f (Fin 4) + 1 ≤ ({1, 2, 3} : Finset (Fin 4)).card)
    (Finset.card_le_card ?_)
  intro x hx
  rw [mem_creatorsOf]
  refine ⟨4 * n + (x : ℕ), ?_, ?_⟩
  · have hx3 : (x : ℕ) = 1 ∨ (x : ℕ) = 2 ∨ (x : ℕ) = 3 := by fin_cases hx <;> simp
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [mem_blocksAt]
      simp only [ugrow_ids, Finset.mem_range, ugrow_block, growBlock_round]
      omega
    · rintro ⟨c, hc⟩
      omega
  · have := x.isLt
    apply Fin.ext
    simp only [ugrow_block, growBlock_creator_val]
    omega

/-! ## Nonzero drift and delay

`ugrowTiming` builds every block at `2 ^ n`, so all validators move in
lockstep and S6's delivery-limited branch is unreachable. Here validator `v`
builds at `v + 4n`, so `T = {1,2,3}` is spread across **drift 2**, with
`delay = 2` against a `timeout` of `4`.

Those constants are forced, and the pair of constraints is worth seeing:

- `synchronisedOn_of_timing` needs `D + delay ≤ timeout`, so `timeout ≥ 4`;
- the delivery-limited branch fires for `w` only when
  `built w n + timeout ≤ latest n + delay`, i.e. `w + timeout ≤ 3 + delay`,
  so for `w = 1` it needs `timeout ≤ 4`.

At `timeout = 4` both hold with equality. For `w = 1` the bound comes from
**delivery** (`4n+5` against `4n+5`), and for `w = 3` from the **timeout**
(`4n+7` against `4n+5`) — so both branches of `driftFrom_of_prompt` are
live. A first attempt used `timeout = 3` and failed the first constraint,
which is exactly the check a degenerate witness cannot perform. -/

/-- Membership in `T` pins the validator index, which is what the arithmetic
below needs. -/
theorem mem_T_bounds {v : Fin 4} (hv : v ∈ ({1, 2, 3} : Finset (Fin 4))) :
    1 ≤ (v : ℕ) ∧ (v : ℕ) ≤ 3 := by fin_cases hv <;> exact ⟨by decide, by decide⟩

def ugrowSkew (N : ℕ) : Timing (Ugrow N) {1, 2, 3} N where
  blk v n := 4 * n + (v : ℕ)
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 0
  delay := 2
  rounds_le b hb := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, growBlock_round]
    omega
  blk_mem v _ n hn := by
    have := v.isLt
    simp only [ugrow_ids, Finset.mem_range]
    omega
  blk_creator v _ n _ := by
    have := v.isLt
    apply Fin.ext
    simp only [ugrow_block, growBlock_creator_val]
    omega
  blk_round v _ n _ := by
    have := v.isLt
    simp only [ugrow_block, growBlock_round]
    omega
  waits _ _ _ _ := by omega
  timeout_pos _ := by omega
  covers v _ w _ n _ _ _ := by
    have hv := v.isLt
    have hw := w.isLt
    simp only [ugrow_block, mem_growBlock_refs]
    omega
  latest n := 3 + 4 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  latest_mem _ _ := ⟨3, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _

/-- **Drift is genuinely nonzero** — validators 1 and 3 are two apart at every
round, so the bound `2` is tight rather than slack. -/
theorem ugrowSkew_drift_tight (N n : ℕ) :
    (ugrowSkew N).built 1 n + 2 = (ugrowSkew N).built 3 n := by
  have h1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  change ((1 : Fin 4) : ℕ) + 4 * n + 2 = ((3 : Fin 4) : ℕ) + 4 * n
  omega

/-- **S6 applied, with both branches live.** Drift is derived from the round-0
spread rather than assumed, and `delay ≤ timeout` is the only condition. -/
theorem ugrowSkew_drift (N : ℕ) : (ugrowSkew N).DriftFrom 0 2 :=
  Timing.driftFrom_of_prompt
    (fun v hv w hw => by
      have h1 := mem_T_bounds hv
      have h2 := mem_T_bounds hw
      change (w : ℕ) + 4 * 0 ≤ (v : ℕ) + 4 * 0 + 2
      omega)
    (fun _ _ => (by omega : (2 : ℕ) ≤ 4))

/-- **Q1/S6 on a skewed execution.** Coverage still holds, now with a real
delay and a real spread between validators. -/
theorem ugrowSkew_synchronised (N : ℕ) : SynchronisedOn (Ugrow N) {1, 2, 3} 0 :=
  Timing.synchronisedOn_of_timing (by decide) (ugrowSkew_drift N) (le_refl _)
    (fun _ _ => (by omega : 2 + (2 : ℕ) ≤ 4))

/-- Which feeds L4 exactly as the lockstep witness did. -/
example (N k : ℕ) (h : 3 * k + 2 ≤ N) :
    ∃ L, IsLeaderBlock (Ugrow N) k L ∧
      DirectCommit (Ugrow N) L (fairSlots.slotRound k) :=
  directCommit_of_leader_mem (T := {1, 2, 3}) (R := 0) (by decide)
    (ugrowSkew_synchronised N) (Nat.zero_le _)
    (PopulatedOn.mono (by decide)
      (no_stall (ugrow_live N) (ugrow_deliversQuorum N) _
        (by simp only [fairSlots_slotRound]; omega)))
    (PopulatedOn.mono (by decide)
      (no_stall (ugrow_live N) (ugrow_deliversQuorum N) _
        (by simp only [fairSlots_slotRound]; omega)))
    (PopulatedOn.mono (by decide)
      (no_stall (ugrow_live N) (ugrow_deliversQuorum N) _
        (by simp only [fairSlots_slotRound]; omega)))
    (by simp only [fairSlots_leader]; decide)

#print axioms ugrowHonest_deliversQuorum
#print axioms ugrowHonest_partial
#print axioms ugrowSkew_drift
#print axioms ugrowSkew_synchronised

end LeanDagTest
