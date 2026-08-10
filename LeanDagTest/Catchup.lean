import LeanDag.Drift.Catchup
import LeanDagTest.Reactive

/-!
# Catch-up, witnessed — and its absence

Two facts, one per direction.

Without the clause, drift does not contract:
`ugrowSkew_spread_constant` shows the existing timed witness carrying its
round-`0` spread unchanged at every round — `waits` and `prompt` are
satisfied, drift is *preserved* exactly as `driftFrom_of_prompt`
promises, and nothing reduces it. The intuition that spread shrinks as
the protocol reaches synchrony is refuted on data for the un-augmented
protocol.

With the clause, the collapse is real at the constants the theorems
name: `ugrowCatch` satisfies `CatchupSync` at spacing `5`, `delay 2`,
`proc 1`, and `decided_of_catchup` commits a slot at timeout `5 = 2Δ +
proc` with **no start-spread hypothesis anywhere** — where the
corresponding `decided_of_wait` invocation would demand the round-`0`
spread as its `D₀`.
-/

namespace LeanDagTest

open LeanDag

attribute [local instance 2000] rrSlots

/-- **Drift does not contract without catch-up.** The skewed witness
satisfies every clause of the timed schedule, and its spread is the
round-`0` spread at every round, for ever. -/
theorem ugrowSkew_spread_constant (N n : ℕ) :
    (ugrowSkew N).built 3 n = (ugrowSkew N).built 1 n + 2 := by
  change (3 : ℕ) + 4 * n = ((1 : ℕ) + 4 * n) + 2
  omega

/-- What `v` holds at time `t` on the `5`-spaced schedule: block `b`
(built at `b % 4 + 5 * (b / 4)`) has arrived once `delay = 2` has
passed, and one's own block is in hand at once. -/
def catchHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    b % 4 + 5 * (b / 4) + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ b % 4 + 5 * (b / 4) ≤ t)

/-- The catch-up witness: `Ugrow` at spacing `5`, timeout `5`, `delay 2`,
`proc 1`. The catch-up clause holds because a sighting of any round-`n`
block happens at earliest two ticks after the fastest build, by which
time every validator's own round-`n` build is at most one tick away. -/
def ugrowCatch (N : ℕ) : CatchupSync (Ugrow N) {1, 2, 3} N where
  blk v n := 4 * n + (v : ℕ)
  built v n := (v : ℕ) + 5 * n
  timeout _ := 5
  gst := 0
  delay := 2
  proc := 1
  rounds_le := (ugrowSkew N).rounds_le
  blk_mem v hv n hn := by
    obtain ⟨_, _⟩ := mem_T_bounds hv
    simp only [ugrow_ids, Finset.mem_range]; omega
  blk_creator v hv n _ := by
    obtain ⟨_, _⟩ := mem_T_bounds hv
    apply Fin.ext
    simp only [ugrow_block, rrBlock_creator_val]
    omega
  blk_round v hv n _ := by
    obtain ⟨_, _⟩ := mem_T_bounds hv
    simp only [ugrow_block, rrBlock_round]; omega
  waits _ _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 5 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  latest_mem _ _ := ⟨3, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _
  holds := catchHolds N
  holds_own v hv n _ := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    have hv4 := v.isLt
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, Or.inr ⟨?_, ?_⟩⟩
    · omega
    · have e : (4 * n + (v : ℕ)) % 4 = (v : ℕ) := by omega
      have d : (4 * n + (v : ℕ)) / 4 = n := by omega
      rw [e, d]
  holds_mono v s t hst := by
    intro b hb
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t _ := by
    intro b hb
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨hb.1, Or.inl ?_⟩
    rcases hb.2 with h | h
    · omega
    · omega
  references v hv n hn a ha har := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [ugrow_block, rrBlock_round] at har
    simp only [ugrow_block, mem_growBlock_refs]
    omega
  catchup v hv u hu n hn t hheld := by
    obtain ⟨hv1, hv3⟩ := mem_T_bounds hv
    obtain ⟨hu1, hu3⟩ := mem_T_bounds hu
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at hheld
    have e : (4 * n + (u : ℕ)) % 4 = (u : ℕ) := by omega
    have d : (4 * n + (u : ℕ)) / 4 = n := by omega
    rw [e, d] at hheld
    change (v : ℕ) + 5 * n ≤ t + 1
    rcases hheld.2 with h | ⟨huv, h⟩
    · omega
    · omega

/-- **The commit at `2Δ + proc`, with no start-spread hypothesis.**
Slot `1` is committed at timeout `5 = 2·2 + 1`; nothing anywhere states
how far apart the validators began. -/
theorem ugrowCatch_decided (N : ℕ) (hN : rrSlots.slotRound 1 + 2 ≤ N) :
    ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) 1 L ∧
      Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) 1 (some L) :=
  (ugrowCatch N).decided_of_catchup (R := 0) (by decide) (by decide)
    (le_refl 0) (fun n _ => by change 2 + 1 + 2 ≤ 5; omega)
    (Nat.zero_le _) hN (by decide)

/-- The collapse itself, on data: the spread bound `Δ + proc = 3` holds
at every round — and would hold whatever the round-`0` spread had been,
which is the content `ugrowSkew_spread_constant` shows `waits` and
`prompt` cannot supply. -/
example (N n : ℕ) (hn : n ≤ N) :
    ∀ v ∈ ({1, 2, 3} : Finset (Fin 4)), ∀ w ∈ ({1, 2, 3} : Finset (Fin 4)),
      (ugrowCatch N).built v n ≤ (ugrowCatch N).built w n + 3 :=
  fun v hv w hw =>
    (ugrowCatch N).drift_collapse hn (fun u _ => Nat.zero_le _) v hv w hw

#print axioms ugrowCatch_decided
#print axioms LeanDag.CatchupSync.drift_collapse
#print axioms LeanDag.CatchupSync.decided_of_catchup
#print axioms ugrowSkew_spread_constant

end LeanDagTest
