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
name: `ugrowCatchPace` satisfies `CatchupPace` at spacing `5`, `delay 2`,
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

/-! ## The witness -/
def ugrowCatchPace (N : ℕ) : CatchupPace (Ugrow N) {1, 2, 3} N where
  top _ := N
  built v n := (v : ℕ) + 5 * n
  timeout _ := 5
  gst := 0
  delay := 2
  proc := 1
  rounds_le := (ugrowSkew N).rounds_le
  built_of_le_top v hv n hn := rrUniverse_populatedOn _ _ _ _ _ _ hn v hv
  le_top_of_built _ _ b hb _ := (ugrowSkew N).rounds_le b hb
  waits _ _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 5 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  latest_mem _ _ := ⟨3, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _
  holds := catchHolds N
  holds_own v hv n _ b hb hbc hbr := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    have hb4 : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa [ugrow_block] using this
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨hb, Or.inr ⟨hb4, by omega⟩⟩
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
  references v hv n hn c hc hcc hcr a ha har := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [ugrow_block, rrBlock_round] at har hcr
    simp only [ugrow_block, mem_growBlock_refs]
    omega
  advances _ _ _ hn _ _ := hn
  catchup v hv n hn b hb hbT hbr t hheld := by
    obtain ⟨hv1, hv3⟩ := mem_T_bounds hv
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [catchHolds, Finset.mem_filter, Finset.mem_range] at hheld
    refine ⟨hn, ?_⟩
    change (v : ℕ) + 5 * n ≤ t + 1
    have hv4 := v.isLt
    rcases hheld.2 with h | ⟨_, h⟩
    · omega
    · omega

/-- **The commit at `2Δ + proc`, production derived, no start spread.**
Nothing in the structure asserts a block above round `0`. -/
theorem ugrowCatchPace_decided (N : ℕ) (hN : rrSlots.slotRound 1 + 2 ≤ N) :
    ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) 1 L ∧
      Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) 1 (some L) :=
  (ugrowCatchPace N).decided_of_catchup (R := 0) (by decide) (by decide)
    (le_refl 0) (fun n _ => by change 2 + 1 + 2 ≤ 5; omega)
    (Nat.zero_le _) hN (by decide)

#print axioms ugrowCatchPace_decided
#print axioms LeanDag.CatchupPace.drift_collapse
#print axioms LeanDag.CatchupPace.decided_of_catchup
#print axioms ugrowSkew_spread_constant

end LeanDagTest
