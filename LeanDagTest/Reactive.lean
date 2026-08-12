import LeanDag.Reactive.Mysticeti
import LeanDag.Reactive.Odontoceti
import LeanDagTest.Quantitative

/-!
# The reactive schedule, witnessed

A `ReactiveM` instance on `Ugrow`, at constants chosen to exhibit the
point of the reactive rule: every build happens at spacing `6`, strictly
inside the timeout `7`, so **no validator ever waits out a timeout** —
the fallback branches of `vote_or_wait` and `cert_or_wait` are never
taken, and both are discharged by their reactive exits.

`Ugrow`'s blocks reference the whole round below, so every block votes
for every leader block and every round-`(n+2)` block certifies; the
reactive exits are therefore available at every slot, which is what the
model is for. The fast-path constants are honest rather than generous:
processing `5` is the least value `prompt_vote` admits here — a
validator's shortcut to its *own* block lets the trigger fire a tick
before the slowest peer's block would force it — so `D + δ + proc = 10`
exceeds the timeout `7`, the sufficient condition of
`no_timeout_of_fast` is deliberately unmet, and its conclusion is
discharged directly by the run (`ugrowReactive_early`).
`ugrowReactive_fast` exhibits the latency theorem itself.
-/

namespace LeanDagTest

open LeanDag

-- `Growth` installs the constant-leader `fairSlots` globally; this file
-- works on the rotating schedule, so it wins synthesis here.
attribute [local instance 2000] rrSlots

/-- What `v` holds at time `t` on the `6`-spaced schedule: block `b`
(built at `b % 4 + 6 * (b / 4)`) has arrived once `delay = 2` has passed,
and a validator holds its own block from the moment it builds. -/
def reactHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    b % 4 + 6 * (b / 4) + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ b % 4 + 6 * (b / 4) ≤ t)

/-- The reactive witness: `Ugrow` on the round-robin schedule, builds at
spacing `6` inside a timeout of `7`. -/
def ugrowReactive (N : ℕ) : ReactiveM (Ugrow N) {1, 2, 3} N where
  blk v n := 4 * n + (v : ℕ)
  built v n := (v : ℕ) + 6 * n
  timeout _ := 7
  proc := 5
  gst := 0
  delay := 2
  rounds_le b hb := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
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
  built_lt _ _ _ := by omega
  deadline _ _ _ _ := by omega
  holds := reactHolds N
  holds_own v hv n _ := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range]
    have hv4 := v.isLt
    constructor
    · omega
    · right
      constructor
      · omega
      · have : (4 * n + (v : ℕ)) % 4 = (v : ℕ) := by omega
        rw [this]
        have : (4 * n + (v : ℕ)) / 4 = n := by omega
        rw [this]
  holds_mono v s t hst := by
    intro b hb
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t _ := by
    intro b hb
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨hb.1, Or.inl ?_⟩
    rcases hb.2 with h | h
    · omega
    · omega
  vote_or_wait v hv k hN _ L hL := by
    -- the reactive exit is always available: every block references the
    -- whole round below, the leader block among it
    left
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    obtain ⟨hmem, hround, -⟩ := hL
    simp only [ugrow_ids, Finset.mem_range] at hmem
    simp only [ugrow_block, rrBlock_round] at hround
    simp only [ugrow_block, mem_growBlock_refs]
    omega
  prompt_vote v hv k hN hlead L hL t hbuilt hheld hall := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    have hv4 := v.isLt
    -- the trigger includes every reliable round-`r` block; blocks `2`
    -- and `3` of the round bound `t` from below far enough for `proc = 5`
    have h2 := hall 2 (by decide)
    have h3' := hall 3 (by decide)
    simp only [reactHolds, Finset.mem_filter, Finset.mem_range] at h2 h3'
    have e2 : (4 * rrSlots.slotRound k + (2 : Fin 4).val) % 4 = 2 := by omega
    have d2 : (4 * rrSlots.slotRound k + (2 : Fin 4).val) / 4 = rrSlots.slotRound k := by
      omega
    have e3 : (4 * rrSlots.slotRound k + (3 : Fin 4).val) % 4 = 3 := by omega
    have d3 : (4 * rrSlots.slotRound k + (3 : Fin 4).val) / 4 = rrSlots.slotRound k := by
      omega
    rw [e2, d2] at h2
    rw [e3, d3] at h3'
    change (v : ℕ) + 6 * (rrSlots.slotRound k + 1) ≤ t + 5
    rcases h2.2 with ha | ⟨hb, hc⟩ <;> rcases h3'.2 with hd | ⟨he, hf⟩ <;> omega
  cert_or_wait v hv k hN _ L hL := by
    -- likewise: every round-`(r+2)` block references the whole round
    -- `(r+1)`, and every round-`(r+1)` block votes, so it certifies
    left
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    obtain ⟨hmem, hround, -⟩ := hL
    simp only [ugrow_ids, Finset.mem_range] at hmem
    simp only [ugrow_block, rrBlock_round] at hround
    show (Fintype.card (Fin 4) - Faults.f (Fin 4)) ≤ _
    have hsub : ({0, 1, 2, 3} : Finset (Fin 4)) ⊆
        creatorsOf (Ugrow N).block
          (votesIn (Ugrow N) (4 * (rrSlots.slotRound k + 2) + (v : ℕ)) L) := by
      intro x _
      have hx4 := x.isLt
      refine mem_creatorsOf.mpr ⟨4 * (rrSlots.slotRound k + 1) + (x : ℕ), ?_, ?_⟩
      · rw [votesIn, Finset.mem_filter]
        constructor
        · simp only [ugrow_block, mem_growBlock_refs]
          omega
        · simp only [ugrow_block, mem_growBlock_refs]
          omega
      · apply Fin.ext
        simp only [ugrow_block, rrBlock_creator_val]
        omega
    have hcard : ({0, 1, 2, 3} : Finset (Fin 4)).card = 4 := by decide
    have := Finset.card_le_card hsub
    have hf : Faults.f (Fin 4) = 1 := rfl
    have hn : Fintype.card (Fin 4) = 4 := rfl
    omega

/-- Drift among `{1,2,3}` at spacing `6` is `2`; `3` is a safe bound. -/
theorem ugrowReactive_drift (N : ℕ) :
    DriftOn (ugrowReactive N).built {1, 2, 3} 0 3 N := by
  intro v hv w hw n _ _
  obtain ⟨_, _⟩ := mem_T_bounds hv
  obtain ⟨_, _⟩ := mem_T_bounds hw
  change (w : ℕ) + 6 * n ≤ ((v : ℕ) + 6 * n) + 3
  omega

/-- **Reactive liveness, on data.** Slot `1` (leader `1`, reliable) is
committed by the full view, at spacing `6` with a timeout of `7` and
delivery bound `2`: `3 + 2 ≤ 7` and the fallback is sound, though this
run never uses it. -/
theorem ugrowReactive_decided (N : ℕ) (hN : rrSlots.slotRound 1 + 2 ≤ N) :
    ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) 1 L ∧
      Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) 1 (some L) :=
  (ugrowReactive N).decided (D := 3) (R := 0) (by decide) (by decide)
    (ugrowReactive_drift N) (le_refl 0)
    (fun n _ => by change 3 + 2 ≤ 7; omega)
    (Nat.zero_le _) hN (by decide)

/-- **No timeout fires, on data**: every build is strictly inside the
deadline — the conclusion of `no_timeout_of_fast`, held by this run at
every round. -/
theorem ugrowReactive_early (N : ℕ) :
    ∀ v ∈ ({1, 2, 3} : Finset (Fin 4)), ∀ n,
      (ugrowReactive N).built v (n + 1)
        < (ugrowReactive N).built v n + (ugrowReactive N).timeout n := by
  intro v _ n
  change (v : ℕ) + 6 * (n + 1) < ((v : ℕ) + 6 * n) + 7
  omega

/-- **The latency theorem, on data.** Slot `1` sits at round `3`; its
leader block is `13`. Every reliable validator builds round `4` within
`D + δ + proc = 3 + 2 + 5` of entering round `3` — the conclusion of
`built_succ_le_of_fast`, with the timeout appearing nowhere. -/
theorem ugrowReactive_fast (N : ℕ) (hN : 4 ≤ N) :
    ∀ v ∈ ({1, 2, 3} : Finset (Fin 4)),
      (ugrowReactive N).built v 4 ≤ (ugrowReactive N).built v 3 + 10 := by
  have hL : IsLeaderBlock (Ugrow N) 1 13 := by
    refine ⟨?_, ?_, ?_⟩
    · simp only [ugrow_ids, Finset.mem_range]; omega
    · simp only [ugrow_block, rrBlock_round, rrSlots_slotRound]
    · apply Fin.ext
      rw [rrSlots_leader_val]
      simp only [ugrow_block, rrBlock_creator_val]
  have h := (ugrowReactive N).built_succ_le_of_fast (k := 1) (D := 3) (δ := 2)
    (fun u hu v _ => by
      obtain ⟨h1, h3⟩ := mem_T_bounds hu
      change (4 * rrSlots.slotRound 1 + (u : ℕ)) ∈
        reactHolds N v ((u : ℕ) + 6 * rrSlots.slotRound 1 + 2)
      simp only [reactHolds, Finset.mem_filter, Finset.mem_range, rrSlots_slotRound]
      refine ⟨by omega, Or.inl ?_⟩
      have e : (4 * (3 * 1) + (u : ℕ)) % 4 = (u : ℕ) := by omega
      have d : (4 * (3 * 1) + (u : ℕ)) / 4 = 3 := by omega
      rw [e, d])
    (fun u hu v hv => by
      obtain ⟨_, _⟩ := mem_T_bounds hu
      obtain ⟨_, _⟩ := mem_T_bounds hv
      change (u : ℕ) + 6 * (3 * 1) ≤ ((v : ℕ) + 6 * (3 * 1)) + 3
      omega)
    (by simp only [rrSlots_slotRound]; omega) (by decide) hL (by decide)
  intro v hv
  have hvle := h v hv
  simp only [rrSlots_slotRound, show (ugrowReactive N).proc = 5 from rfl] at hvle
  have h34 : (3 : ℕ) * 1 + 1 = 4 := by norm_num
  have h31 : (3 : ℕ) * 1 = 3 := by norm_num
  rw [h34, h31] at hvle
  omega

#print axioms ugrowReactive_decided
#print axioms LeanDag.ReactiveM.decided
#print axioms LeanDag.Odontoceti.reactive_decided
#print axioms LeanDag.ReactiveCore.no_timeout_of_fast

end LeanDagTest
