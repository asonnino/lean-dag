import LeanDag.ViewPace
import LeanDagTest.Quantitative

/-!
# The partial schedule, witnessed

Witnesses for `ViewPace`, the structure the liveness development runs on
(report §6.9, V17). Three claims are certified on data:

* **satisfiability at the running constants** — `ugrowSkewPace` is the
  familiar `Ugrow` layout at drift `2`, `delay = 2`, `timeout = 4`, with
  production *derived*: nothing in the structure asserts a block above
  round `0`;
* **liveness runs off it** — production, coverage, derived drift, the
  recurring commit, and the wait bound, each read off the same witness;
* **stuck is expressible** — `ugrowStuckPace` is satisfied by an execution
  that has genuinely halted, which is what no total build schedule can
  represent, and which is why the structure exists.
-/

namespace LeanDagTest

open LeanDag

/-- What `v` holds at time `t`. Block `b` sits at round `b / 4` with author
`b % 4` and is built at time `(b % 4) + 4 * (b / 4)`, which is `b` itself —
so "built at least `delay = 2` ago" is `b + 2 ≤ t`, and a validator's own
block is in hand the moment it is built, `b ≤ t`. -/
def skewHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    b + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ b ≤ t)

/-- Every validator has a block at every round of `Ugrow` — the layout
fact `built_of_le_top` comes down to, at `T = {1,2,3}`. -/
theorem ugrow_populatedOn {N r : ℕ} (hr : r ≤ N) :
    PopulatedOn (Ugrow N) {1, 2, 3} r :=
  rrUniverse_populatedOn _ _ _ _ _ _ hr

/-- **The witness.** `top v = N` — in this model nobody is ever stuck —
and `advances` is discharged by arithmetic. -/
def ugrowSkewPace (N : ℕ) : ViewPace (Ugrow N) {1, 2, 3} N where
  top _ := N
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 0
  delay := 2
  rounds_le b hb := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  built_of_le_top v hv n hn := ugrow_populatedOn hn v hv
  le_top_of_built _ _ b hb _ := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  waits _ _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 4 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  latest_mem _ _ := ⟨3, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _
  holds := skewHolds N
  holds_own v hv n _ b hb hbc hbr := by
    have hv4 := v.isLt
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    have hbc' : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa using this
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨hb, Or.inr ⟨hbc', by omega⟩⟩
  holds_mono v s t hst := by
    intro b hb
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t _ := by
    intro b hb
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, Or.inl (by omega)⟩
  references v hv n _ c hc _ hcr a ha har := by
    have hv4 := v.isLt
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [ugrow_ids, Finset.mem_range] at hc
    simp only [ugrow_block, rrBlock_round] at hcr har
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [ugrow_block, mem_growBlock_refs]
    omega
  advances _ _ _ hn _ _ := hn

/-- **Production**: every round populated, from genesis, view convergence
and the progress rule — no drift, no backoff, no `timeout`, and no
schedule hypothesis. -/
theorem ugrowSkewPace_populated (N : ℕ) :
    ∀ n ≤ N, PopulatedOn (Ugrow N) {1, 2, 3} n :=
  (ugrowSkewPace N).populatedOn (by decide)

/-- **Drift derived, not assumed** — `driftOn_of_prompt` at the running
constants. -/
theorem ugrowSkewPace_drift (N : ℕ) :
    DriftOn (ugrowSkewPace N).built {1, 2, 3} 0 2 N :=
  (ugrowSkewPace N).driftOn_of_prompt (by decide)
    (fun v hv w hw => by
      obtain ⟨_, _⟩ := mem_T_bounds hv
      obtain ⟨_, _⟩ := mem_T_bounds hw
      change (w : ℕ) + 4 * 0 ≤ ((v : ℕ) + 4 * 0) + 2
      omega)
    (fun n _ => by change 2 ≤ 4; omega)

/-- **Coverage**, at the same constants. -/
theorem ugrowSkewPace_synchronised (N : ℕ) :
    SynchronisedOn (Ugrow N) {1, 2, 3} 0 :=
  (ugrowSkewPace N).synchronisedOn_of_converges (D := 2)
    (ugrowSkewPace_drift N) (le_refl 0)
    (fun n _ => by change 2 + 2 ≤ 4; omega)

/-- **The spine, on data**: commits recur, with the slot named before the
horizon is chosen — and no schedule hypothesis anywhere. -/
theorem ugrowSkewPace_commits (k : ℕ) :
    ∃ k', k ≤ k' ∧ ∃ N L, IsLeaderBlock (Ugrow N) k' L ∧
      Decided (Ugrow N) (View.full (Ugrow N)) k' (some L) := by
  obtain ⟨k', hk', _, hcommit⟩ :=
    ViewPace.commits_recur_via_pace (BlockId := ℕ) (Payload := Unit)
      (T := ({1, 2, 3} : Finset (Fin 4))) (by decide) (by decide)
      (fun j => ⟨j, le_refl j, by simp only [fairSlots_leader]; decide⟩) 0 k
  obtain ⟨L, hL, hd⟩ :=
    hcommit (Ugrow (fairSlots.slotRound k' + 2)) _ 2 (ugrowSkewPace _)
      (ugrowSkewPace_drift _) (le_refl 0)
      (fun n _ => by change 2 + 2 ≤ 4; omega) (le_refl _)
  exact ⟨k', hk', _, L, hL, hd⟩

/-- **The wait bound, on data, production derived**: slot `3` committed at
the constant timeout `4 = D₀ + Δ`, from a structure asserting no blocks
above round `0`. -/
example (N : ℕ) (hlead : rrSlots.leader 3 ∈ ({1, 2, 3} : Finset (Fin 4)))
    (hN : rrSlots.slotRound 3 + 2 ≤ N) :
    ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) 3 L ∧
      Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) 3 (some L) :=
  (ugrowSkewPace N).decided_of_wait (S := rrSlots) (D₀ := 2) (by decide)
    (fun v hv w hw => by
      obtain ⟨_, _⟩ := mem_T_bounds hv
      obtain ⟨_, _⟩ := mem_T_bounds hw
      change (w : ℕ) + 4 * 0 ≤ ((v : ℕ) + 4 * 0) + 2
      omega)
    (fun n => by change 2 + 2 ≤ 4; omega) (Nat.zero_le _) hN hlead

/-- **Stuck, expressed.** A `ViewPace` in which a validator never gets past
round `0`, while the horizon is `5`.

The universe is `Ugrow 0` — round-`0` blocks and nothing above — and `T` is
the singleton `{1}`, which is *not* a quorum. `advances` is never
triggered: validator `1` holds one block, so one distinct round-`0` author,
and `1 < 3 = n - f`. Nothing forces it forward and `top 1 = 0` stands.

This is what no total schedule can say. There, `built 1 1` exists whatever
happens, so the validator has a build time for a round it never reached,
and the structure cannot distinguish *stuck at round 0* from *built round 1
with no quorum*.

Note also where the quorum bound does its work: `ViewPace.populatedOn`
would give `PopulatedOn (Ugrow 0) {1} 1` from this structure were `hcard`
dropped, and that is false, since validator `1` has no round-`1` block. -/
def ugrowStuckPace : ViewPace (Ugrow 0) {1} 5 where
  top _ := 0
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 0
  delay := 2
  rounds_le b hb := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  built_of_le_top v hv n hn :=
    PopulatedOn.mono (by decide) (ugrow_populatedOn (N := 0) hn) v hv
  le_top_of_built _ _ b hb _ := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  waits _ _ _ h := absurd h (Nat.not_lt.mpr (Nat.zero_le _))
  timeout_pos _ := by omega
  latest n := 1 + 4 * n
  built_le_latest v hv _ _ := by
    have hv1 : v = 1 := by simpa using hv
    subst hv1; omega
  latest_mem _ _ := ⟨1, by decide, le_refl _⟩
  prompt _ _ _ h := absurd h (Nat.not_lt.mpr (Nat.zero_le _))
  holds _ _ := {1}
  holds_own v hv n _ b hb hbc _ := by
    have hv1 : v = 1 := by simpa using hv
    subst hv1
    simp only [ugrow_ids, Finset.mem_range] at hb
    have hb4 : b % 4 = 1 := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa [ugrow_block] using this
    simp only [Finset.mem_singleton]
    omega
  holds_mono _ _ _ _ := Finset.Subset.refl _
  converges _ _ _ _ _ _ := Finset.Subset.refl _
  references _ _ _ _ c hc _ hcr _ _ _ := by
    simp only [ugrow_ids, Finset.mem_range] at hc
    simp only [ugrow_block, rrBlock_round] at hcr
    omega
  advances _ _ n _ _ hq := by
    exfalso
    have hle : (creatorsOf (Ugrow 0).block
        (({1} : Finset ℕ).filter fun b => ((Ugrow 0).block b).round = n)).card ≤ 1 := by
      simp only [creatorsOf]
      refine le_trans (Finset.card_le_card
        (Finset.image_subset_image (Finset.filter_subset _ _))) ?_
      exact le_trans Finset.card_image_le (by simp)
    have hq3 : Fintype.card (Fin 4) - Faults.f (Fin 4) = 3 := by decide
    omega

/-- **And it really is stuck.** The horizon is `5`, the validator's top is
`0`, and round `1` is unpopulated — the structure is satisfied by an
execution that has genuinely halted. -/
theorem ugrowStuckPace_stuck :
    ugrowStuckPace.top 1 = 0 ∧ ¬ PopulatedOn (Ugrow 0) {1} 1 := by
  refine ⟨rfl, fun h => ?_⟩
  obtain ⟨b, hb, _, hbr⟩ := h 1 (by decide)
  simp only [ugrow_ids, Finset.mem_range] at hb
  simp only [ugrow_block, rrBlock_round] at hbr
  omega

#print axioms ugrowSkewPace_populated
#print axioms ugrowSkewPace_synchronised
#print axioms ugrowSkewPace_drift
#print axioms ugrowSkewPace_commits
#print axioms ugrowStuckPace_stuck
#print axioms LeanDag.ViewPace.populatedOn
#print axioms LeanDag.ViewPace.driftOn_of_prompt
#print axioms LeanDag.ViewPace.commits_recur_via_pace
#print axioms LeanDag.ViewPace.covers_of_converges

end LeanDagTest
