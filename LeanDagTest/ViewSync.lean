import LeanDag.ViewSync
import LeanDagTest.Partial
import LeanDagTest.Quantitative
import LeanDag.Network.Quorum

/-!
# View convergence, witnessed

`ugrowSkewView` is `ugrowSkew` (`LeanDagTest/Partial.lean`) with its
`covers` field replaced by the two clauses that field conflates: a
view-level network guarantee and the protocol's referencing rule. The
holdings function is the honest one for that model — validator `v` holds
every block whose author built it at least `delay = 2` before time `t` —
so `converges` is a statement about *views* with no mention of references,
and `references` is a statement about *blocks* with no mention of the
network.

The point of the witness is that the split is satisfiable at the same
constants: drift `2`, `delay = 2`, `timeout = 4`, all tight
(`ugrowSkew_drift_tight`). Reference coverage then comes out through
`ViewSync.toTiming`, so nothing downstream is re-proved.
-/

namespace LeanDagTest

open LeanDag

/-- What `v` holds at time `t`. In this model the block `b` sits at round
`b / 4` with author `b % 4` and is built at time `(b % 4) + 4 * (b / 4)`,
which is `b` itself — so "built at least `delay` ago" is `b + 2 ≤ t`, and
a validator's own block is in hand the moment it is built, `b ≤ t`. Both
disjuncts are needed: the first is what `converges` moves between
validators, the second is what `holds_own` supplies. -/
def skewHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    b + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ b ≤ t)

/-- The view-level witness: `ugrowSkew` with `covers` split into
`converges` (network) and `references` (protocol). -/
def ugrowSkewView (N : ℕ) : ViewSync (Ugrow N) {1, 2, 3} N where
  blk v n := 4 * n + (v : ℕ)
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 0
  delay := 2
  rounds_le := (ugrowSkew N).rounds_le
  blk_mem := (ugrowSkew N).blk_mem
  blk_creator := (ugrowSkew N).blk_creator
  blk_round := (ugrowSkew N).blk_round
  waits _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 4 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  latest_mem _ _ := ⟨3, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _
  holds := skewHolds N
  holds_own v hv n hn := by
    have hv4 := v.isLt
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, Or.inr ⟨?_, by omega⟩⟩
    omega
  holds_mono v s t hst := by
    intro b hb
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t _ := by
    intro b hb
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, Or.inl (by omega)⟩
  references v hv n hn a ha har := by
    have hv4 := v.isLt
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [ugrow_block, rrBlock_round] at har
    simp only [ugrow_block, mem_growBlock_refs]
    omega

/-- **Reference coverage, from view convergence.** The witness satisfies
the view-level assumption, and `SynchronisedOn` follows — the derivation
of §6.8 with its network premise stated over views rather than over
references. -/
theorem ugrowSkewView_synchronised (N : ℕ) :
    SynchronisedOn (Ugrow N) {1, 2, 3} 0 :=
  (ugrowSkewView N).synchronisedOn_of_converges (by decide) (D := 2)
    (fun v hv w hw n _ _ => by
      obtain ⟨_, _⟩ := mem_T_bounds hv
      obtain ⟨_, _⟩ := mem_T_bounds hw
      show (w : ℕ) + 4 * n ≤ ((v : ℕ) + 4 * n) + 2
      omega)
    (le_refl 0) (fun n _ => by show 2 + 2 ≤ 4; omega)

/-- The reduction is definitional on the timing data, so every quantitative
result of `Timing.lean` reads off the view-level witness unchanged. -/
example (N : ℕ) : (ugrowSkewView N).toTiming.delay = 2 := rfl
example (N : ℕ) : (ugrowSkewView N).toTiming.built 1 0 = 1 := rfl

/-! ## Liveness on the foundation, on data

`Ugrow`'s round-robin schedule commits, and the whole chain — production,
coverage, the commit — runs off the view-level structure with no
`Delivery`, no `Live` and no `DeliversQuorum` anywhere. -/

-- Production comes from the structure itself.
example (N : ℕ) (hn : 2 ≤ N) : PopulatedOn (Ugrow N) {1, 2, 3} 2 :=
  (ugrowSkewView N).populatedOn hn

/-- A `{1,2,3}`-led slot commits, from view convergence and the wait
alone. -/
example (N : ℕ) (hlead : rrSlots.leader 3 ∈ ({1, 2, 3} : Finset (Fin 4)))
    (hN : rrSlots.slotRound 3 + 2 ≤ N) :
    ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) 3 L ∧
      Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) 3 (some L) :=
  (ugrowSkewView N).decided_of_leader_of_converges (S := rrSlots) (by decide)
    (by decide) (D₀ := 2)
    (fun v hv w hw => by
      obtain ⟨_, _⟩ := mem_T_bounds hv
      obtain ⟨_, _⟩ := mem_T_bounds hw
      show (w : ℕ) + 4 * 0 ≤ ((v : ℕ) + 4 * 0) + 2
      omega)
    (fun n => by show 2 + 2 ≤ 4; omega) (Nat.zero_le _) hN hlead

/-! ## The untimed variant, witnessed

`ugrowHonest` (`LeanDagTest/Partial.lean`) holds exactly the round-`n`
blocks not authored by validator `0` — the Byzantine one — so its views
are genuinely partial, and yet they converge on correct blocks. It
therefore satisfies both untimed clauses, and populates every round with
no `DeliversQuorum` anywhere. -/

theorem ugrowHonest_viewsConverge (N : ℕ) :
    ViewsConverge (ugrowHonest N) := by
  intro v _ w _ n b hb _
  exact hb

theorem ugrowHonest_holdsOwn (N : ℕ) : HoldsOwn (ugrowHonest N) := by
  intro v hv n b hb hbc hbr
  simp only [ugrowHonest, Finset.mem_filter, mem_blocksAt]
  refine ⟨⟨hb, hbr⟩, ?_⟩
  -- `v` is correct, so `v ≠ 0`, so `b` is not a multiple of four
  have : ((Ugrow N).block b).creator = v := hbc
  simp only [ugrow_block] at this
  have hv0 : (v : ℕ) ≠ 0 := by
    have hall : ∀ x : Fin 4, x ∈ (Correct : Finset (Fin 4)) → (x : ℕ) ≠ 0 := by
      decide
    exact hall v hv
  have : b % 4 = (v : ℕ) := by
    have := congrArg (fun (x : Fin 4) => (x : ℕ)) this
    simpa using this
  omega

/-- `Live` over the partial-view delivery — the same universe, so
production is immediate. -/
theorem ugrowHonest_live (N : ℕ) : Live (Ugrow N) (ugrowHonest N) N where
  genesis := ugrow_populated (Nat.zero_le N)
  builds _ hr v hv _ := ugrow_populated hr v hv

/-- **Production with no N1**, on data: every round populated, from
untimed view convergence and nothing else about the network. -/
example (N : ℕ) : ∀ r ≤ N, Populated (Ugrow N) r :=
  populated_of_viewsConverge (ugrowHonest_live N)
    (ugrowHonest_viewsConverge N) (ugrowHonest_holdsOwn N)

/-! ## Production derived, witnessed

`ugrowSkewGrowth` is `ugrowSkewView` with `blk` deleted: it asserts no
blocks at all beyond round `0`, and instead carries the build rule. The
population of every round is then a *theorem* about it
(`ugrowSkewGrowth_populated`), and `toViewSync` recovers the structure
above — at the same constants, since none of the timing data changed.

The two generalised clauses are what make this satisfiable: `holds_own`
and `references` are discharged for an arbitrary authored block rather
than for `blk v n`, which in this model is the observation that a block's
id determines its author and round. -/

/-- Every validator has a block at every round of `Ugrow` — the fact both
`base` and `builds` need, at `T = {1,2,3}` rather than at `Correct`. -/
theorem ugrow_populatedOn {N r : ℕ} (hr : r ≤ N) :
    PopulatedOn (Ugrow N) {1, 2, 3} r :=
  rrUniverse_populatedOn _ _ _ _ _ _ hr

/-- The view-level witness with production removed. `base` covers round
`0` only; every later round is derived. -/
def ugrowSkewGrowth (N : ℕ) : ViewGrowth (Ugrow N) {1, 2, 3} 0 N where
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 0
  delay := 2
  rounds_le := (ugrowSkew N).rounds_le
  waits _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 4 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  latest_mem _ _ := ⟨3, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _
  holds := skewHolds N
  holds_sub v t := by
    intro b hb
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at hb
    simp only [ugrow_ids, Finset.mem_range]
    exact hb.1
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
  base := ugrow_populatedOn (Nat.zero_le N)
  builds v _ n _ hn _ := by
    have hv4 := v.isLt
    refine ⟨4 * (n + 1) + (v : ℕ), ?_, ?_, ?_⟩
    · simp only [ugrow_ids, Finset.mem_range]; omega
    · apply Fin.ext
      simp only [ugrow_block, rrBlock_creator_val]
      omega
    · simp only [ugrow_block, rrBlock_round]; omega

/-- The drift, backoff and quorum side conditions, at the same constants
as `ugrowSkewView`: drift `2`, `delay = 2`, `timeout = 4`. -/
theorem ugrowSkewGrowth_drift (N : ℕ) :
    DriftOn (ugrowSkewGrowth N).built {1, 2, 3} 0 2 N := by
  intro v hv w hw n _ _
  obtain ⟨_, _⟩ := mem_T_bounds hv
  obtain ⟨_, _⟩ := mem_T_bounds hw
  change (w : ℕ) + 4 * n ≤ ((v : ℕ) + 4 * n) + 2
  omega

/-- **Production, derived on data.** Every round of `Ugrow` is populated —
proved from view convergence, the waiting rule and the build rule, on a
structure that never asserts a block exists above round `0`. -/
theorem ugrowSkewGrowth_populated (N : ℕ) :
    ∀ n, 0 ≤ n → n ≤ N → PopulatedOn (Ugrow N) {1, 2, 3} n :=
  (ugrowSkewGrowth N).populatedOn (by decide) (ugrowSkewGrowth_drift N)
    (le_refl 0) (fun n _ => by change 2 + 2 ≤ 4; omega)

/-- And the reduction closes the circle: `toViewSync` yields a `ViewSync`
with the same timing data, so `ugrowSkewView`'s conclusions are available
without ever having assumed `blk`. -/
example (N : ℕ) :
    ((ugrowSkewGrowth N).toViewSync (by decide) (ugrowSkewGrowth_drift N)
      (le_refl 0) (fun n _ => by change 2 + 2 ≤ 4; omega)
      (fun n hn => absurd hn (by omega))).delay = 2 := rfl

/-- **L7c with nothing assumed about production** — and, since the proof no
longer routes through `toViewSync`, nothing assumed about the quorum, the
reliable set's correctness, or population below the seed round either. The
three arguments left are the network's: drift, GST, and the backoff. -/
theorem ugrowSkewGrowth_synchronised (N : ℕ) :
    SynchronisedOn (Ugrow N) {1, 2, 3} 0 :=
  (ugrowSkewGrowth N).synchronisedOn_of_converges
    (ugrowSkewGrowth_drift N) (le_refl 0) (fun n _ => by change 2 + 2 ≤ 4; omega)

/-- **The spine from the build rule, on data.** `commits_recur_via_growth`
applied to the one structure in this file that assumes no blocks exist:
production comes from `builds` and the single seed round, coverage from
`converges`, and — as in L6 — the slot is named before the horizon is chosen.

This is the counterpart of `ugrow_commits_recur`, which reaches the same
conclusion from `Live` and `DeliversQuorum`. Here N1 is absent and P8 appears
in the conditional form an implementation can execute. -/
theorem ugrowSkewGrowth_commits (k : ℕ) :
    ∃ k', k ≤ k' ∧ ∃ N L, IsLeaderBlock (Ugrow N) k' L ∧
      Decided (Ugrow N) (View.full (Ugrow N)) k' (some L) := by
  obtain ⟨k', hk', _, hcommit⟩ :=
    ViewGrowth.commits_recur_via_growth (BlockId := ℕ) (Payload := Unit)
      (T := ({1, 2, 3} : Finset (Fin 4))) (by decide) (by decide)
      (fun j => ⟨j, le_refl j, by simp only [fairSlots_leader]; decide⟩) 0 k
  obtain ⟨L, hL, hd⟩ :=
    hcommit (Ugrow (fairSlots.slotRound k' + 2)) _ 2 (ugrowSkewGrowth _)
      (ugrowSkewGrowth_drift _) (le_refl 0)
      (fun n _ => by change 2 + 2 ≤ 4; omega) (le_refl _)
  exact ⟨k', hk', _, L, hL, hd⟩

/-! ### The untimed condition, induced on data

`{1,2,3}` is exactly `Correct` in this model and `gst = 0`, so the witness
meets the bridge's parameters and the untimed assumption comes out as a
theorem about the delivery it induces. -/

theorem ugrow_T_eq_correct : ({1, 2, 3} : Finset (Fin 4)) = Correct := by decide

/-- The witness, retyped at `T = Correct` — the same structure, since the
two sets are equal. -/
def ugrowCorrectGrowth (N : ℕ) : ViewGrowth (Ugrow N) (Correct : Finset (Fin 4)) 0 N :=
  ugrow_T_eq_correct ▸ ugrowSkewGrowth N

/-- **`ViewsConverge`, derived from the timed structure**, on data: the
untimed route's assumption, obtained as a theorem of the timed one. -/
theorem ugrowCorrectGrowth_viewsConverge (N : ℕ) :
    ViewsConverge (ugrowCorrectGrowth N).toDelivery :=
  ViewGrowth.viewsConverge_toDelivery (D := 2) _
    (by
      intro v hv w hw n _ _
      rw [← ugrow_T_eq_correct] at hv hw
      obtain ⟨_, _⟩ := mem_T_bounds hv
      obtain ⟨_, _⟩ := mem_T_bounds hw
      change (w : ℕ) + 4 * n ≤ ((v : ℕ) + 4 * n) + 2
      omega)
    rfl (fun n => by change 2 + 2 ≤ 4; omega)

/-- **N2a, derived on data.** The delivery induced by the witness satisfies
eventual DAG synchrony from round `0` — including the topmost round, which
is what `waits` reaching past the horizon buys. -/
theorem ugrowCorrectGrowth_eventuallyDelivers (N : ℕ) :
    EventuallyDelivers (ugrowCorrectGrowth N).toDelivery 0 :=
  ViewGrowth.eventuallyDelivers_toDelivery (D := 2) _
    (by
      intro v hv w hw n _ _
      rw [← ugrow_T_eq_correct] at hv hw
      obtain ⟨_, _⟩ := mem_T_bounds hv
      obtain ⟨_, _⟩ := mem_T_bounds hw
      change (w : ℕ) + 4 * n ≤ ((v : ℕ) + 4 * n) + 2
      omega)
    (le_refl 0) (fun n _ => by change 2 + 2 ≤ 4; omega)

/-- And L7a's conclusion follows, so the delivery route of §6.7 is
available from view convergence. -/
example (N : ℕ) : Synchronised (Ugrow N) 0 :=
  ViewGrowth.synchronised_toDelivery (D := 2) (ugrowCorrectGrowth N)
    (by
      intro v hv w hw n _ _
      rw [← ugrow_T_eq_correct] at hv hw
      obtain ⟨_, _⟩ := mem_T_bounds hv
      obtain ⟨_, _⟩ := mem_T_bounds hw
      change (w : ℕ) + 4 * n ≤ ((v : ℕ) + 4 * n) + 2
      omega)
    (le_refl 0) (fun n _ => by change 2 + 2 ≤ 4; omega)

#print axioms ugrowCorrectGrowth_eventuallyDelivers
#print axioms ugrowCorrectGrowth_viewsConverge
#print axioms ugrowSkewGrowth_populated
#print axioms ugrowSkewGrowth_synchronised
#print axioms ugrowSkewGrowth_commits
#print axioms ugrowSkewView_synchronised
#print axioms LeanDag.ViewGrowth.commits_recur_via_growth
#print axioms LeanDag.ViewSync.commits_recur_of_converges
#print axioms LeanDag.ViewSync.all_decided_below_of_converges
#print axioms LeanDag.ViewSync.covers_of_converges

end LeanDagTest
