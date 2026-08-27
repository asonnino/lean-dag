import LeanDag.FinWhale.Pass
import LeanDag.FinWhale.Model.Liveness
import LeanDag.ViewPace

/-!
# FinWhale — a validator's holdings are its view

`View.lean` takes a view to be any reference-closed part of the DAG, and
the liveness results ask that a validator's view hold the reliable blocks
up to the horizon. Neither is tied to a schedule: a view is a `Finset`,
and holding the blocks is a hypothesis.

This file ties both to the pacing trunk. `PaceCore.holds` is what a
validator has at a time, and its two store clauses — holdings are part of
the universe, and holdings are closed under references — are exactly what
`IsView` asks. So a validator's holdings *are* a view, at every instant,
and `restrict` turns them into a DAG the decision rules run on.

The second half is what the network gives. `PaceCore.holds_roundBlocks`
says every reliable validator's round-`n` block reaches every reliable
validator by `latest n + delay`, past GST. Taking the largest such time
below the horizon and `holds_mono` gives one instant at which the view
holds every reliable block of every round from the coverage round up —
which is the condition `all_decided_of_view` reads, and nothing more is
available: no clause of any schedule obliges a validator to hold a
Byzantine author's block.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}
variable {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator} {M : ℕ}

/-- **A validator's holdings are a view.** `holds_sub` is the subset
clause and `holds_closed` the closure clause. -/
theorem isView_holds (pc : PaceCore U T M) (hids : D.ids = U.ids) (hblk : D.block = U.block)
    {v : Validator} (hv : v ∈ T) (t : ℕ) : IsView D (pc.holds v t) :=
  ⟨by rw [hids]; exact pc.holds_sub v t, by rw [hblk, hids] at *; exact pc.holds_closed v hv t⟩

/-- **And by then the view holds every reliable block from the coverage
round up.** Byzantine authors are not covered, and no schedule covers
them: nothing obliges a validator to receive what a faulty validator
never sent. -/
theorem held_of_pace (pc : PaceCore U T M) (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hle : ∀ u ∈ T, ∀ n ≤ pc.top u, n ≤ pc.built u n)
    (hcard : quorumCard Validator ≤ T.card) {R : ℕ} (hgst : pc.gst ≤ R)
    {v : Validator} (hv : v ∈ T) :
    ∀ n, R ≤ n → n ≤ M → ∀ b ∈ blocksAt D n, (D.block b).creator ∈ T →
      b ∈ pc.holds v (settled pc) := by
  intro n hR hM b hb hbT
  simp only [blocksAt, Finset.mem_filter, hids, hblk] at hb hbT ⊢
  have hg : ∀ u ∈ T, pc.gst ≤ pc.built u n :=
    fun u hu => le_trans (le_trans hgst hR) (hle u hu n (pc.reached hcard n hM u hu))
  have harrive := pc.holds_roundBlocks hM hg v hv b hb.1 hbT hb.2
  refine pc.holds_mono v _ _ ?_ harrive
  exact Finset.le_sup (f := fun m => pc.latest m + pc.delay) (Finset.mem_range.2 (by omega))

/-! ## The capstone: a validator, with nothing about it assumed -/

variable [LinearOrder BlockId]

/-- **Every slot below the horizon is decided**, by a validator whose
view is its own holdings and whose verdicts are the reverse pass.

Nothing about the validator is a hypothesis here. Its view is
`pc.holds v` — the store clauses make that a view — its verdicts are
`decOf`, which `wellFormed_decOf` makes well formed, and what it holds is
what the network delivered. What is left is about the schedule and the
DAG: that the pace reaches the rounds (`hle`, `hcard`), that the coverage
round is past GST, that the liveness interface holds, and that the
rotation is round robin. -/
theorem all_decided_of_pass (pc : PaceCore U (Correct : Finset Validator) M)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hle : ∀ u ∈ (Correct : Finset Validator), ∀ n ≤ pc.top u, n ≤ pc.built u n)
    {R : ℕ} (hgst : pc.gst ≤ R) {v : Validator} (hv : v ∈ (Correct : Finset Validator))
    {choose : BlockId → ℕ → Option BlockId} {Np N r : ℕ}
    (hhorizon : ∀ b ∈ pc.holds v (settled pc), (D.block b).round ≤ Np)
    (hcommits : CommitsCorrectLeaders D R N) (hrr : RoundRobin D.leader)
    (hNM : N ≤ M) (hN : max r R + (3 * F.f + 5) ≤ N) :
    decOf (restrict D (pc.holds v (settled pc)) (isView_holds pc hids hblk hv (settled pc)))
      choose Np r ≠ Verdict.undecided :=
  all_decided_of_view (isView_holds pc hids hblk hv (settled pc))
    (wellFormed_decOf hhorizon choose)
    (fun n hRn hnN b hb hbc =>
      held_of_pace pc hids hblk hle card_correct hgst hv n hRn (by omega) b hb hbc)
    hcommits hrr hN

end FinWhale

end LeanDag
