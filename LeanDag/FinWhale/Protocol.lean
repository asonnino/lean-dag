import LeanDag.FinWhale.Holdings
import LeanDag.FinWhale.Model.Protocol
import LeanDag.FinWhale.Validity

/-!
# FinWhale — what the protocol guarantees

The results below this file are stated over whatever each of them needs:
a verdict assignment and its well-formedness, a view and its closure, a
horizon and a bound. That is the right shape for a proof and the wrong
shape for a reader, who wants to know what FinWhale guarantees and under
what.

`Run` collects one execution of the protocol — the blocks, the schedule
and the network that carried them, the rotation, the tie-break — and the
four properties are stated over it. Their hypotheses are about the run
and nothing else: which validators are correct, and how far the
horizon reaches.

Each property is the corollary of a theorem proved elsewhere, and the
docstring names it. Nothing new is proved here; what is new is that the
statements no longer mention verdict assignments, views, well-formedness
or bounds.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] [LinearOrder BlockId] {Payload : Type*}

namespace Run

variable (run : Run Validator BlockId Payload) {v w : Validator}

/-- And what it holds is a view: part of the run, closed under
references. -/
theorem isView (hv : v ∈ (Correct : Finset Validator)) : IsView run.dag (run.view v) :=
  isView_holds run.pace run.ids_eq run.block_eq hv _

/-- **The verdicts a validator reaches**, by running the reverse pass on
its own view. -/
noncomputable def verdicts (hv : v ∈ (Correct : Finset Validator)) : ℕ → Verdict BlockId :=
  decOf (restrict run.dag (run.view v) (run.isView hv)) run.choose run.horizon

/-- **And what it delivers**: the causal histories of its committed
leader blocks, in order, each block once. -/
noncomputable def delivers (hv : v ∈ (Correct : Finset Validator)) (k : ℕ) : List BlockId :=
  linearise (histOf run.dag) (commitSeq (run.verdicts hv) k)

/-! ## What each validator's pass amounts to

Five short facts, each an instance of a theorem proved elsewhere. They
are what the four properties below are assembled from, and none of them
is a hypothesis of a run. -/

/-- The blocks a validator holds sit below the run's horizon. -/
theorem view_rounds_le (hv : v ∈ (Correct : Finset Validator)) :
    ∀ b ∈ run.view v, (run.dag.block b).round ≤ run.horizon :=
  fun b hb => run.rounds_le b ((run.isView hv).subset hb)

/-- Its verdicts follow the reverse pass. -/
theorem wellFormed (hv : v ∈ (Correct : Finset Validator)) :
    WellFormed (viewCommit run.dag (run.view v) (run.isView hv))
      (viewSkip run.dag (run.view v) (run.isView hv)) run.choose (run.verdicts hv) :=
  wellFormed_decOf (run.view_rounds_le hv) run.choose

/-- A committed verdict names a block of its slot. -/
theorem slot_of_verdicts (hv : v ∈ (Correct : Finset Validator)) {r : ℕ} {A : BlockId}
    (h : run.verdicts hv r = Verdict.commit A) : A ∈ slotBlocks run.dag r :=
  mem_slotBlocks_of_decOf (fun _ => slotBlocks_restrict) run.chooseSound h

/-- Nothing above the horizon is decided. -/
theorem undecided_of_gt (hv : v ∈ (Correct : Finset Validator)) {s : ℕ}
    (hs : run.horizon < s) : run.verdicts hv s = Verdict.undecided :=
  decOf_of_gt hs

/-- Past the stable round, a validator holds every reliable block of
every round below the horizon. -/
theorem held (hv : v ∈ (Correct : Finset Validator)) :
    ∀ n, run.stable ≤ n → n ≤ run.liveHorizon → ∀ b ∈ blocksAt run.dag n,
      (run.dag.block b).creator ∈ (Correct : Finset Validator) → b ∈ run.view v :=
  fun n hRn hnN b hb hbc => held_of_pace run.pace run.ids_eq run.block_eq
    run.rounds_advance card_correct run.gst_le hv n hRn
    (by have := run.live_le; omega) b hb hbc

/-! ## The four properties -/

/-- **Every slot below the horizon is decided.** Lemma 23, over a run:
the rotation names three consecutive correct leaders, their blocks are
committed, and the reverse pass reads every slot below them off that.

The bound is the window Lemma 22 needs — `3f + 3` rounds — plus the two
the anchor sits above, past the round the network stabilised. -/
theorem decided (hv : v ∈ (Correct : Finset Validator)) {r : ℕ}
    (hr : max r run.stable + (3 * F.f + 5) ≤ run.liveHorizon) :
    run.verdicts hv r ≠ Verdict.undecided :=
  all_decided_of_view (run.isView hv) (run.wellFormed hv) (run.held hv) run.commits
    run.roundRobin hr

/-- Below a decided horizon a validator's sequence is complete. -/
theorem decidedBelow (hv : v ∈ (Correct : Finset Validator)) {k : ℕ}
    (hk : max k run.stable + (3 * F.f + 5) ≤ run.liveHorizon) :
    ∀ s, s < k → run.verdicts hv s ≠ Verdict.undecided := by
  intro s hs
  refine run.decided hv ?_
  have : max s run.stable ≤ max k run.stable := max_le_max (by omega) le_rfl
  omega

/-- **Agreement.** Two correct validators deliver the same sequence.
Theorem 24, with the verdicts computed rather than assumed: each
validator's view is what it holds, and its verdicts are the reverse pass
on that view. -/
theorem agreement (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) {k : ℕ}
    (hk : max k run.stable + (3 * F.f + 5) ≤ run.liveHorizon) :
    run.delivers hv k = run.delivers hw k :=
  agreement_of_views (run.isView hv) (run.isView hw) (run.wellFormed hv) (run.wellFormed hw)
    run.chooseSound (fun _ _ h => run.slot_of_verdicts hv h)
    (fun _ _ h => run.slot_of_verdicts hw h)
    (fun s (hs : run.horizon + 1 ≤ s) =>
      ⟨run.undecided_of_gt hv (by omega), run.undecided_of_gt hw (by omega)⟩)
    (run.held hv) (run.held hw) run.commits run.roundRobin hk (histOf run.dag)

/-- **Total order.** One validator's sequence is a prefix of another's,
at any two horizons. Theorem 14 over Lemma 13. -/
theorem totalOrder (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) {k k' : ℕ}
    (hk : max k run.stable + (3 * F.f + 5) ≤ run.liveHorizon)
    (hk' : max k' run.stable + (3 * F.f + 5) ≤ run.liveHorizon) :
    run.delivers hv k <+: run.delivers hw k' ∨ run.delivers hw k' <+: run.delivers hv k :=
  safety_of_pass (run.isView hv) (run.isView hw) run.chooseSound
    (run.view_rounds_le hv) (run.view_rounds_le hw)
    (run.decidedBelow hv hk) (run.decidedBelow hw hk') (histOf run.dag)

/-- **Integrity.** No block is delivered twice. Theorem 15 at the
concrete order, and it asks nothing of the run: the order appends only
what it has not already delivered, and a causal history lists each block
once. -/
theorem integrity (hv : v ∈ (Correct : Finset Validator)) (k : ℕ) :
    (run.delivers hv k).Nodup :=
  nodup_delivery _

/-- **Validity.** A correct validator's block is delivered. Theorem 26:
the block lies in the causal history of its own author's next leader
block, by the self-parent chain, and that slot is committed. -/
theorem validity (hv : v ∈ (Correct : Finset Validator)) {b : BlockId} {k : ℕ}
    (hb : b ∈ run.dag.ids)
    (hbc : (run.dag.block b).creator ∈ (Correct : Finset Validator))
    (hbound : max ((run.dag.block b).round) run.stable + Fintype.card Validator + 2 ≤
      run.liveHorizon)
    (hk : max ((run.dag.block b).round) run.stable + Fintype.card Validator < k) :
    b ∈ run.delivers hv k :=
  theorem26_of_selfParent run.selfParented (run.wellFormed hv)
    (sees_of_commits_of_held (run.isView hv) run.commits (run.held hv))
    run.roundRobin hb hbc hbound hk

end Run

end FinWhale

end LeanDag
