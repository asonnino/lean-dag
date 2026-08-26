import LeanDagTest.ViewPace
import LeanDagTest.Reactive
import LeanDag.FinWhale.View
import LeanDag.FinWhale.Reactive

/-!
# FinWhale witnesses — the pacing structure under liveness

`LeanDag/FinWhale/Liveness.lean` derives coverage and production from a
`ViewPace`, and the liveness capstones are stated over one. This file
exhibits an execution that is such a structure, so that those theorems
run on a model rather than on an unfilled premise.

The committee is FinWhale's smallest: `f = 1` and `p = 1` give
`n = 3f + 2p − 1 = 4`, which is the committee the development's own
pacing witness (`LeanDagTest/ViewPace.lean`) is built over. `Ugrow N` is
that execution — four blocks a round, each referencing the whole round
below — and `ugrowSkewCorrect N` is its `ViewPace` over the correct
validators.

What has to be shown here is that the same blocks satisfy FinWhale's
validity rule, which adds the leader clause to Mysticeti's. They do, and
for a reason the layout settles rather than the protocol: an identifier
fixes both the round and the author, so a round holds one block per
validator and the leader's block two rounds down is unique. Nothing in
the parent sets can disagree about it.

At `p = 1` the slow-path quorum and the validity quorum coincide, which
is why the `Fin 9` witnesses of `Model.lean` exist beside this one.
-/

namespace LeanDagTest

namespace FinWhalePace

open LeanDag LeanDag.FinWhale

/-- One fast-path slot at four validators: `n + 1 = 3f + 2p = 5`. -/
local instance growParams : Params (Fin 4) where
  p := 1
  p_pos := by omega
  p_le_f := by decide
  card_add_one := by decide

/-- Round robin, shifted so that round `0` is led by validator `1`:
validator `0` is the Byzantine one here. -/
def growLeader : ℕ → Fin 4 := fun r => ⟨(r + 1) % 4, Nat.mod_lt _ (by omega)⟩

/-- **The grown execution is a FinWhale DAG**, at any leader schedule.
The first three validity clauses are Mysticeti's, and hold of it already;
the leader clause is FinWhale's, and the layout gives it — an identifier
fixes both the round and the author, so the leader's block two rounds
down is unique whatever the schedule names. -/
def DgrowFor (lead : ℕ → Fin 4) (N : ℕ) : Dag (Fin 4) ℕ Unit where
  ids := (Ugrow N).ids
  block := (Ugrow N).block
  leader := lead
  complete := (Ugrow N).complete
  valid := by
    intro i hi
    refine ⟨((Ugrow N).valid i hi).predecessor, ((Ugrow N).valid i hi).distinct_creators,
      ((Ugrow N).valid i hi).quorum, ?_⟩
    intro hround
    refine Or.inl ?_
    intro p hp q hq x hx y hy hxl hyl
    -- the parents sit in one round, so their references sit in one round
    simp only [ugrow_block, growBlock_refs, Finset.mem_Ico] at hp hq hx hy
    simp only [ugrow_block, rrBlock_round] at hround
    -- and inside a round an author has one block
    have hval : x % 4 = y % 4 := by
      have := congrArg (fun (v : Fin 4) => (v : ℕ)) (hxl.trans hyl.symm)
      simpa [ugrow_block] using this
    omega
  correct_single := (Ugrow N).no_equivocation

/-- The execution under the shifted schedule. -/
abbrev Dgrow (N : ℕ) : Dag (Fin 4) ℕ Unit := DgrowFor growLeader N

@[simp] theorem dgrow_ids (N : ℕ) : (Dgrow N).ids = (Ugrow N).ids := rfl

@[simp] theorem dgrow_block (N : ℕ) : (Dgrow N).block = (Ugrow N).block := rfl

/-- The blocks are the ones `Ugrow` lays out: id `1` is validator `1`'s
genesis block, and validator `1` leads round `0`. -/
example : ((Dgrow 5).block 1).round = 0 ∧ ((Dgrow 5).block 1).creator = 1 ∧
    (Dgrow 5).leader 0 = 1 := by decide

/-- And validator `1` is correct, so round `0` has an honest leader. -/
example : ((Dgrow 5).block 1).creator ∈ (Correct : Finset (Fin 4)) := by decide

/-- **Lemma 20 on a pacing structure.** The honest leader's block of
round `0` is directly committed, derived from `ugrowSkewCorrect` — view
convergence, the drift bound and the backoff — and nothing else. -/
example : DirectCommit (Dgrow 5) 1 :=
  directCommit_of_viewPace (D := Dgrow 5) (R := 0) (r := 0) (l := 1) (ugrowSkewCorrect 5) rfl rfl
    (by decide) (fun n _ => Nat.le_refl _) (by omega) (by omega) (by decide) (by decide) (by decide)

/-- **Theorem 26 on a pacing structure.** Validator `2`'s genesis block
is delivered, once the round-`1` leader's slot is committed: it lies in
that leader's causal history, and the ordering is the causal history. -/
example {dec : ℕ → Verdict ℕ} (hcom : dec 1 = Verdict.commit 6) :
    (2 : ℕ) ∈ linearise (histOf (Dgrow 5)) (commitSeq dec 3) :=
  delivered_of_synchronised (D := Dgrow 5) (R := 0)
    (synchronised_of_viewPace (D := Dgrow 5) (ugrowSkewCorrect 5) rfl rfl (by decide)
      (fun n _ => Nat.le_refl _))
    (by omega) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by omega) hcom


/-! ## The reactive schedule

`ViewPace` above is the full-timeout discipline. FinWhale's pacemaker is
reactive — C1 and C3 fire early, and the `2∆` timeout is only the
fallback — so the faithful structure is `ReactivePace`, and the arc's
reactive route runs off it.

The same execution serves. `Ugrow` has every block reference the whole
round below, so both of the reactive wait clauses hold by their *first*
disjunct: the exit is always available, and no fallback argument is
needed. The trunk is reused from the development's own reactive witness;
what is rebuilt here is the schedule — FinWhale names a leader every
round, where Mysticeti's witness names one every three. -/

/-- One leader per round, which is FinWhale's schedule. -/
@[reducible] def fwSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

attribute [local instance 3000] fwSlots

@[simp] theorem fwSlots_slotRound (k : ℕ) : fwSlots.slotRound k = k := by simp

/-- The execution under that schedule. -/
abbrev Dreact (N : ℕ) : Dag (Fin 4) ℕ Unit := DgrowFor (fun k => ⟨k % 4, by omega⟩) N

/-- **Every block votes.** A round-`(r+1)` block of this layout
references the whole of round `r`. -/
theorem ugrow_votes {N r : ℕ} {c L : ℕ}
    (hcr : ((Ugrow N).block c).round = r + 1)
    (hLr : ((Ugrow N).block L).round = r) : L ∈ ((Ugrow N).block c).refs := by
  simp only [ugrow_block, rrBlock_round] at hcr hLr
  simp only [ugrow_block, mem_growBlock_refs]
  omega

/-- **And every round-`(r+2)` block certifies.** Its parents are the
whole of round `r + 1`, and each of them votes, so the votes it carries
are the whole committee. -/
theorem ugrow_certifies {N r : ℕ} {c L : ℕ} (hc : c ∈ (Ugrow N).ids)
    (hcr : ((Ugrow N).block c).round = r + 2)
    (hLr : ((Ugrow N).block L).round = r) : Certifies (Ugrow N) c L := by
  have hfilter : votesIn (Ugrow N) c L = ((Ugrow N).block c).refs := by
    refine Finset.filter_true_of_mem fun q hq => ?_
    have hqids : q ∈ (Ugrow N).ids := (Ugrow N).complete c hc q hq
    have hqr : ((Ugrow N).block q).round = r + 1 := by
      have := (Ugrow N).round_of_mem_refs hc hq
      omega
    exact ugrow_votes hqr hLr
  show quorumCard (Fin 4) ≤ (creatorsOf (Ugrow N).block (votesIn (Ugrow N) c L)).card
  rw [hfilter]
  exact ((Ugrow N).valid c hc).quorum (by omega)

/-- The trunk — views, convergence, the progress and catch-up rules — is
the development's own reactive witness, read at its own schedule; the
structure below rebuilds only the schedule-dependent clauses. -/
def fwPaceCore (N : ℕ) : PaceCore (Ugrow N) {1, 2, 3} N :=
  ReactivePace.toPaceCore (S := rrSlots) (ReactiveM.toReactivePace (S := rrSlots) (ugrowReactive N))

@[simp] theorem fwPaceCore_built (N : ℕ) (v : Fin 4) (n : ℕ) :
    (fwPaceCore N).built v n = (v : ℕ) + 6 * n := rfl

@[simp] theorem fwPaceCore_timeout (N : ℕ) (n : ℕ) : (fwPaceCore N).timeout n = 9 := rfl

@[simp] theorem fwPaceCore_proc (N : ℕ) : (fwPaceCore N).proc = 5 := rfl

@[simp] theorem fwPaceCore_holds (N : ℕ) (v : Fin 4) (t : ℕ) :
    (fwPaceCore N).holds v t = reactHolds N v t := rfl

/-- **The reactive witness at FinWhale's schedule.** -/
def fwReactive (N : ℕ) : ReactiveM (Ugrow N) {1, 2, 3} N :=
  { fwPaceCore N with
    built_lt := fun _ _ _ _ => by simp only [fwPaceCore_built]; omega
    deadline := fun _ _ _ _ => by simp only [fwPaceCore_built, fwPaceCore_timeout]; omega
    vote_or_wait := fun v hv k hN _ L hL c hc hcc hcr =>
      Or.inl (ugrow_votes hcr hL.2.1)
    prompt_vote := fun v hv k hN hlead L hL t hbuilt hheld hall => by
      obtain ⟨h1, h3⟩ := mem_T_bounds hv
      have hv4 := v.isLt
      have h2 := hall (4 * k + 2)
        (by
          have hk : fwSlots.slotRound k = k := by simp
          simp only [ugrow_ids, Finset.mem_range]
          rw [hk] at hN; omega)
        (by
          have : ((Ugrow N).block (4 * k + 2)).creator = (2 : Fin 4) := by
            apply Fin.ext
            simp only [ugrow_block, rrBlock_creator_val]
            omega
          rw [this]; decide)
        (by simp only [ugrow_block, rrBlock_round, fwSlots_slotRound]; omega)
      have h3' := hall (4 * k + 3)
        (by
          have hk : fwSlots.slotRound k = k := by simp
          simp only [ugrow_ids, Finset.mem_range]
          rw [hk] at hN; omega)
        (by
          have : ((Ugrow N).block (4 * k + 3)).creator = (3 : Fin 4) := by
            apply Fin.ext
            simp only [ugrow_block, rrBlock_creator_val]
            omega
          rw [this]; decide)
        (by simp only [ugrow_block, rrBlock_round, fwSlots_slotRound]; omega)
      simp only [fwPaceCore_holds, reactHolds, Finset.mem_filter, Finset.mem_range] at h2 h3'
      have e2 : (4 * k + 2) % 4 = 2 := by omega
      have d2 : (4 * k + 2) / 4 = k := by omega
      have e3 : (4 * k + 3) % 4 = 3 := by omega
      have d3 : (4 * k + 3) / 4 = k := by omega
      rw [e2, d2] at h2
      rw [e3, d3] at h3'
      show (v : ℕ) + 6 * (fwSlots.slotRound k + 1) ≤ t + 5
      simp only [fwSlots_slotRound]
      rcases h2.2 with ha | ⟨hb, hc⟩ <;> rcases h3'.2 with hd | ⟨he, hf⟩ <;> omega
    cert_or_wait := fun v hv k hN _ L hL c hc hcc hcr =>
      Or.inl (ugrow_certifies hc hcr hL.2.1) }

/-- The same, over `Correct`. -/
def fwReactiveCorrect (N : ℕ) : ReactiveM (Ugrow N) (Correct : Finset (Fin 4)) N := by
  rw [show (Correct : Finset (Fin 4)) = {1, 2, 3} from by decide]
  exact fwReactive N

/-- **The liveness interface, off the reactive schedule.** Every
correct-led slot below the horizon carries a direct commit — with no
coverage assumption anywhere, since a reactive builder has none. -/
example (N : ℕ) : CommitsCorrectLeaders (Dreact N) 0 N :=
  commits_of_reactive (D := Dreact N) (fwReactiveCorrect N) rfl rfl
    (fun k => by simp) (fun k => rfl) rfl (Nat.le_refl _) (fun n _ => Nat.le_refl _)

/-- And the fast path on the same schedule. Round `1` is led by validator
`1`, which is correct, and its block is id `5`: at most `p = 1` Byzantine
validator makes the correct validators' votes an `n − p` fast commit. -/
example (N : ℕ) (hN : 2 ≤ N) : FastCommit (Dreact N) 5 :=
  fastCommit_of_reactive (D := Dreact N) (k := 1) (R := 0)
    (fwReactiveCorrect N).toReactivePace rfl rfl rfl (by decide) (Nat.le_refl _)
    (fun n _ => Nat.le_refl _) (by omega) (by simpa using hN) (by decide)
    ⟨by simp only [ugrow_ids, Finset.mem_range]; omega, by simp,
      by apply Fin.ext; simp only [ugrow_block, rrBlock_creator_val]; rfl⟩

end FinWhalePace

end LeanDagTest
