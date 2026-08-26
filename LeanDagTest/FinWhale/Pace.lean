import LeanDagTest.ViewPace
import LeanDag.FinWhale.View

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

/-- **The grown execution is a FinWhale DAG.** The first three validity
clauses are Mysticeti's, and hold of it already; the leader clause is
FinWhale's, and the layout gives it. -/
def Dgrow (N : ℕ) : Dag (Fin 4) ℕ Unit where
  ids := (Ugrow N).ids
  block := (Ugrow N).block
  leader := growLeader
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

end FinWhalePace

end LeanDagTest
