import LeanDag.Schedule
import LeanDag.Liveness

/-!
# Pipelined and multi-leader schedules — the witnesses

`Model.lean` exercises the commit rule against the original schedule, one
leader every three rounds. This file exercises the two schedules that
generalisation was for, and pins down the fact that motivated it: under
pipelining and under multiple leaders, **the next slot cannot anchor the
current one**.

Each schedule is a `local instance`, so the two never meet — as with
`Growth.lean`, which carries its own `Slots (Fin 4)` for the same reason.

Everything here is settled by `decide`: `Eligible` is a comparison of two slot
rounds and `Slots.uniform` computes.
-/

namespace LeanDagTest

open LeanDag

-- Axiom audit for the results the generalisation introduced or reproved.
#print axioms LeanDag.decided_unique
#print axioms LeanDag.certifiedIn_of_directCommitIn
#print axioms LeanDag.eligible_of_lt_of_spacing
#print axioms LeanDag.lt_of_eligible
#print axioms LeanDag.slot_eq_of_isLeaderBlock
#print axioms LeanDag.slot_eq_of_decided_commit
#print axioms LeanDag.exists_eligible
#print axioms LeanDag.commits_recur_on
#print axioms LeanDag.decided_of_first_eligible_commit
#print axioms LeanDag.decided_below_of_committed_run
#print axioms LeanDag.all_decided_below_of_fairRun
#print axioms LeanDag.all_decided_below_of_fairRun_correct
#print axioms LeanDag.decided_of_committed_above
#print axioms LeanDag.all_decided_below_of_spacing
#print axioms LeanDag.notMem_stuck_of_decided
#print axioms LeanDag.stuck_empty_below_commit_of_spacing
#print axioms LeanDag.Slots.uniform
#print axioms LeanDag.Slots.uniformSingle_slotRound

/-! ## Pipelined: one leader in every round

`slotRound k = k`. Slot `k`'s certificates sit at round `k + 2`, so the first
slot that can anchor it is `k + 3` — the next two are useless, and under the
pre-pipelining premise `k < j` they would both have qualified. -/

section Pipelined

local instance pipeSlots : Slots (Fin 4) :=
  Slots.uniformSingle 1 (by omega) (fun k => ⟨k % 4, by omega⟩)

@[local simp] theorem pipeSlots_slotRound (k : ℕ) : pipeSlots.slotRound k = k := by
  change 1 * (k / 1) = k
  omega

example : pipeSlots.slotRound 0 = 0 := by decide
example : pipeSlots.slotRound 1 = 1 := by decide
example : pipeSlots.slotRound 7 = 7 := by decide

/-- A leader in every round, rotating. -/
example : pipeSlots.leader 0 = 0 := by decide
example : pipeSlots.leader 5 = 1 := by decide

/-- **The point of `Eligible`.** The next slot is one round on, and a block
there cannot reach a round-`2` certificate for slot `0`. Under the old
premise — merely `0 < 1` — it would have been an admissible anchor, and one
validator's direct commit would have become another's indirect skip. -/
example : ¬ Eligible (Fin 4) 0 1 := by decide

/-- Nor the slot after that: certificates for slot `0` sit at round `2`, and
a round-`2` block reaches only round-`1` blocks. This is M2's bound being
tight. -/
example : ¬ Eligible (Fin 4) 0 2 := by decide

/-- Three rounds on, the anchor is in range — and every later one too. -/
example : Eligible (Fin 4) 0 3 := by decide
example : Eligible (Fin 4) 0 4 := by decide

/-- Eligibility is upward-closed, so "the nearest eligible committed slot" is
well defined: the intermediate premise of `Decided` ranges over slots `3` up
to the anchor, not over `1` and `2`. -/
example : ∀ j, 3 ≤ j → Eligible (Fin 4) 0 j := by
  intro j hj
  rw [eligible_iff]
  simp only [pipeSlots_slotRound]
  omega

/-- An eligible anchor always exists — L6's `exists_eligible` on this
schedule. -/
example : ∃ j, Eligible (Fin 4) 0 j := exists_eligible 0

/-- **L8's hypothesis fails here, and this is the whole cost of pipelining.**

`decided_of_committed_above` clears the backpressure — no slot below a commit
is left undecided — on the strength of *every* later slot being an eligible
anchor. Slot `1` is not one for slot `0`, so the guarantee does not transfer,
and the counterexample recorded at L8 shows it genuinely fails rather than
merely resisting proof. -/
example : ¬ (∀ a b : ℕ, a < b → Eligible (Fin 4) a b) :=
  fun h => absurd (h 0 1 (by omega)) (by decide)

/-- **L9's regress clause is satisfiable here**, and this is the arithmetic
that makes a stuck set possible. An eligible anchor must clear slot `i`'s
decision round, so unless it is the very first eligible slot there is room for
an *eligible* intermediate between the two — and that intermediate is what L9's
descent consumes. -/
example (i j : ℕ) (hgap : i + 3 < j) :
    ∃ i', i < i' ∧ i' < j ∧ Eligible (Fin 4) i i' := by
  refine ⟨i + 3, by omega, hgap, ?_⟩
  rw [eligible_iff]
  simp only [pipeSlots_slotRound]
  omega

/-! ### The escape

Nothing strictly between `k` and `k + 3` is eligible to anchor `k`, and `k + 3`
is. So an anchor at `k + 3` carries a **vacuous** intermediate premise, and
`decided_of_first_eligible_commit` applies with no induction.

This is what stops pipelining from stalling the ledger: slot `j - 1`, which
cannot anchor on a committed `j`, anchors on `j + 2` instead — and under fair
leader election `j + 2` is committed whenever `j` is. -/

/-- The first slot eligible to anchor `k` is `k + 3`; nothing between qualifies. -/
theorem pipe_not_eligible_between (k i : ℕ) (h1 : k < i) (h2 : i < k + 3) :
    ¬ Eligible (Fin 4) k i := by
  simp only [eligible_iff, pipeSlots_slotRound]
  omega

theorem pipe_eligible_add_three (k : ℕ) : Eligible (Fin 4) k (k + 3) := by
  simp only [eligible_iff, pipeSlots_slotRound]
  omega

-- These two are exactly the arguments `decided_of_first_eligible_commit` takes,
-- so a committed slot at `k + 3` decides slot `k` with no induction. Stating
-- that composition here would need a `Faults (Fin 4)` instance, which this file
-- deliberately does without; the composition is the lemma itself.

/-- **`hspan` for P7′, at three consecutive slots.** Every slot below `b` has
`b + 2` as an eligible anchor, so `decided_below_of_committed_run` applies to a
run of three: `b`, `b + 1`, `b + 2`.

Three is exactly right and two will not do — `Eligible (b - 1) (b + 1)` is
false, since slot `b - 1`'s certificates sit at round `b + 1`. -/
theorem pipe_hspan (b i : ℕ) (hi : i < b) : Eligible (Fin 4) i (b + 2) := by
  simp only [eligible_iff, pipeSlots_slotRound]
  omega

example (b : ℕ) (hb : 0 < b) : ¬ Eligible (Fin 4) (b - 1) (b + 1) := by
  simp only [eligible_iff, pipeSlots_slotRound]
  omega

/-- **`SpansEligible 3`**, which is L10's schedule-shape hypothesis at this
schedule: a run of three consecutive slots reaches three rounds past everything
below it. -/
theorem pipe_spansEligible : SpansEligible (Validator := Fin 4) 3 := by
  intro b i hi
  simpa using pipe_hspan b i hi

/-! ### Round-robin supplies the run

`FairRunOn T 3` is L10's other hypothesis. Round-robin over four validators with
one Byzantine satisfies it: slots `4k+1, 4k+2, 4k+3` are led by validators
`1, 2, 3`, all correct. In general `f` Byzantine among `3f+1` cut the rotation
into at most `f` arcs holding `2f+1` correct slots, so some arc has
`⌈(2f+1)/f⌉ = 3` — enough for every `f ≥ 1`. -/

theorem pipe_leader_val (j : ℕ) : (pipeSlots.leader j).val = j % 4 := rfl

theorem mem_T_of_val_ne_zero :
    ∀ {v : Fin 4}, v.val ≠ 0 → v ∈ ({1, 2, 3} : Finset (Fin 4)) := by decide

/-- **A run of three correct leaders, arbitrarily far out.** -/
theorem pipe_fairRun : FairRunOn (S := pipeSlots) ({1, 2, 3} : Finset (Fin 4)) 3 := by
  intro k
  refine ⟨4 * k + 1, by omega, ?_⟩
  intro i hi
  exact mem_T_of_val_ne_zero (by rw [pipe_leader_val]; omega)

/-- **L10 applies to this schedule — pipelined liveness, assembled.**

Everything L10 asks of the *schedule* is discharged by the two theorems above.
What is left are hypotheses about the DAG and the network — `Live`,
`DeliversQuorum`, `SynchronisedOn`, and the horizon — which is exactly the
intended division of labour, and identical to what L4 and L6 already need. -/
example {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
    [F : Faults (Fin 4)] (hT : ({1, 2, 3} : Finset (Fin 4)) ⊆ Correct)
    (hcard : 2 * F.f + 1 ≤ ({1, 2, 3} : Finset (Fin 4)).card) (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ pipeSlots.slotRound b ∧
      ∀ (U : BlockUniverse (Fin 4) BlockId Payload) (D : Delivery U) (N : ℕ),
        Live U D N → DeliversQuorum D → SynchronisedOn U ({1, 2, 3} : Finset (Fin 4)) R →
        pipeSlots.slotRound (b + 3 - 1) + 2 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v :=
  all_decided_below_of_fairRun (by omega) hT hcard pipe_spansEligible pipe_fairRun R k

end Pipelined

/-! ## The original schedule, for contrast

One leader every three rounds. Here eligibility and lateness coincide, which
is what L8 needs: the nearest committed slot above any slot is always an
admissible anchor for it, so the intermediate range shrinks and the downward
induction terminates. -/

section Spaced

local instance spacedSlots : Slots (Fin 4) :=
  Slots.uniformSingle 3 (by omega) (fun k => ⟨k % 4, by omega⟩)

@[local simp] theorem spacedSlots_slotRound (k : ℕ) : spacedSlots.slotRound k = 3 * k := by
  change 3 * (k / 1) = 3 * k
  omega

/-- **Eligibility is lateness.** Both directions: `lt_of_eligible` holds for
every schedule, and the converse is what the three-round spacing buys. -/
example : ∀ a b : ℕ, a < b ↔ Eligible (Fin 4) a b := by
  intro a b
  constructor
  · intro h
    rw [eligible_iff]
    simp only [spacedSlots_slotRound]
    omega
  · exact lt_of_eligible

/-- So L8 applies, and the slot immediately below a commit — the one pipelining
cannot decide — is decided here. -/
example : Eligible (Fin 4) 6 7 := by decide

/-- The next slot is always a legitimate anchor, which is what pipelining
denies. -/
example (i : ℕ) : Eligible (Fin 4) i (i + 1) := by
  rw [eligible_iff]
  simp only [spacedSlots_slotRound]
  omega

/-- **And L9's regress clause is blocked here.** With `i + 1` already an
eligible anchor, there is nothing eligibly between it and `i`, so a stuck set
cannot contain the slot below a commit. This is the arithmetic behind
`stuck_empty_below_commit_of_spacing`: under three-round spacing the descent has
nowhere to go. -/
example (i : ℕ) : ¬ ∃ i', i < i' ∧ i' < i + 1 ∧ Eligible (Fin 4) i i' := by
  rintro ⟨i', h1, h2, -⟩
  omega

/-- **`hspan` for P7′ needs only a *single* commit here.** Under three-round
spacing every slot below `b` has `b` itself as an eligible anchor, so
`decided_below_of_committed_run` applies with `n = b`. Pipelining is what turns
"one commit" into "three consecutive commits" — the whole difference between the
two schedules, in one line each. -/
theorem spaced_hspan (b i : ℕ) (hi : i < b) : Eligible (Fin 4) i b := by
  simp only [eligible_iff, spacedSlots_slotRound]
  omega

/-- So L10's schedule-shape hypothesis holds at `c = 1` here, against `c = 3`
under pipelining. That single number is the entire cost pipelining imposes on
ledger-advance. -/
theorem spaced_spansEligible : SpansEligible (Validator := Fin 4) 1 := by
  intro b i hi
  simpa using spaced_hspan b i hi

end Spaced

/-! ## Multi-leader: two leaders in every round

`slotRound k = k / 2`, so slots `2i` and `2i+1` share round `i`. Their
leaders differ, which is what `Slots.keyed` needs and what makes them genuinely
two slots rather than one counted twice. -/

section MultiLeader

/-- Two proposers per round over four validators. The distinctness condition
is real arithmetic here rather than a formality: slots sharing a round differ
by one, and `k % 4` separates them. -/
local instance duoSlots : Slots (Fin 4) :=
  Slots.uniform 1 2 (by omega) (by omega) (fun k => ⟨k % 4, by omega⟩)
    (fun k₁ k₂ h hl => by
      have : k₁ % 4 = k₂ % 4 := congrArg Fin.val hl
      omega)

-- Slots 0 and 1 share round 0; slots 2 and 3 share round 1.
example : duoSlots.slotRound 0 = 0 := by decide
example : duoSlots.slotRound 1 = 0 := by decide
example : duoSlots.slotRound 2 = 1 := by decide
example : duoSlots.slotRound 3 = 1 := by decide

/-- The two slots of a round are led by *different* validators. Were they
not, one block would be the candidate for both and the ledger would deliver
it twice — which is exactly what `Slots.keyed` rules out. -/
example : duoSlots.leader 0 ≠ duoSlots.leader 1 := by decide

/-- **A co-round slot cannot anchor.** Slot `1` is not merely too close, it is
at the *same* round as slot `0`. Under the old `k < j` premise it would have
qualified, since `0 < 1`. -/
example : ¬ Eligible (Fin 4) 0 1 := by decide

/-- Nor anything below round `3`: slots `2` through `5` sit at rounds `1` and
`2`. -/
example : ¬ Eligible (Fin 4) 0 5 := by decide

/-- Slot `6` opens round `3`, and is the first eligible anchor for slot `0`.
With two leaders per round the wait is six slots but still only three
rounds — the commit depth is unchanged, which is the whole point. -/
example : Eligible (Fin 4) 0 6 := by decide

/-- The ledger advances two slots per round rather than one per three. -/
example : duoSlots.slotRound 6 = 3 := by decide

end MultiLeader

/-! ## Why `keyed` is a real condition

A schedule that gives one validator two slots in a round is rejected, and has
to be: the two slots would have the same round and the same leader, so
`IsLeaderBlock` could not tell them apart and a single block would be
committed at both. `Slots.uniform` refuses to build such a schedule, because
its `hblock` argument is unprovable. -/

example : ¬ (∀ k₁ k₂ : ℕ, k₁ / 2 = k₂ / 2 → (fun _ : ℕ => (0 : Fin 4)) k₁ =
    (fun _ : ℕ => (0 : Fin 4)) k₂ → k₁ = k₂) := by
  intro h
  exact absurd (h 0 1 (by decide) rfl) (by decide)

/-- With one leader per round the condition is free, which is why
`uniformSingle` needs no argument for it: slots of a round *are* the round. -/
example (elect : ℕ → Fin 4) : ∀ k₁ k₂ : ℕ, k₁ / 1 = k₂ / 1 → elect k₁ = elect k₂ → k₁ = k₂ :=
  Slots.one_hblock elect

end LeanDagTest
