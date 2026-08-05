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

end Pipelined

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
