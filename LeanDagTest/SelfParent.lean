import LeanDagTest.Exposure
import LeanDagTest.Exclusion
import LeanDag.SelfParent

/-!
# Self-parent chains on concrete DAGs

`dos-equivocation-and-growth.md` §5, the witnesses for **D20**–**D24**.

`Umerge` (from `LeanDagTest.Exposure`) already satisfies the strengthened
validity — every non-genesis block references a block by its own author — so
the exact-cost results can be read off it directly. The numbers to watch:

* block `12` (validator 1, round 3) carries validator 1's chain
  `12 → 9 → 6 → 1`: **exactly one** block per round, rounds 0–3 (D22);
* it references block `10` (validator 2), and pays for that with validator
  2's full chain `10 → 7 → 2` — **exactly one** per round strictly below,
  and none at round 3 (D23);
* its history holds 12 blocks, above the floor `(2f+1)·3 + 1 = 10` (D24);
* validator 0 — exposed at the merge — has *no* block above round 1, and
  D21 is why no extension of this DAG can ever change that: a 0-authored
  block above the merge would reference its own self-parent while exposed
  to itself.
-/

namespace LeanDagTest

open LeanDag

/-! ## The self-parent condition holds, visibly -/

-- Validator 1's chain in `Umerge`: 12 → 9 → 6 → 1, one edge per round.
example : (9 : Fin 13) ∈ (Umerge.block 12).refs ∧
    (Umerge.block 9).creator = (Umerge.block 12).creator := by decide
example : (6 : Fin 13) ∈ (Umerge.block 9).refs ∧
    (Umerge.block 6).creator = (Umerge.block 9).creator := by decide
example : (1 : Fin 13) ∈ (Umerge.block 6).refs ∧
    (Umerge.block 1).creator = (Umerge.block 6).creator := by decide

/-- **D20 applied.** Validator 1 appears in block 12's history at *every*
round below it — the chain is contiguous to the ground. -/
example : ∀ t ≤ (Umerge.block 12).round, ∃ i ∈ history Umerge 12,
    (Umerge.block i).creator = (Umerge.block 12).creator ∧ (Umerge.block i).round = t :=
  fun _ ht => exists_self_ancestor (by decide) ht

/-! ## D21 — no self-laundering -/

/-- **D21 applied.** No block of `Umerge` is exposed to its own author —
including the merge blocks, which *are* exposed to validator 0 but are not
authored by it. -/
example : ∀ b ∈ Umerge.ids, ¬ ExposedIn Umerge b (Umerge.block b).creator :=
  fun _ hb => not_exposedIn_self_creator umerge_dosValid hb

-- The content of that statement, concretely: the merge block 9 is exposed to
-- validator 0 and authored by validator 1 — and had validator 0 authored a
-- block referencing 9's frontier, that block would be exposed to its own
-- author, which D21 forbids in any DoS-valid universe. Exclusion by exposure
-- and exclusion from *building* are now the same fact.
example : ExposedIn Umerge 9 0 ∧ (Umerge.block 9).creator ≠ 0 := by decide

/-! ## D22/D23 — the exact cost of a reference -/

/-- **D22 applied.** One block of the author per round, exactly, rounds 0–3. -/
example : ∀ t ≤ (Umerge.block 12).round,
    (historyBlocksOf Umerge 12 (Umerge.block 12).creator t).card = 1 :=
  fun _ ht => card_historyBlocksOf_self umerge_dosValid (by decide) ht

/-- **D22 totalled**: the own-author content of block 12's history is exactly
`round + 1 = 4` blocks — the chain `12, 9, 6, 1` and nothing else. -/
example : ((history Umerge 12).filter
    (fun i => (Umerge.block i).creator = (Umerge.block 12).creator)).card = 3 + 1 :=
  card_filter_self_creator umerge_dosValid (by decide)

/-- **D23 applied.** Referencing block 10 (validator 2) costs exactly one
validator-2 block per round strictly below block 12. -/
example : ∀ t < (Umerge.block 12).round,
    (historyBlocksOf Umerge 12 (Umerge.block 10).creator t).card = 1 :=
  fun _ ht => card_historyBlocksOf_of_mem_refs umerge_dosValid (by decide) (by decide) ht

/-- **D23 totalled**: exactly `round = 3` blocks — the chain `10, 7, 2`,
whole and nothing more. A reference buys one clean chain, in full. -/
example : ((history Umerge 12).filter
    (fun i => (Umerge.block i).creator = (Umerge.block 10).creator)).card = 3 :=
  card_filter_creator_of_mem_refs umerge_dosValid (by decide) (by decide) (by decide)

-- The counts are facts about the model too, so `decide` confirms the
-- theorems' outputs against the raw data.
example : ((history Umerge 12).filter
    (fun i => (Umerge.block i).creator = 1)).card = 4 := by decide
example : ((history Umerge 12).filter
    (fun i => (Umerge.block i).creator = 2)).card = 3 := by decide

/-! ## D24 — the floor -/

/-- **D24 applied.** Block 12's history must hold at least
`(2f+1)·round + 1 = 10` blocks; it holds 12. -/
example : (2 * Faults.f (Fin 4) + 1) * (Umerge.block 12).round + 1 ≤
    (history Umerge 12).card :=
  card_history_ge (by decide) (by decide)

example : (history Umerge 12).card = 12 := by decide

/-- And on the six-round `Uexcl`: the floor at round 5 is `16`, met with an
18-block history — the DAG that keeps committing after excluding validator 0
still pays full price for its chains. -/
example : (2 * Faults.f (Fin 4) + 1) * (Uexcl.block 17).round + 1 ≤
    (history Uexcl 17).card :=
  card_history_ge (by decide) (by decide)

example : (history Uexcl 17).card = 18 := by decide

end LeanDagTest
