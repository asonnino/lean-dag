# lean-dag — Chain quality: what a commit carries, and who gets in

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document records the **chain quality** arc: machine-checked
theorems about *whose blocks the ledger contains*, in
`LeanDag/Quality/` with witnesses in `LeanDagTest/Quality/`, consuming
the existing development read-only. Results carry **CQ**-labels. Two
families, split exactly along the trust boundary:

1. **Asynchronous coverage** (`Coverage.lean`). Every commit flushes an
   entire cone, and the quorum structure forces every layer of every
   valid cone to carry blocks from all but at most `f` of the correct
   validators — so each commit carries, at every round below it,
   **at least half of the correct validators' blocks**
   (`card_correct_le_two_mul_coveredAt_of_decided`), with no synchrony
   assumption, no delivery model, and no populated rounds anywhere.
2. **Post-synchrony inclusion** (`Inclusion.lean`, `Capstone.lean`).
   After `R`, every correct block is in the cone of every later
   correct-led commit (`mem_history_of_decided_commit`), and commits by
   correct leaders recur — so **every correct block enters the agreed
   ledger** (`committed_of_correct_block`), within an explicit
   schedule-window bound (`committed_of_correct_block_within`,
   `…_by_round`), packaged with the coverage half in the capstone
   `chain_quality`.

The split is genuine, not a proof artifact: the witness model `Ucens`
commits for ever while the *same* correct validator is missing from
every flushed layer, so aggregate coverage provably does not imply
individual inclusion, and the synchrony round `R` is exactly what the
upgrade costs.

## 1. The property

Every protocol in this family claims that leader rotation prevents
censorship; almost none proves what its ledger *contains*. The
classical blockchain form is *chain quality* — the fraction of honest
contribution in any window of the chain — and the DAG setting has a
stronger natural form, because a commit does not append one block: it
flushes the entire causal cone of the committed leader
(`ledgerSet U g n = {b | ∃ k < n, ∃ L, g k = some L ∧ Reaches U L b}`).
The two right questions, and their answers:

- *Coverage*: of the blocks correct validators produced, how many does
  each flush carry? **All but at most `f` authors per round, always.**
- *Inclusion*: is any particular correct validator's block guaranteed
  in, and when? **Yes, from round `R` on, within a schedule window —
  and provably not before `R`.**

## 2. The metric — a decision that held

"Fraction of committed blocks that are correct-authored" is the
conventional metric and the wrong one here: an equivocator can inflate
a cone with any number of blocks per round, so a block-count fraction
is adversary-deflatable. All CQ statements count **distinct correct
authors per round**:

```lean
def coveredAt (U) (b : BlockId) (δ : ℕ) : Finset Validator :=
  (Correct : Finset Validator).filter fun v =>
    ∃ i ∈ history U b, (U.block i).creator = v ∧ (U.block i).round = δ
```

with `coveredAt_eq_sdiff : coveredAt U b δ = Correct \ missingAt U b δ`
tying it to density's complement. The block-fraction variant (CQ4) was
assessed against its recorded gate — *state it only if the constant is
clean* — and **dropped**: under `DoSValid` alone the per-author block
count carries the exponential pedigree constant, and under the budget
the cone-level Byzantine count is the author's whole store bound,
linear in the round rather than the layer; neither yields a ratio worth
quoting.

## 3. Asynchronous coverage (CQ1–CQ3)

The engine is density (D25, `card_missingAt_le`, `DoS/Density.lean`) —
at most `f` correct validators lack a round-`δ` block in any valid
cone — and the results are packaging, exactly as planned:

- **CQ1** (`card_coveredAt_ge`, `card_coveredAt_ge_of_decided`): for a
  committed leader `L` — any route, any view — and every
  `δ < (U.block L).round`,
  `|Correct| − f ≤ (coveredAt U L δ).card`. The only fact consumed
  about the commit is `L ∈ U.ids` (`isLeaderBlock_of_decided`).
- **CQ2** (`card_correct_le_two_mul_coveredAt_of_decided`): the half,
  exactly — `|Correct| ≤ 2·|coveredAt|`, since `|Correct| ≥ 2f+1`.
- **CQ3** (`ledger_coverage`): the cumulative ledger form, in the
  verdict-assignment idiom: for `g` with `Decided U V k (g k)` and
  `g k = some L`, an exhibited set of at least `|Correct| − f` correct
  validators each has a round-`δ` block in `ledgerSet U g n`. The
  bridging lemma `mem_ledgerSet_of_mem_history` is the one unfolding
  CQ3 and CQ6 share; view-independence is `ledgerSet_agree`.

## 4. Post-synchrony inclusion (CQ5–CQ7)

- **CQ5** (`mem_history_of_decided_commit`): post-`R`, every correct
  block is in the cone of every committed leader block with a correct
  author at a later round — the backbone
  (`mem_history_of_correct`, `DoS/Exclusion.lean`) applied through
  `isLeaderBlock_of_decided`, no new counting.
- **CQ6** (`committed_of_correct_block`, and `…_correct` at
  `T := Correct`): under a fair schedule over reliable validators, for
  every round `m ≥ R` there is a committed slot — above `m`, led by a
  correct validator, **fixed by the schedule before the universe is
  quantified**, in the L6 style — whose flush contains every correct
  round-`m` block; ledger membership follows for any covering verdict
  assignment. One discovery from the proof: `commits_recur_on` does
  not expose that the committed leader lies in `T`, which the backbone
  needs, so CQ6 composes from the fair schedule, L4
  (`decided_of_leader_mem`) and `no_stall` directly, mirroring L6's
  own proof rather than consuming its statement.
- **CQ7** (`Capstone.lean`): the quantitative and packaged forms.
  Under a windowed-fair schedule the committing slot lies within `w`
  slots of `slotAt (m+1)` (`committed_of_correct_block_within`);
  bounded spacing converts to rounds, `s·w`
  (`committed_of_correct_block_by_round`) — *a correct block is
  committed within a schedule-window of its creation, once the DAG is
  synchronous*. The capstone `chain_quality` states both halves
  together under enforceable or standard conditions only, in the
  `dos_resistance` style.

A scoping note that held: the schedule side is `T ⊆ Correct`-relative,
the backbone side is Correct-wide (`Synchronised U R`); a fully
`T`-relative variant would need a `T`-relative backbone lemma, possible
but not attempted.

## 5. Witnesses (`LeanDagTest/Quality/Model.lean`)

- **`Ucens`** — tightness and censorship in one universe (`Fin 4`,
  `f = 1`, six rounds): validators `0,1,2` reference only each other;
  validator `3` (correct) builds validly — self-parent plus two
  others — and is never referenced. Slot 1 commits directly with the
  full certificate pattern, and on data: `missingAt = {3}` at **every**
  layer (CQ1's `≤ f` is exactly tight), `coveredAt = {1,2}` (the half),
  `Synchronised` fails at every round while the commit stands, the
  censored validator's blocks are absent from the committed cone and
  from the ledger (`decide` against a concrete verdict assignment),
  and a correct-authored cone block is present. Aggregate coverage is
  not individual inclusion, exhibited.
- **`Uexcl`** — inclusion on data: CQ5 applied puts a correct round-1
  block in the slot-1 commit's cone, confirmed independently by
  `decide`; CQ3 applied yields the two-of-three ledger coverage; CQ6's
  and CQ7's schedule sides instantiate over `fairSlots` and the
  round-robin `rrSlots` (the two-slot window on data).

All witnesses are by `decide` or explicit one-line terms; all proofs
use the standard axioms only.

## 6. Decisions, as they played out

- **Authors per round, not blocks** — held; CQ4 dropped at its gate,
  with both failing routes recorded (§2).
- **Cumulative ledger form** — held; the delta form was never needed.
- **Read-only cross-arc reuse** — held: the arc imports `DoS/Density`
  and `DoS/Exclusion` for D25 and the backbone; nothing outside
  `Quality/` changed.
- **Ledger decidability (R1)** — resolved as predicted in review:
  membership on data is `mem_history_iff` plus a finite slot scan.
- **The `max(m, R)` shape (R2)** — avoided: stating the theorems at
  `R ≤ m` (the only case with content — blocks below `R` get CQ1's
  aggregate guarantee only) keeps every bound in terms of
  `slotAt (m+1)` alone.
- **The censorship model (R3)** — constructed exactly as reviewed, and
  it earned double duty as the CQ1 tightness witness.

## 7. Where everything lives

| Module | Contents |
|:---|:---|
| `LeanDag/Quality/Coverage.lean` | `coveredAt`; CQ1 (`card_coveredAt_ge_of_decided`), CQ2 (`card_correct_le_two_mul_coveredAt_of_decided`), CQ3 (`ledger_coverage`), `mem_ledgerSet_of_mem_history` |
| `LeanDag/Quality/Inclusion.lean` | CQ5 (`mem_history_of_decided_commit`), CQ6 (`committed_of_correct_block`) |
| `LeanDag/Quality/Capstone.lean` | CQ7: `committed_of_correct_block_within`, `…_by_round`, `chain_quality`; the CQ4 verdict |
| `LeanDagTest/Quality/Model.lean` | `Ucens`; every result applied on data; the censorship exhibit |
