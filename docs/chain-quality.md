# lean-dag — Chain quality: what a commit carries, and who gets in

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Design notes and plan for **chain quality**: theorems about *whose blocks
the ledger contains*. Two families, with sharply different trust
requirements:

1. **Asynchronous coverage.** Every commit flushes an entire cone, and
   the quorum structure forces every layer of every valid cone to carry
   blocks from all but at most `f` of the correct validators — so each
   commit carries, at every round below it, **at least half of the
   correct validators' blocks**, with no synchrony assumption anywhere.
2. **Post-synchrony inclusion (censorship resistance).** After `R`,
   every correct block is in the cone of every later correct block (the
   backbone), commits by correct leaders recur, and therefore **every
   correct block enters the agreed ledger**, within an explicit bound.

Results use **CQ**-labels; plan phases are CQP0–CQP4. The intended home
is `LeanDag/ChainQuality/` with witnesses in
`LeanDagTest/ChainQuality/`, consuming the existing development
read-only — the same additive discipline as the DoS, GC and Odontoceti
arcs.

## 1. The property, and why it is worth proving

Every protocol in this family claims that leader rotation prevents
censorship; almost none proves what its ledger *contains*. The classical
blockchain form of the property is *chain quality* (the fraction of
honest contribution in any window of the chain); the DAG setting has a
stronger natural form, because a commit does not append one block — it
flushes the **entire causal cone** of the committed leader
(`ledgerSet U g n = {b | ∃ k < n, ∃ L, g k = some L ∧ Reaches U L b}`,
§3.6 of the report). The right questions are therefore:

- *Coverage*: of the blocks correct validators produced, how many does
  each flush carry?
- *Inclusion*: is any particular correct validator's block guaranteed to
  be committed, and when?

The two questions separate exactly along the trust boundary: coverage is
structural and asynchronous; individual inclusion is a liveness property
and genuinely needs the synchrony round `R` — asynchronously, the *same*
`f` correct validators could be the ones missing from every layer, so an
aggregate guarantee is the best available. Making that separation
precise is half the point of the arc.

## 2. A recorded decision: coverage counts authors, not blocks

"Fraction of committed blocks that are correct-authored" is the
conventional chain-quality metric, and it is the wrong one here: an
equivocator can inflate a cone with many blocks per round (the DoS arc's
§7 is the study of exactly that), so a raw block-count fraction is
adversary-deflatable. The robust metric — and the one the existing
machinery bounds — is **per-round author coverage**: for each round `δ`
below the committed leader, count the correct validators whose round-`δ`
block appears in the flushed cone. All CQ statements use this metric.
(A block-fraction corollary *under the novelty budget* is available as a
stretch goal, CQ4, since the budget is what bounds the Byzantine
inflation; it is deliberately not the headline.)

## 3. Asynchronous coverage

The engine already exists: **density** (D25, `card_missingAt_le`,
`LeanDag/DoS/Density.lean`). For any valid block `b` and any round
`δ < round(b)`,

```lean
missingAt U b δ = (Correct).filter fun v =>
  ∀ i ∈ history U b, ¬ ((U.block i).creator = v ∧ (U.block i).round = δ)

theorem card_missingAt_le (hb : b ∈ U.ids) (hδ : δ < (U.block b).round) :
    (missingAt U b δ).card ≤ F.f
```

— at most `f` correct validators lack a round-`δ` block in the cone.
This is purely structural (the quorum clause of validity, layer by
layer); no synchrony, no delivery, no populated rounds. The new content
is packaging, not proof machinery:

- **CQ1 (per-commit coverage).** For a committed leader block `L`
  (`Decided U V k (some L)` — any route, any view) and every
  `δ < (U.block L).round`: at least `|Correct| − f` correct validators
  have a round-`δ` block in `H(L)`. Proof: `isLeaderBlock_of_decided`
  gives `L ∈ U.ids`; apply density. Note the statement quantifies over
  *decided* commits, so by agreement (M6) the guarantee is
  view-independent.
- **CQ2 (the half, exactly).** `|Correct| − f ≥ |Correct| / 2` —
  because `|Correct| ≥ n − f ≥ 2f + 1 ≥ 2f`. So: **every commit
  carries, at every round below it, blocks from at least half of the
  correct validators** — at the boundary `n = 3f+1`, from at least
  `f+1` of the `2f+1`. Pure arithmetic over CQ1; this is the quotable
  form and confirms the design intuition that motivated the arc.
- **CQ3 (ledger form).** Lifted to `ledgerSet`: after any commit at
  slot `k` with leader round `r`, the agreed ledger contains, for every
  `δ < r`, round-`δ` blocks of at least `|Correct| − f` correct
  authors. Stated **cumulatively** (a recorded decision): the
  per-flush *delta* — what slot `k` adds over slot `k−1` — is awkward
  under pipelining, where consecutive cones overlap heavily, while the
  cumulative form is monotone (`ledgerSet_mono`), agreed
  (`ledgerSet_agree`), and composes with CQ1 by one unfolding of
  `ledgerSet`.
- **CQ4 (stretch — block-fraction purity under the budget).** Under
  `DoSValid` or the novelty budget, the Byzantine *block count* per
  committed cone is bounded (§7's machinery), giving a classical
  chain-quality fraction. Optional; only worth stating if the constant
  comes out clean.

## 4. Post-synchrony inclusion

The second family upgrades the aggregate guarantee to an individual one,
at the price of `R` — and only at that price, which the plan records as
a negative observation worth witnessing: asynchronously, nothing
prevents the *same* correct validator being among the `f` missing from
every layer of every commit for ever.

The engine is the **backbone** (`mem_history_of_correct`,
`LeanDag/DoS/Exclusion.lean`): post-`R`, a correct block at round
`m ≥ R` is in the cone of every correct block at every round `> m`. The
new content composes it with commit recurrence:

- **CQ5 (inclusion in every later correct commit).** Post-`R`, every
  correct block `b` at round `m ≥ R` is in `H(L)` for **every**
  committed leader block `L` with a correct author and
  `(U.block L).round > m`. Proof: `isLeaderBlock_of_decided` + the
  backbone. No new counting.
- **CQ6 (inclusion liveness — the headline).** Every correct block at
  round `m ≥ R` enters the agreed ledger, and within an explicit bound:
  commits by reliable leaders recur (`commits_recur_on`, L6), a
  recurring commit above round `m` exists, CQ5 puts `b` in its cone,
  and `ledgerSet` membership follows. Quantitative forms come from the
  L8b machinery: under a windowed-fair schedule the committing slot is
  within `w` slots (`commits_recur_within`) and its round within
  `s·w` rounds (`commits_recur_by_round`) of `max(m, R)` — so the
  statement can be phrased as *"a correct block is committed within a
  schedule-window of rounds of its creation, once the DAG is
  synchronous"*. For pipelined schedules the same composition runs
  through the committed-run results (`all_decided_below_of_fairRun`).
- **CQ7 (enforceable-hypotheses form).** The capstone packaging in the
  house style of `dos_resistance`: under `Live`, `DeliversQuorum`,
  `SynchronisedOn`, and a fair schedule — enforceable or standard
  conditions only — every correct block from round `R` on is in the
  ledger of every correct validator's view within the CQ6 bound.

A boundary note for honesty in the doc and the eventual report section:
CQ5–CQ7 concern blocks at rounds `≥ R`. Correct blocks *below* `R` get
only the aggregate CQ1 guarantee plus whatever cones happen to carry
them — the common-core theorem (T3c) guarantees one common correct
ancestor per round, not full inclusion — and this is a real asymmetry of
the model, not a proof gap: pre-`R` delivery may genuinely have dropped
a block from every correct validator's building horizon.

## 5. Witnesses

House rule: every definition and every theorem gets a `decide` instance
before or alongside its proof.

- **Coverage on data** (`Uexcl`): `missingAt` is decidable; compute the
  per-layer coverage of the slot-1 commit's cone — the committed cone
  at round 3 carries all three correct authors at every layer
  (`missingAt = ∅`, better than the `≤ f` bound), and a variant cone
  that genuinely misses one (the exclusion story already provides
  blocks whose cones omit validator 0's half). CQ2's arithmetic at the
  boundary: `f + 1 = 2` of `2f + 1 = 3`.
- **The negative witness — aggregate is not individual.** A universe
  where the same correct validator is missing from every committed
  cone's every layer for as long as the universe runs: three validators
  build on each other, the fourth's blocks arrive but are never
  referenced (asynchrony permits it), commits still occur. This
  witnesses why CQ6 needs `R`, and it is buildable from the §12.1
  quorum-formation example of the report.
- **Inclusion on data**: in `Ugrow` or `Uexcl`, a specific correct
  block's membership in `ledgerSet` after the slot-1 commit, by an
  explicit `Reaches` witness; and the CQ5 composition applied with
  `uexcl_synchronised` at `R = 0`.

## 6. The plan

- **CQP0 — witnesses first** *(no dependencies)*. The coverage
  computations on `Uexcl` and the censorship counter-model; settles
  that `missingAt`, `ledgerSet` membership and the coverage counts all
  `decide`.
- **CQP1 — asynchronous coverage (CQ1–CQ3)** *(after CQP0)*. The
  density packaging: per-commit coverage, the half corollary, the
  cumulative ledger form. Expected to be short — the counting is D25.
- **CQP2 — inclusion (CQ5, CQ6)** *(after CQP0; independent of
  CQP1)*. Backbone composition with L6, then the quantitative bounds
  through L8b, then the pipelined form through the committed-run
  results.
- **CQP3 — the capstone and stretch (CQ7, CQ4)** *(after CQP1,
  CQP2)*. The enforceable-hypotheses packaging; the budgeted
  block-fraction form if its constant is clean.
- **CQP4 — docs** *(last)*. Rewrite this document as a final-state
  record; a chain-quality subsection for the report (§5 or a short
  section after §6, since CQ1–CQ3 are safety-side and CQ5–CQ7
  liveness-side); `related.md` gains the chain-quality/fairness
  literature paragraph.

## 7. Decisions and risks

**Decisions, recorded where they bind:**

- **Coverage counts authors per round, not blocks** (§2): the
  block-count metric is equivocation-deflatable; the author metric is
  what density bounds. CQ4 is the block-count story, gated on the
  budget, and optional.
- **The ledger statement is cumulative** (§3): per-flush deltas overlap
  under pipelining; the cumulative form is monotone, agreed, and
  composes.
- **Cross-arc reuse is read-only**: the arc imports `DoS/Density` and
  `DoS/Exclusion` for D25 and the backbone exactly as GC and Odontoceti
  consume their dependencies — no existing file changes.

**Risks the plan watches:**

- **R1 — `ledgerSet` is a `Set`, not a `Finset`.** Membership witnesses
  on data need explicit `Reaches` terms rather than `decide` on the
  set; if that grates in CQP0, add a decidable bounded form
  (`ledgerSet` restricted to `U.ids` is finite) without touching the
  original.
- **R2 — the CQ6 bound's shape.** L8b's constants are stated against
  `FairWithin`/`BoundedSpacing`; composing them with the backbone's
  `m ≥ R` side conditions may produce an ugly `max(m, R)` expression.
  If so, state the clean form at `R ≤ m` and the general form
  separately rather than forcing one statement.
- **R3 — the censorship counter-model under `Live`.** The negative
  witness needs commits to occur while one correct validator is never
  referenced; `Live.builds` only requires building on *accepted*
  quorums, so this should be constructible, but if `DeliversQuorum`
  forces the fourth validator's blocks into acceptance the model needs
  `held ⊃ accepted` asymmetry — worth checking first in CQP0.
