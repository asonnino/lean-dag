# lean-dag

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

A Lean 4 + Mathlib formalization of uncertified DAG consensus in the
style of Mysticeti: the DAG itself, the commit rule, and machine-checked
safety and liveness — together with further developments built on the
same foundation, each in its own module consuming the core read-only.
Everything is stated for `n ≥ 3f+1` validators with quorums of size
`n − f`, over pipelined, multi-leader slot schedules.

## What is proved

- **Safety** of the Mysticeti-style commit rule — agreement across
  views and routes, uniqueness of the committed sequence, a monotone and
  agreed ledger — with no network assumption of any kind.
- **Chain quality** (`LeanDag/Quality/`): every commit's flush carries,
  at every round below it, blocks from **at least half of the correct
  validators** — with no synchrony assumption — and once the DAG is
  synchronous, every correct block enters the agreed ledger within a
  schedule-window of its creation; a six-validator counterexample shows
  the aggregate guarantee provably does not imply the individual one.
- **Liveness** above *eventual DAG synchrony*, a structural condition on
  the DAG under which no liveness theorem mentions time. The whole of
  what the network must supply reduces to a single clause of **view
  convergence** — after stabilisation, whatever one correct validator
  holds reaches every correct validator within `Δ` — from which the
  structural condition is derived, and block production with it, rather
  than assumed. The threshold a deployment must meet is the constant
  `2Δ + proc`: no quantity set by deployment appears, because the
  pacemaker's catch-up rule collapses any clock spread to `Δ + proc` in
  one post-stabilisation round. And liveness is **local** — not merely
  that some view commits, but that every reliable validator decides on
  *its own* view, at an explicit time (`commits_recur_local`).
- **Denial-of-service resistance** (`LeanDag/DoS/`): safety is shown
  independent of any anti-equivocation condition; storage is bounded
  under an exposure condition (with a matching construction showing its
  exponential constant is forced) and made linear-forever under an
  enforceable, author-blind **novelty budget** (`dos_resistance`).
- **Garbage collection** (`LeanDag/GC/`): a per-validator horizon below
  which nothing is retained, with commit verdicts invariant across the
  cut, storage **constant** at a lag, bootstrap by an `f+1`-sampled
  attested base — and **no consensus on the cut** anywhere.
- **Odontoceti** (`LeanDag/Odontoceti/`): safety and liveness of the
  two-round commit rule (arXiv:2510.01216), generalized from `n = 5f+1`
  to `n ≥ 5f+1`, on the unmodified DAG layer — including four findings
  about the published safety argument, one of which (agreement among
  indirect commits resting on candidate-iteration order) is refutable
  on data without the canonicity repair the formalization supplies.
- **Reactive schedules** (`LeanDag/Reactive/`): both commit rules remain
  live when validators wait only until they hold the leader's block —
  or, under Mysticeti, until they can certify — with the timeout as a
  fallback. The fast path is quantified: round latency is bounded by
  drift, delivery and processing with the timeout appearing nowhere,
  and when delivery undercuts the timeout no timeout ever fires.
- **Catch-up**, now a clause of the pacing core: drift between
  validators is *preserved*, not contracted, by the waiting rule alone —
  refuted on data — and the pacemaker's second rule (seeing evidence of a
  round is entering it) collapses any spread to `Δ + proc` in a single
  post-stabilisation round, whatever it was before; a witness starts with
  a spread of ten and collapses to exactly three. A valid block cannot
  outrun the honest schedule, so the author-blind rule a deployment runs
  is safe (`exists_honest_floor`).
- **The view a validator holds** (`LeanDag/PaceDelivery.lean`): the
  commit rules are view-relative and the pacing line reasons about
  time-indexed holdings; the two are now joined. A validator's holdings
  *are* a view (`viewAt_ids`), which is what makes liveness local; and a
  pacing structure **induces** a delivery layer, so the storage model of
  the DoS arc is derived rather than postulated — including its
  acceptance rule, at most one block per author, which follows from the
  reference discipline (`heldOf_inj`). One structure plus the acceptance
  budget then yields liveness and linear storage together
  (`dos_resistance_of_pace`).
- **Safe Skip** (`LeanDag/SafeSkip/`): a crashed validator rejoins with
  **one constant-size message** denoting a block for every missed round —
  a donor's references plus the self reference the validity rules force.
  The fill is proved a block universe extending the old one unchanged;
  production is restored at every missed round, a filled leader
  candidate is directly skipped rather than committed, and every verdict
  reached before the fill re-derives and agrees after it
  (`decided_fill_agree`).
- **Adaptive leaders** (`LeanDag/Adaptive/`): a Hammerhead-style
  schedule — the leaders ahead recomputed from the agreed prefix, to
  favour validators observed live — proved safe and live for **both**
  commit rules. Safety is unconditional: the schedule-and-verdict
  fixpoint is unique under **no synchrony or fairness hypothesis**, for
  arbitrary adapted policies (`adaptiveRun_agree`); liveness is its
  existence under one clause — the policy keeps placing runs of
  reliable leaders (`adaptiveRun_exists`); and the layer is
  rule-agnostic, the two-round mirror consuming the same policy
  objects.
- **Hybrid fault tolerance** (`LeanDag/Hybrid/`): the two-round rule
  proved safe and live under **separate Byzantine and crash caps** —
  `fb` equivocators, `fc` honest validators that may halt — at
  Orcaella's bound `n ≥ 5·fb + 3·fc + 1` (arXiv:2607.04789), for every
  indirect threshold in an admissible interval whose nonemptiness *is*
  the committee bound. Four validators suffice for two-round finality
  under a single crash, where Byzantine tolerance costs six; at
  `fc = 0` the development collapses onto Odontoceti. The bound is
  also proved **necessary**: one validator short, one view derives
  conflicting verdicts at every threshold
  (`hybrid_bound_necessary`).
- **Integration** (`LeanDag/Integration/`): the arcs are proved to
  **compose** — not by settling a quadratic matrix, but by naming the
  invariants each consumes and proving the two universe transformers
  preserve them, after which a validator running four mechanisms at
  once still cannot disagree about a verdict (`hybrid_agree_stack`).
  The deployment constraints only the composition reveals: garbage
  collection at lag `Λ` supports one-message recovery from outages of
  up to `Λ` rounds and no more; a horizon must fall on an epoch
  boundary of an adaptive schedule; and a validator pruned past its own
  history can read but not produce until it **re-genesises** — a
  provision that needs no exemption from the self-parent rule and no
  agreement on where anyone's cut falls.

Every definition is exercised on concrete models by `decide` before
anything is proved from it, and every principal result depends on
exactly Lean's three standard axioms (`propext`, `Classical.choice`,
`Quot.sound`) — no `sorry`, no bespoke axioms, no `native_decide`.

## Building

```
lake build
```

Requires [elan](https://github.com/leanprover/elan). The toolchain version
is pinned in `lean-toolchain`; `lake build` will fetch it automatically.

## Layout

- `LeanDag/` — theorem/definition source: the core DAG and Mysticeti
  development at the top level, with the pacing structures in
  `ViewPace.lean` and the delivery layer they induce in
  `PaceDelivery.lean`, and the arcs in subdirectories (`Quality/` —
  chain quality; `DoS/` — equivocation and the novelty budget; `GC/` —
  garbage collection; `Odontoceti/` — the two-round protocol;
  `Reactive/` — the reactive schedule; `SafeSkip/` — crash recovery in
  one message; `Adaptive/` — adaptive leader schedules; `Hybrid/` —
  Byzantine and crash faults apart; `Network/` — the composed
  denial-of-service capstones; `Integration/` — how the arcs compose).
- `LeanDag.lean` — root import file.
- `LeanDagTest/` — `decide` witnesses and concrete models, mirroring the
  same layout.
- `docs/` — the design records and the report. `docs/build-pdf.sh`
  compiles them to `docs/pdf/` — requires `pandoc` and `typst`
  (`brew install pandoc typst`).
- `scripts/` — the extraction and verification pipeline. `DepGraph.lean`
  and `depgraph.py` extract and draw the support diagrams
  (`docs/depgraph/README.md`); `svg2pdf.sh` renders them to PDF;
  `extract-decls.py` reads every declaration with its docstring and
  statement, and `gen-reference.py` regenerates the report's reference
  appendices from it; `audit-report.py` checks the report's
  cross-references, its Lean identifiers, and every displayed statement
  verbatim against the compiled source. Regeneration is deterministic,
  so regenerate-and-diff is the pre-merge check.

## Documents

| Document | Contents |
|---|---|
| [`docs/report.md`](docs/report.md) | **the entry point**: the full report — model, commit rule, trust boundary (including what the adversary may do), safety, liveness on view convergence, the extension arcs, satisfiability, mechanisation — plus generated reference appendices giving **every definition and public theorem verbatim** and an index of the internal lemmas |
| [`docs/spec.md`](docs/spec.md) | the safety design record |
| [`docs/liveness.md`](docs/liveness.md) | the liveness design record, and eventual DAG synchrony |
| [`docs/liveness-routes.md`](docs/liveness-routes.md) | why one liveness route was kept and the others deleted, and what the later clause changes cost |
| [`docs/pipelining-and-multi-leader.md`](docs/pipelining-and-multi-leader.md) | the schedule generalization: eligibility, runs, pipelined commits |
| [`docs/chain-quality.md`](docs/chain-quality.md) | chain quality: coverage without synchrony, inclusion with it |
| [`docs/dos-equivocation-and-growth.md`](docs/dos-equivocation-and-growth.md) | equivocation, exposure, view growth, and the novelty budget |
| [`docs/garbage.md`](docs/garbage.md) | the horizon: truncation, bounded storage, bootstrap without consensus |
| [`docs/odontoceti.md`](docs/odontoceti.md) | the two-round protocol: the generalized thresholds, and the findings |
| [`docs/adaptive-leaders.md`](docs/adaptive-leaders.md) | adaptive leader schedules: the design record and theorem plan |
| [`docs/hybrid-plan.md`](docs/hybrid-plan.md) | hybrid fault tolerance: the design record and theorem plan |
| [`docs/integration.md`](docs/integration.md) | composing the arcs: the invariant interface, and what composition revealed |
| [`docs/related.md`](docs/related.md) | a survey of consensus on uncertified DAGs |
| [`docs/style.md`](docs/style.md) | writing conventions for the documents and the source |

## License

MIT — see [`LICENSE`](LICENSE).
