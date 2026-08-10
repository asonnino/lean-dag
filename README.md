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
  structural condition is derived three ways and block production is
  derived rather than assumed. Quantitative forms give the wait
  threshold (a correct leader commits once correct validators wait
  `D₀ + Δ`, `2Δ` under a common start). The quorum-based alternative N1
  is retained in `LeanDag/Network/`, which nothing else imports.
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
- **Catch-up** (`LeanDag/Drift/`): drift between validators is
  *preserved*, not contracted, by the standard build rules — refuted on
  data — and one further clause (seeing evidence of a round is entering
  it) collapses any start spread to `Δ + proc` in a single post-GST
  round, making the commit threshold `2Δ + proc` with no deployment
  assumption; a witness starts with a spread of ten and collapses to
  exactly three.

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
  development at the top level, with `Network/` holding the quorum-based
  network assumption kept out of the main line, and the arcs in subdirectories
  (`Quality/` — chain quality; `DoS/` — equivocation and the novelty
  budget; `GC/` — garbage collection; `Odontoceti/` — the two-round
  protocol; `Reactive/` — the reactive schedule; `Drift/` — catch-up
  and the start spread).
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
| [`docs/report.md`](docs/report.md) | **the entry point**: the full report — model, commit rule, trust boundary (including what the adversary may do), safety, liveness on view convergence, the five arcs, satisfiability, mechanisation — plus generated reference appendices giving **every definition and public theorem verbatim** and an index of the internal lemmas |
| [`docs/spec.md`](docs/spec.md) | the safety design record |
| [`docs/liveness.md`](docs/liveness.md) | the liveness design record, and eventual DAG synchrony |
| [`docs/pipelining-and-multi-leader.md`](docs/pipelining-and-multi-leader.md) | the schedule generalization: eligibility, runs, pipelined commits |
| [`docs/chain-quality.md`](docs/chain-quality.md) | chain quality: coverage without synchrony, inclusion with it |
| [`docs/dos-equivocation-and-growth.md`](docs/dos-equivocation-and-growth.md) | equivocation, exposure, view growth, and the novelty budget |
| [`docs/garbage.md`](docs/garbage.md) | the horizon: truncation, bounded storage, bootstrap without consensus |
| [`docs/odontoceti.md`](docs/odontoceti.md) | the two-round protocol: the generalized thresholds, and the findings |
| [`docs/related.md`](docs/related.md) | a survey of consensus on uncertified DAGs |
| [`docs/style.md`](docs/style.md) | writing conventions for the documents and the source |

## License

MIT — see [`LICENSE`](LICENSE).
