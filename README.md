# lean-dag

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

A Lean 4 + Mathlib formalization of uncertified DAG consensus in the
style of Mysticeti: the DAG itself, the commit rule, and machine-checked
safety and liveness — together with three further developments built on
the same foundation. Everything is stated for `n ≥ 3f+1` validators with
quorums of size `n − f`, over pipelined, multi-leader slot schedules.

## What is proved

- **Safety** of the Mysticeti-style commit rule — agreement across
  views and routes, uniqueness of the committed sequence, a monotone and
  agreed ledger — with no network assumption of any kind.
- **Liveness** above *eventual DAG synchrony*, a structural condition on
  the DAG under which no liveness theorem mentions time; the condition
  is then **derived** twice, from an abstract delivery model and from
  GST, with quantitative forms (a correct leader commits once correct
  validators wait `2Δ`).
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
  development at the top level, with the three arcs in subdirectories
  (`DoS/` — equivocation and the novelty budget; `GC/` — garbage
  collection; `Odontoceti/` — the two-round protocol).
- `LeanDag.lean` — root import file.
- `LeanDagTest/` — `decide` witnesses and concrete models, mirroring the
  same layout.
- `docs/` — the design records and the report. `docs/build-pdf.sh`
  compiles them to `docs/pdf/` — requires `pandoc` and `typst`
  (`brew install pandoc typst`).

## Documents

| Document | Contents |
|---|---|
| [`docs/report-outline.md`](docs/report-outline.md) | **the entry point**: the full report — model, commit rule, trust boundary, safety, liveness, the three arcs, satisfiability, statement index |
| [`docs/spec.md`](docs/spec.md) | the safety design record |
| [`docs/liveness.md`](docs/liveness.md) | the liveness design record, and eventual DAG synchrony |
| [`docs/pipelining-and-multi-leader.md`](docs/pipelining-and-multi-leader.md) | the schedule generalization: eligibility, runs, pipelined commits |
| [`docs/dos-equivocation-and-growth.md`](docs/dos-equivocation-and-growth.md) | equivocation, exposure, view growth, and the novelty budget |
| [`docs/garbage.md`](docs/garbage.md) | the horizon: truncation, bounded storage, bootstrap without consensus |
| [`docs/odontoceti.md`](docs/odontoceti.md) | the two-round protocol: the generalized thresholds, and the findings |
| [`docs/related.md`](docs/related.md) | a survey of consensus on uncertified DAGs |
