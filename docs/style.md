# lean-dag — writing style

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Conventions for the documents and the source, derived from the editing
passes that produced them. The rules are few; the examples are the point.

## 1. Register

`report.md` is an academic report. It states results; it does not narrate
the work that produced them.

**Avoid commercial metaphor.** It reads as sales copy and is almost
always less precise than the literal statement.

| Instead of | Write |
|:---|:---|
| this clause is load-bearing | this clause is indispensable to §8 |
| what the stronger committee buys | what the stronger committee yields |
| at the price of `X` | though `X`; at the cost of `X` |
| where the fifth `f` is spent | where the committee of size `5f+1` is required |
| pruning only cheapens blocks | pruning only decreases novelty |
| obtained for free | obtained without further hypotheses |
| mechanisation earns its keep here | the value of mechanisation is concentrated here |

**Avoid figurative verbs and nouns.** A metaphor that has to be decoded
is slower to read than the thing it replaces.

| Instead of | Write |
|:---|:---|
| the assumption would swallow its own conclusion | would presuppose what it is invoked to establish |
| retains the attacker's freight | retains material injected by an adversary |
| the budget paces what an author can inject | limits the rate at which an author can inject material |
| that indexing does the work | that indexing is what carries the argument |
| the two budgets sandwich each other | the two formulations bound each other to within a factor of `f` |
| its engine deserves stating | the mechanism behind it should be stated |
| exclusion does not depend on luck | does not depend on favourable circumstances |
| it just stores more junk | it merely retains more |

**Avoid the laboratory notebook.** The report is not a record of how the
development evolved. Delete, rather than rephrase:

- corrections of earlier drafts — "the correction to §4.3's earlier
  claim", "an earlier version of this development fixed …";
- discovery narration — "turned out", "the surprise", "we found",
  "worth recording", "two things must be said";
- process asides — "this cost a debugging round", "for anyone repeating
  the exercise".

State the final position. If an alternative was considered and rejected,
say so in one clause and give the reason — *"a block-count variant was
considered and rejected: neither route yields an informative ratio"* —
not the history of considering it.

**Permitted, and encouraged.** Established technical metaphor with a
fixed meaning in the field: quorum *intersection*, the correct
*backbone*, a causal *cone*, a sliding *window*, a *horizon*. Honest
negative statements: *"this does not hold before `R`"*, *"a `T`-relative
variant would require a `T`-relative backbone lemma, and is not attempted
here"*. Naming which hypothesis a result consumes, and where.

## 2. Structure

- **Define notation before use.** Global symbols belong in the notation
  table of §2.5; a symbol introduced in one section and used in another
  belongs there too.
- **Every displayed Lean statement is copied from the source** and
  type-checks against the built library. Binders may be elided for
  layout; mark an elision with `…`.
- **Labels** are alphanumeric by area — T, M, L (core), P, N, R (trust
  boundary), CQ, D/C/B, G, O (the arcs) — and must be *introduced where
  the reader first meets them*, not only in the appendix.
- **Tables are left-aligned** (`|:---|`), and carry short cells with the
  explanation in the surrounding prose.
- **Cross-references** use `§n.m`. After renumbering, re-run the audit in
  §4 below; a reference to a section that no longer exists is the most
  common casualty of restructuring.

## 3. The Lean source

- **A witness precedes the theorem.** Every definition is exercised on a
  concrete model by `decide` before anything is proved from it. A
  definition that cannot be witnessed is a definition that may be
  vacuous.
- **Docstrings say why, not what.** The statement already says what.
  Record the design decision, the alternative rejected, and the
  hypothesis that is genuinely consumed.
- **Names**: `X_of_Y` concludes `X` from characteristic hypothesis `Y`;
  a prime marks a post-`R` or incremental variant; a protocol variant
  lives in its own namespace (`Odontoceti.DirectCommit`) rather than
  carrying a suffix.
- **Arcs are additive.** A new development goes in its own directory and
  consumes the core read-only. If it requires a change to the core, that
  is a finding to report, not a refactor to perform quietly.
- **Standard axioms only** — `propext`, `Classical.choice`, `Quot.sound`.
  No `sorry`, no bespoke axioms, no `native_decide`.

## 4. Before committing a document change

Four checks, all cheap:

1. **Cross-references resolve.** Every `§n.m` names a section that
   exists.
2. **Identifiers resolve.** Every backticked Lean name appears in the
   built library. (Both checks are a short script over `report.md` and
   the source; see the audits in the session history of
   `scripts/depgraph.py`, which parses the same appendix.)
3. **Claims are consistent with what was added.** New material commonly
   falsifies an older sentence — a count, a "these two are the whole
   of …", a "two routes" that has become three. Search for the numeral.
4. **Read the render, not the source.** Rebuild with
   `docs/build-pdf.sh` and read the changed pages: clipped captions,
   tables that will not break, and figures too small to read are
   invisible in Markdown.
