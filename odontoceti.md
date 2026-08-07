# lean-dag — Odontoceti: two-round commitment, formalized

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Design notes and plan for formalizing **Odontoceti** — the first DAG
protocol to commit in **two** communication rounds:

> P. Vander Vos (supervised by P. Jovanovic and A. Sonnino). *Odontoceti:
> Ultra-Fast DAG Consensus with Two Round Commitment.* MSc thesis,
> arXiv:2510.01216, 2025.

Goal: machine-checked **safety** and **liveness** of the two-round
decision rule, in a new directory `LeanDag/Odontoceti/` (witnesses in
`LeanDagTest/Odontoceti/`), reusing the existing DAG development
wherever it applies and building only the rule layer fresh. Results use
**O**-labels, continuing the house scheme; plan phases are OP0–OP5.

> **Status: proved and witnessed, with one finding.** The arithmetic
> core O1/O1′/O2/O3/O4′ (`Rules.lean`), the decision relation with
> agreement O5/O6 (`Decision.lean`, `decided_unique`/`safety`), and
> liveness O7–O10 (`Liveness.lean`, through
> `all_decided_below_of_fairRun`) are all proved at the generalized
> thresholds `n ≥ 5f+1`, `n−f`, `n−3f` — the generalization held, no
> fallback needed — and witnessed by `decide` at the boundary
> `n = 6, f = 1` (`LeanDagTest/Odontoceti/Model.lean`): the sunny-day
> universe, a direct skip, an indirect commit with `ThickLink` at
> exactly the threshold, an indirect skip, and O7/O8/O9 applied.
> **The finding**: risk R2's worry was real. The thesis's Lemma 5
> proof asserts "same anchor ⇒ same decision", but no counting
> argument separates two equivocating candidates that both pass the
> indirect test at one anchor — `utwin6_both_pass` realises that
> configuration on data — so agreement genuinely rests on the
> implementation's candidate-iteration order. The formalized
> `indirectCommit` therefore carries a **canonicity premise** (commit
> the `≤`-least passing candidate, `[LinearOrder BlockId]` = hash
> order in practice), under which O5 closes; the O4′ counting lemma
> (`n−f + n−3f − f > n` at `n ≥ 5f+1`) covers every *other* crossing,
> so canonicity is needed exactly where the thesis was silent.
> Remaining: OP5's final-state rewrite of this document.

## 1. The protocol, in our vocabulary

Odontoceti runs `n = 5f+1` validators on an **uncertified** structured
DAG. Per round, each block carries `4f+1` references to distinct-author
blocks of the previous round, the first being the author's own previous
block (mandatory self-parent). Waves are **two rounds long** and
pipelined — every round proposes leaders (between 1 and `4f+1` per
round, ranked, round-robin), and the wave proposing at round `r`
decides at round `r+1`:

- A round-`(r+1)` block **supports** a leader block `L` at `r` if it
  references `L` as a parent, and **blames** it otherwise. Support and
  blame are *direct-parent* facts — there is no certificate round.
- **Direct commit**: `4f+1` distinct authors support `L` at `r+1`.
- **Direct skip**: `4f+1` distinct authors blame `L` at `r+1`.
- **Indirect rule**: an undecided leader looks for an **anchor** — the
  first (in rank order) committed-or-undecided leader at rounds
  `≥ r+2`; if the anchor is undecided, the leader stays undecided; if
  committed, the leader commits iff the anchor's causal history
  contains **`2f+1` supports** for it, else skips.
- Leader equivocation is handled per candidate block: every block
  authored by the slot's leader is evaluated against the same rule.

Liveness is partial-synchrony-standard: after GST, a `2Δ` proposal
timeout makes every honest round-`(r+1)` block reference an honest
leader's round-`r` block, so honest leaders commit **directly**; a
round-robin argument supplies two consecutive honest top-ranked leaders
in every window of `2f+2` rounds, and anchoring then clears every
undecided slot below. (A "slow-participant" early-production
optimisation — produce early after `2f+1` blames — accelerates the
crash case; it is a network-layer optimisation and out of scope here,
like all timeout machinery, exactly as in the Mysticeti development.)

## 2. The reuse boundary — and one pleasant surprise

**The surprise: Odontoceti's quorums are `n − f`.** At `n = 5f+1`, the
DAG quorum `4f+1` *is* `n − f`, the direct-commit and direct-skip
thresholds *are* `n − f`, and our development is already parameterised
at exactly that shape: `Faults` demands only `3f+1 ≤ n`, and every
quorum in `BlockUniverse.valid`, the support layer, and the delivery
layer is literally `Fintype.card Validator − F.f`. (`related.md` §4.2
currently claims Odontoceti's quorums are *not* `n − f`; that is wrong
and OP5 corrects it.) Consequently:

**The hard constraint, stated up front: the DAG theorems do not
change.** Nothing outside `LeanDag/Odontoceti/` and
`LeanDagTest/Odontoceti/` is modified — no definition, no theorem, no
generalization pass over existing files. The commit rule is *redefined*
in the new directory and its safety and liveness proved there; the DAG
layer is consumed as-is. (The only file touched elsewhere is
`related.md`, prose.) This is the same additive discipline the GC arc
kept, and the quorum observation above is what makes it possible at
zero cost.

**Reused verbatim — the entire DAG layer.** `Block`, `BlockUniverse`
(all four validity clauses match Odontoceti's: `predecessor`,
`distinct_creators`, `quorum` at `n − f`, `self_parent` — the thesis
mandates the self-parent we added as S10), `View`, `history`/cones,
`supporters`/`blames` (**these are Odontoceti's support/blame,
already defined**), `creatorsOf`, the counting layer, `Slots`
(`uniform 1 m` is precisely the pipelined multi-leader ranked
schedule; since the new rule layer is slot-indexed through `Slots`
exactly as Mysticeti's is, multi-leader support is free — witnesses
run single-leader, theorems are schedule-generic), `IsLeaderBlock`,
`Delivery`/`viewUpto`, `Populated`/`Synchronised`/
`EventuallyDelivers`/`DeliversQuorum`/`Live`, the backbone lemma, the
common core, and `FairRunOn` (schedule-only, no eligibility in its
statement). The DoS/novelty-budget and GC layers apply to any
universe, hence to these too, but are not this arc's concern.

**Mirrored, not reused — the eligibility-indexed liveness
combinatorics.** `SpansEligible` mentions Mysticeti's `Eligible`, and
`decided_of_first_eligible_commit` / `decided_of_committed_above`
/ `decided_below_of_committed_run` / `all_decided_below_of_fairRun` are
inductions over Mysticeti's `Decided` constructors. Their Odontoceti
analogues are re-proved in the new directory with the same proof
shapes; the reuse is of the *template*, not the theorem. (A
rule-parameterised refactor of `Decided` would let them be literally
shared — rejected here because it would rewrite `Mysticeti.lean`,
violating the constraint above.)

**New — the fault bound and the rule layer.**

- `Faults5` — a class extending `Faults` with `5f+1 ≤ n`. Extension,
  not replacement: a `Faults5` instance *is* a `Faults` instance, so
  every existing theorem applies to the same types unchanged, and the
  new theorems take the stronger bound only where the two-round
  arithmetic needs it.
- The two-round decision rule: `DirectCommit5`, `DirectSkip5`,
  `decisionRound5 = slotRound + 1`, `Eligible5`, the indirect test
  `ThickLink`, and the decision relation `Decided5` — parallel
  definitions in `LeanDag/Odontoceti/`, mirroring the *shape* of the
  Mysticeti layer (whose `decisionRound` deliberately isolates the
  wavelength: here that one definition changes from `+2` to `+1`).
  Nothing in `LeanDag/` outside the new directory is modified.

## 3. The rule layer, and the generalization we will prove

The thesis fixes `n = 5f+1` exactly. **Decided: we formalize the
natural generalization**, in house style — `n ≥ 5f+1` with quorum
`q := n − f`, direct thresholds `n − f`, indirect threshold `n − 3f` —
which specializes to the paper's constants at the boundary. (If some
lemma resists the general form, pinning `n = 5f+1` is the recorded
fallback; the boundary witnesses are unaffected either way.)

A naming decision, made here: the new definitions live in
`namespace LeanDag.Odontoceti` under their **plain names**
(`Odontoceti.DirectCommit`, `Odontoceti.Eligible`,
`Odontoceti.Decided`, …) — no `5`-suffixes in the code; qualification
disambiguates from the Mysticeti layer, which stays in the root
namespace untouched. This document writes `DirectCommit5` etc. only as
prose shorthand.

```lean
namespace Odontoceti

class Faults5 (Validator : Type*) [Fintype Validator] extends Faults Validator where
  card_validators5 : 5 * f + 1 ≤ Fintype.card Validator

-- supports/blames: already `supporters U L (r+1)`, `blames U L (r+1)`

def DirectCommit (U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (supporters U L (r + 1)).card

def DirectSkip (U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (blames U L (r + 1)).card

def decisionRound (k : ℕ) : ℕ := S.slotRound k + 1
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j

/-- The indirect test: supports for `L` at its decision round, visible
in the anchor's cone, counted by distinct authors. -/
def ThickLink (U) (A L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - 3 * F.f) ≤
    (creatorsOf U.block
      ((blocksAt U (r + 1)).filter
        (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A))).card

end Odontoceti
```

with `Decided5` an inductive mirroring `Decided` constructor for
constructor — direct commit, direct skip (quantified over all candidate
leader blocks), indirect commit and indirect skip through the nearest
eligible anchor, the intermediate premise stated positively over
eligible slots, exactly the idiom that made M6 provable.

**Why these thresholds generalize (the arithmetic core, three facts):**

- **Commit vs skip** (O1): `|supporters| ≥ q` and `|blames| ≥ q` force
  `|supporters ∩ blames| ≥ 2q − n = n − 2f ≥ f+1` authors who both
  supported and blamed — each has two round-`(r+1)` blocks, so all are
  equivocators, but there are at most `f`. Contradiction. (Needs only
  `n ≥ 3f+1` — the two-round rule's commit-vs-skip safety is not where
  the stronger committee is spent.)
- **Support propagation** (O3, the heart): if `q` distinct authors
  support `L` at `r+1`, then **every** block at rounds `≥ r+2` carries
  at least `n − 3f` of those support blocks in its cone. One hop: a
  round-`(r+2)` block references `q` distinct-author parents, whose
  authors meet the supporter set in `≥ 2q − n = n − 2f` authors; up to
  `f` of those are Byzantine equivocators whose *referenced* block may
  be a non-supporting twin, leaving `≥ n − 3f` genuine support blocks
  (honest authors' round-`(r+1)` blocks are unique). Deeper rounds:
  cones are monotone through any single parent, so the `n − 3f` bound
  propagates by induction. At `n = 5f+1` this is the thesis's
  `2f+1`.
- **Skip vs indirect commit** (O2): if `L` is directly skipped, its
  supporters — anywhere, hence in any cone — number `≤ 2f` authors,
  and `2f < n − 3f` exactly when `n ≥ 5f+1`. **This is where the
  fifth `f` is spent**, and why the indirect threshold `n − 3f` is
  forced from both sides: propagation supplies `≥ n − 3f`, a skipped
  leader can muster `≤ 2f < n − 3f`. At the boundary the window is
  exactly `{2f+1}`.

  An arithmetic trap here, found in review and worth pinning before
  the proof is attempted: the honest-supporter bound needs the
  **exact complement identity** `|Correct| = n − |byzantine|`, not
  the usual inequality `|Correct| ≥ n − f`. The correct chain:
  correct supporters and correct blamers are disjoint
  (`no_equivocation` — one block per correct author per round, and it
  either references `L` or not), correct blamers number
  `≥ |blames| − |byzantine| ≥ (n−f) − |byzantine|`, so correct
  supporters number
  `≤ (n − |byzantine|) − ((n−f) − |byzantine|) = f` — the
  `|byzantine|` cancels — and total supporters `≤ f + f = 2f`. Bound
  `|Correct|` by `n` instead and the estimate degrades to `3f`, which
  is **not** below `n − 3f` at the boundary: the naive bounding
  fails, the exact one works, and `Correct` being defined as the
  literal complement is what makes it available.

**Decided: `ThickLink` counts distinct authors of in-cone support
blocks**, not raw blocks. The thesis says "2f+1 supports in the history
of the anchor" without disambiguating; an equivocating supporter could
plant many support-twins in one cone, so the block count is inflatable
by the adversary and the author count is the one both O2 (`≤ 2f`
authors) and O3 (`≥ n − 3f` authors) actually bound. Should a closer
reading of the thesis's algorithm turn out to intend raw blocks, the
formalization is the arbiter: O2/O3 will say which count is *provable*,
and the author count is the one we expect to survive.

## 4. Safety plan

Mirroring the thesis's Section 5.1 (Lemmas 1–6), with the M-series
proofs as templates:

- **O1 (commit vs skip; thesis Lemma 1).** No leader block is directly
  committed by one view and directly skipped by another. Views only
  under-report (`DirectCommitIn5 → DirectCommit5`, as with the
  Mysticeti view layer), so this is universe-level counting: the
  `n − 2f ≥ f+1` equivocator argument above. Proof route: an author in
  `supporters ∩ blames` has two distinct round-`(r+1)` blocks (their
  reference sets differ on `L`), so by `no_equivocation` it is not
  correct — `supporters ∩ blames ⊆ byzantine`, whose card is `≤ f`.
  Needs only `n ≥ 3f+1`.
- **O1′ (twin uniqueness; M5 analogue).** Two directly committed
  blocks of one slot are equal: their supporter sets meet in
  `n − 2f ≥ f+1` authors, each supporting two same-author round-`r`
  blocks — but `distinct_creators` forbids one block referencing both
  twins, so the intersection authors are equivocators; at most `f`.
  The thesis leaves this implicit inside `GetLeaderBlocks`; we state
  it, because M6's proof needs it explicitly.
- **O2 (skip vs indirect commit; thesis Lemma 2).** A directly skipped
  leader fails `ThickLink` for every anchor: the `≤ 2f < n − 3f`
  count.
- **O3 (propagation; thesis Lemma 3).** As in §3. This is the
  two-round replacement for Mysticeti's M2/M4 ("every anchor finds the
  certificate"): here every anchor's cone *is* the certificate. Two
  precisions the induction rests on: the one-hop bound holds for
  **every** block of the universe, Byzantine-authored included —
  validity is structural (`n − f` distinct-author parents), so no
  honesty enters the argument; and the inductive step is pure cone
  monotonicity — a round-`(m+1)` block has at least one round-`m`
  parent (the quorum clause), and `H(parent) ⊆ H(block)` carries the
  same `n − 3f` support blocks upward, so the bound never decays with
  depth.
- **O4 (commit vs indirect skip; thesis Corollary 4).** A directly
  committed leader passes `ThickLink` for every eligible anchor — O3
  read at the anchor.
- **O5 (agreement; thesis Lemma 5 / our M6 analogue).**
  `decided5_unique`: no two views decide one slot differently,
  whatever routes they took. Structural induction on the first
  derivation, mirroring `decided_unique` case for case: the
  direct/direct diagonal closes by O1/O1′, the direct/indirect
  crossings by O2/O3/O4, and the one real case — indirect commit vs
  indirect skip — by the anchor trichotomy, which is why `Eligible5`
  must be a predicate on the slot pair alone and the intermediate
  premise must be stated positively. The M6 proof survived one
  wavelength change already (the `decisionRound` indirection); this is
  the second.
- **O6 (safety).** The package statement, quoting O5.

The equivocation story needs no new mechanism: candidate quantification
(`IsLeaderBlock` reused with the new schedule) plus O1′ covers
equivocating leaders, and O3's twin discount covers equivocating
supporters. `no_equivocation` constrains correct authors only, exactly
as the thesis assumes.

## 5. Liveness plan

- **O7 (honest leaders commit directly; thesis Lemma 8 + Corollary
  9).** Post-`R`, `Synchronised` makes every correct round-`(r+1)`
  block reference every correct round-`r` block — so a correct
  leader's supporters include all of `Correct`, and
  `|Correct| ≥ n − f = q` commits it. **Two populated rounds (propose
  and decide) and one synchronised step** — the Mysticeti analogue
  (`L4`, `decided_of_leader_mem`) needed three populated rounds; the
  two-round rule's liveness is *simpler*, which is the protocol's
  whole point.
- **O8 (the run spans eligibility).** With pipelined waves,
  `Eligible5 k j ⟺ slotRound k + 2 ≤ slotRound j`, so — as in
  Mysticeti's pipelined case — a slot cannot anchor on the slot
  immediately above it, and single commits do not clear backlogs: it
  takes **two consecutive** committed rounds (thesis Lemma 10's "two
  consecutive honest top-ranked leaders" is exactly this). The
  spanning arithmetic checks out at `c = 2`: for a run committing
  rounds `x` and `x+1` and any slot `k` below the run, either
  `slotRound k ≤ x − 2` (round `x` is eligible) or
  `slotRound k = x − 1` (round `x` is one too close, but `x+1`
  clears `slotRound k + 2`) — every slot below sees an eligible
  committed anchor inside the run. Proved as the `Eligible5` version
  of `SpansEligible` at `c = 2`, feeding O9's run lemma.
- **O9 (undecided slots clear; thesis Lemma 11).** *Not* the plain L8
  analogue: L8 (`decided_of_committed_above`) assumes every later slot
  may anchor an earlier one, which **fails pipelined** — under
  `Eligible5` a slot cannot anchor on the round immediately above it,
  exactly as in pipelined Mysticeti. The right templates are
  `decided_of_first_eligible_commit` (single-slot resolution through
  the *first* eligible committed anchor, whose intermediate premise is
  vacuous) and `decided_below_of_committed_run` (a run of `c`
  consecutive committed slots clears everything below, given
  `SpansEligible c`) — both re-proved for `Decided5`.
- **O10 (liveness; thesis Theorem 12 / our L10 analogue).**
  `all_decided5_below_of_fairRun`: under `Live`, `DeliversQuorum`,
  `Synchronised R` and a fair run of length 2, every slot below a
  post-`R` committed run is decided. Composition of O7 + O8 + O9
  through the existing `FairRunOn` machinery.

**Decided: the schedule fact is hypothesized, not derived.** The
liveness theorems take a `FairRunOn`-style hypothesis — *runs of two
consecutive correct-led slots recur* — exactly as the Mysticeti
liveness does. The thesis derives this from its round-robin schedule
(Lemma 10's `2f+2`-window argument); that derivation is a statement
about one concrete schedule, is strictly separable from the consensus
argument, and stays out of the core plan. If wanted later, it is a
self-contained lemma about `uniform 1 m` with a rotating `elect`,
touching nothing else.

Out of scope, recorded: the `2Δ` timeout and the early-production
optimisation (network layer, as always — `Delivery` and
`EventuallyDelivers` are where their effects enter the model), and
message complexity/latency claims (performance, not correctness).

## 6. Witnesses

House rule: every definition gets a `decide` witness before anything is
proved from it. The boundary instance is pleasantly small: `f = 1`,
`n = 6` — `Validator = Fin 6`, Byzantine `{0}`, quorum `n − f = 5`,
indirect threshold `n − 3f = 3`.

- **`Uodo`** — the base model: `Fin 6`, rounds 0–3, six blocks per
  round (`Fin 24` ids), every block referencing 5 distinct-author
  parents with self-parent first. Schedule `uniformSingle 1` (one
  leader per round, pipelined — rank structure enters later if at
  all). Witnesses: validity by `decide`; `DirectCommit5` for the
  round-1 leader from its 5 round-2 supporters; `Decided5` slot
  verdicts by constructor + `decide`.
- **A skip witness**: a leader whose block 5 authors decline to
  reference (blames at `n − f`), directly skipped; then an indirect
  witness: an undecided middle slot resolved through a committed
  anchor two rounds up, `ThickLink` computed by `decide` — and the
  negative: a skipped leader failing `ThickLink` against the same
  anchor.
- **An equivocation witness**: leader 0 with twins at one round;
  neither twin reaches `q` supports (O1′ on data); a Byzantine
  supporter with twins showing the O3 discount is real — the anchor's
  cone holding the non-supporting twin, the author-count still
  clearing `n − 3f`.
- **Liveness on data**: `Populated`/`Synchronised` instances for
  `Uodo` and O7 applied to commit the round-1 leader; a two-round
  committed run clearing an earlier undecided slot (O9 applied).

`decide` feasibility matches earlier models (`Uexcl` is `Fin 20` over
`Fin 4`; `Fin 24` over `Fin 6` with quorum-5 reference sets is the same
order of work; `maxRecDepth 400000` as needed).

## 7. The plan

- **OP0 — model and witnesses first** *(no dependencies)*. `Faults5`
  (instance for `Fin 6`), `Uodo`, validity by `decide`. Settles that
  the existing `BlockUniverse` really does accept the Odontoceti
  parameters with no changes — the reuse claim of §2 as a computation.
- **OP1 — the rule layer** *(after OP0)*. `DirectCommit5`,
  `DirectSkip5`, `decisionRound5`/`Eligible5`, `ThickLink`,
  decidability instances, witnesses for each; the arithmetic core as
  three standalone counting lemmas (the §3 facts), each with a
  boundary witness at `n = 6, f = 1`.
- **OP2 — propagation (O3)** *(after OP1; the heart)*. The one-hop
  intersection-minus-twins argument, then cone-monotone induction.
  Risk lives here: the twin discount needs the support *blocks* (not
  just authors) tracked through the induction — if the author-counting
  formulation fights the induction, the fallback is to carry the
  support-block set explicitly and count authors at the end.
- **OP3 — the decision relation and agreement (O1, O1′, O2, O4, O5,
  O6)** *(after OP2)*. `Decided5` with the view layer
  (`DirectCommitIn5`/`DirectSkipIn5`, monotone into universe level),
  then `decided5_unique` by the M6 template.
- **OP4 — liveness (O7–O10)** *(after OP1; O9/O10 after OP3)*. The
  one-step L4 analogue; the `Eligible` version of `SpansEligible` at
  `c = 2`; the first-eligible-commit and committed-run lemmas for the
  new `Decided`; the composed L10 analogue with the hypothesized run.
- **OP5 — docs** *(last)*. Rewrite this document as a final-state
  record (house pattern); correct `related.md` §4.2's quorum claim and
  point it here; a paragraph on what the generalization `n ≥ 5f+1`
  says that the thesis's fixed `5f+1` does not.

## 8. Decisions and risks

**Decisions, recorded where they bind:**

- **The generalization** (§3): prove `n ≥ 5f+1` with thresholds
  `n − f` / `n − 3f`; pinning `n = 5f+1` is the fallback if a lemma
  resists.
- **`ThickLink` counts distinct authors** (§3): the
  adversary-inflatable block count is rejected; the safety lemmas are
  the arbiter if the thesis intended otherwise.
- **The schedule fact is hypothesized** (§5): liveness takes the
  run-recurrence hypothesis in house style; deriving it from
  round-robin is separable, optional, and out of the core plan.
- **Naming** (§3): `namespace LeanDag.Odontoceti`, plain names.
- **The DAG layer is read-only** (§2): the commit rule is redefined in
  the new directory; nothing outside it changes, and the
  rule-parameterised-`Decided` refactor that would have shared the
  liveness combinatorics is rejected on those grounds.

**Risks the plan watches:**

- **R1 — anchor order within a round.** The thesis ranks leaders and
  searches "highest to lowest" from round `r+2`. Our `Decided` idiom
  ranges the anchor and the intermediate premise over *slot indices*
  with eligibility on pairs, which under `uniform 1 m` encodes
  (round, rank) lexicographically — the plan assumes this encoding
  suffices, as it did for pipelined Mysticeti. If the rank order
  within the *starting* round matters in a way slot order does not
  capture, O5's trichotomy will surface it.
- **R2 — undecided anchors.** "First committed *or undecided*" — an
  undecided anchor blocks the search rather than being passed over.
  This is exactly the positive-intermediate-premise idiom of
  `Decided`; the plan assumes the same inductive shape carries it,
  and O5's induction is where a mismatch would show.
- **R3 — the O3 induction's bookkeeping** (also flagged at OP2): the
  twin discount needs support *blocks* tracked through the induction
  with authors counted at the end; if the author-first formulation
  fights the induction, carry the block set explicitly.
