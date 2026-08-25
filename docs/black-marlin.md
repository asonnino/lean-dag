# Black Marlin: the commit rule

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

The design record for `LeanDag/BlackMarlin/`: the commit rule of *DAG it
off: Latency Prefers No Common Coins* (Amores-Sesar, Grøndal, Holmgård
and Ottendal, arXiv:2508.14716v3): its safety, its liveness, the round
rule it advances on, Definition 1's Agreement, and the order its
deliveries come out in.

## 1. The protocol, and what this arc covers

Black Marlin is a partially synchronous DAG protocol at `n ≥ 3f + 1`
with neither reliable broadcast nor a common coin. It elects one
**anchor** per round by round robin, and it commits three rounds after
proposal. A round advances when a validator holds blocks from `n − f`
parties, has the anchor of the round, and sees the two anchors below it
supported; a timeout supplies the second disjunct when an anchor is
Byzantine, which is what keeps the protocol responsive.

This arc covers the commit rule of `delivery(r)` (Algorithm 2, L14–L17)
with §5.1's safety results (§4), liveness above the structural condition
in place of §5.2's timing argument (§8), the round rule of L38–L41 and
the responsiveness it yields (§9), Definition 1's Agreement (§10), and
the order the descent of `commit` delivers in (§11). §12 says what
remains.

## 2. The rule

Write `supp(B)` for the number of distinct validators whose block at
round `round(B) + 1` references `B`. The anchor `B` of round `r` is
committed when

1. `supp(B) ≥ n − f`, and
2. some anchor `B′` of round `r + 1` references `B` and has
   `supp(B′) ≥ n − f`.

In the source these are `Supported U L r` and `Linked U L r`, and their
conjunction with `IsAnchor U r L` is `Committed U L r`
(`LeanDag/BlackMarlin/Model/Rules.lean`). No threshold above `n − f`
appears, and no certificate round: the second clause is what the other
protocols of this repository obtain from a certificate.

`supp` is the core's `supporters`, which counts authors rather than
blocks. The paper's side condition on `supp` excludes a supporter whose
**cone** holds a second block of `B`'s author and round, not merely one
whose references do. The two coincide, and the reason is a fact about
the model rather than a modelling choice: a reference sits exactly one
round below its referrer, so the round-`r` members of a round-`(r+1)`
block's cone are exactly its references, and the condition reduces to
the core's `ValidWrt.distinct_creators`.

`Linked` is a `Finset` of witnesses rather than a bare existential, so
that the rule is decidable on a concrete DAG. The rotation is a class
`Rotation` with one field, `anchor : ℕ → Validator`, rather than the
core's `Slots`: the protocol is indexed by rounds, and every clause
above names round `r + 1` explicitly, which under `Slots` would be a
hypothesis `slotRound (k + 1) = slotRound k + 1` carried through every
statement. §4 reconciles the two.

## 3. The rule as a validator applies it

`delivery(r)` runs against one validator's `DAG`, so each count is taken
over the blocks that validator holds: `SupportedIn`, `LinkedIn` and
`CommittedIn` are the definitions of §2 with each block set intersected
against a `View` (`LeanDag/BlackMarlin/Model/Decision.lean`).

There is no decision relation. Mysticeti and Odontoceti carry one
because a slot may be **skipped**, and a skip has to be derived through
an anchor. Black Marlin has no skip verdict and no indirect rule: an
anchor the rule does not admit is delivered, in its turn, inside the
causal history of a later anchor that the rule does admit. So the whole
of what a validator decides is `CommittedIn`, and agreement is the
statement that two validators' committed anchors lie on one chain.

`IsAnchor` is not relativised. Which validator anchors a round is a
schedule fact rather than an observation, and that the block exists at
all follows from the view holding a block that references it — which is
the second conjunct of BM4.

## 4. The results

Seven claims, stated in `LeanDag/BlackMarlin/Safety/Statement.lean` and
proved in the neighbouring `Proof.lean`. None assumes synchrony, a
global stabilisation time, or any bound beyond `n ≥ 3f + 1`; as in the
paper, they hold during the asynchronous period as well.

| | Claim | Paper |
|:---|:---|:---|
| BM1 | `AnchorUniqueness` — two supported anchors of one round are one block | Lemma 2 |
| BM2 | `Propagation` — a supported block is in the causal history of every block two rounds above | Lemma 4 |
| BM3 | `Density` — below the highest round, every round carries a quorum of authors | Lemma 3 |
| BM4 | `ViewSound` — a view's verdict is the universe's, and the view holds the block | — |
| BM5 | `Chained` — two committed anchors are one block, or one is in the causal history of the other | Lemma 5 |
| BM6 | `HistoryPrefix` — the lower committed anchor's history is contained in the higher's | Lemma 5, corollary |
| BM7 | `AnchorsAreLeaderBlocks` — the anchors are the core's leader blocks | — |

**BM1** is quorum intersection: two support quorums share `n − 2f ≥ f+1`
authors, each supporting both blocks, and a validator that supports two
blocks of one author and round is an equivocator — one more than the
fault bound admits. Only `n ≥ 3f + 1` is used, which is the whole
committee of this arc.

**BM2** is the core's `reaches_of_correct_support_of_card` followed by
`reaches_pred_of_round_le`, so it consumes no Black Marlin definition
beyond `Supported`. The support quorum holds `f + 1` correct authors,
each with one block at the round above; a block two rounds above names
`n − f` of the at most `n` authors of that round and cannot miss all of
them.

**BM5** is where the rule's second clause is used, and the only place.
The three cases of the paper's Lemma 5 are the three ranges of the round
gap between the two committed anchors: at gap `0` BM1 identifies them;
at gap `≥ 2` BM2 applies to the higher block itself; at gap `1` the
lower anchor's linking block and the higher anchor are both supported
anchors of the same round, so BM1 identifies *them*, and the link is a
direct reference. Without the link clause, two supported anchors one
round apart need not be comparable, and nothing else in the rule would
make them so.

**BM6** is what the paper means by the committed anchors defining one
partial order across honest parties. `commit(B)` delivers the
undelivered blocks of `past(B)` and then `B`, so containment of causal
histories is containment of delivered prefixes: two validators'
deliveries agree wherever both have delivered, and neither can retract.
The order *within* each increment is the deterministic sort `τ`, which
the rule does not constrain and this arc does not model.

**BM7** connects a round-indexed arc to the slot-indexed vocabulary of
the rest of the development: under `Slots.uniformSingle 1` — one slot
per round, slot `r` led by the validator the rotation elects for round
`r` — an anchor block of round `r` is a leader block of slot `r`, and
conversely. It asserts nothing about any verdict.

`commit(B)`'s recursion over `strong(B) \ D` selects `maxAnchor`, the
highest-round undelivered anchor in the strong past. That choice fixes
the order in which anchors are visited; it does not enlarge the set of
blocks delivered, since `past(B′) ∪ {B′} ⊆ past(B)` for every
`B′ ∈ strong(B)`, which is why BM5 and BM6 are stated about `history`.
The order it fixes is §11.

## 5. Modelling choices

**(i) The DAG layer is the core's, unchanged.** The paper's validity
predicate `V` — a quorum of distinct authors from the round below, no
two blocks of one author, all signed — is the core's `ValidWrt`
(`spec.md` §3.2). The one addition the core makes is
`ValidWrt.self_parent`, a reference by the block's own author, which
Black Marlin does not require. It restricts the universes the results
range over and is consumed by none of them, so what is proved here is
weaker than the paper by exactly that clause. Removing it would be a
change to the core rather than an addition to an arc, and is recorded
rather than performed.

**(ii) Strong references only.** A Black Marlin block carries a second,
time-bounded set of weak references to earlier rounds; `past` follows
both and `strong` follows the first alone. The commit rule reads
`strong`, so the arc is stated over the core's `refs`, and BM2 and BM5
conclude something stronger than the paper's `past`. Weak references
bear on delivery completeness — that every block is eventually
delivered — rather than on the rule.

**(iii) `Reaches` is reflexive** where the paper's `past` and `strong`
exclude their own argument, which is why BM5 states equality as a
separate disjunct rather than folding it into the reachability case.

**(iv) The rotation is abstract.** `Rotation.anchor` is an arbitrary
function `ℕ → Validator`; round robin is one instance, used in the
witness. No result below depends on which validator is elected, only on
one being elected per round.

**(v) Anchors are a predicate, not a function.** The paper's `RR`
"returns both blocks" when the elected validator equivocates, so an
anchor round has one elected *author* but may hold several anchor
*blocks*. `IsAnchor U r L` admits all of them, and the uniqueness the
rule needs is BM1 rather than a property of the rotation.

## 6. Witnesses

`LeanDagTest/BlackMarlin/Model.lean` is the paper's Figure 1: four
validators with validator `0` Byzantine, `f = 1`, six rounds, one anchor
per round, and every block referencing three of the four below it
including its author's own. Every definition of `Model/` is settled on
it by `decide` before anything is proved from it.

The figure's point is the last two rounds. Anchors `B0`, `B1`, `B2` and
`B3` all carry a quorum of support, but validator `0` omits `B3` from
`B4`, so `B3` fails the link clause while `B0`, `B1` and `B2` satisfy
the whole rule — `decide` settles both halves, and `linkers Ubm 15 3 = ∅`
identifies the clause that fails. `B4` fails the other way: supported,
with its linking anchor present, but that anchor unsupported because the
DAG stops at round `5`.

The same universe carries the configuration the link clause exists for:
`B3` and `B4` are both supported anchors, one round apart, and neither
lies in the causal history of the other — so a rule with the support
clause alone would admit two incomparable anchors and BM6 would fail of
them.

The seven claims are then instantiated at this universe through
`Safety.holds` itself, so what the witness exercises is the proved
theorem rather than a restatement of it.

## 7. Layout and discipline

The arc adopts the statement/proof partition of `LeanDag/MahiMahi/`
(`mahi-mahi.md` §9).

```
LeanDag/BlackMarlin/
  Model/         definitions only, theorem-free: Rules, Decision, Round, Ledger
                 (decidable instances by `inferInstanceAs` included: definitions, not proofs)
  Helpers/       generated lemma infrastructure; unaudited
  <Result>/Statement.lean imports Model/ only; definitions, prose, `def Statement : Prop`
  <Result>/Proof.lean     `theorem holds : Statement`; unaudited
                          Results: Safety (BM1-BM7), Liveness (BML1-BML5),
                          Reactive (BMR1-BMR6), Agreement (BMA1-BMA4),
                          Ledger (BMD1-BMD6)
LeanDagTest/BlackMarlin/  witness models; the instantiations are audited
scripts/check-arc-holes.py   sorry/admit/axiom/native_decide/unsafe/partial absent;
                             Statement.lean files proof-free; Model/ files theorem-free
```

The audit surface is `Model/`, the four `Statement.lean` files, the
witness instantiations and the checker. `scripts/check-arc-holes.py` covers both
partitioned arcs; it was named for Mahi-Mahi and is renamed here, its
checks unchanged.

**Relation to the core.** The core is consumed read-only: `Block`,
`BlockDag`, `Causality`, `CausalHistory`, `History`, `Support`,
`Validators`, `Schedule` for BM7 alone, `Liveness` for the participation
vocabulary and the counting step BML1 reuses, and `ViewPace` for the
pacing trunk `Pace` extends. The self-parent clause of
§5(i) is the one place a change to the core would strengthen a result,
and it is reported rather than made.

## 8. Liveness

The paper reaches liveness through §5.2's timing argument: Lemma 6's
`3∆` bound on a round, Lemma 9 on the timeout not firing when anchors
are honest, Lemma 10 on the expected number of rounds to a correct
anchor. This development states liveness above the structural condition
instead (`liveness.md`), so those are replaced rather than transcribed,
and no timeout, message delay, stabilisation time or probability appears
below. Five claims, in `LeanDag/BlackMarlin/Liveness/Statement.lean`:

| | Claim | Paper |
|:---|:---|:---|
| BML1 | `CommitStep` — a run of two reliable anchors over three populated rounds is committed | — |
| BML2 | `FullViewSound` — the full view reaches the verdict the rule reaches | — |
| BML3 | `Inclusion` — a reliable validator's block is in the causal history of every block two rounds above | Lemma 7 |
| BML4 | `Recurrence` — the rotation names a committing round arbitrarily far out | Lemma 10, role |
| BML5 | `RotationFair` — round robin supplies the run of two | — |

**BML1** is the core's counting step read twice. `Supported U L r` is
the core's `DirectCommit` under another name, so
`directCommit_of_votesAt` applies verbatim: coverage makes every
reliable block one round above `L` reference it, and those authors carry
a quorum. The link clause then costs no hypothesis of its own. The
round-`(r+1)` anchor is one of those reliable blocks, so the same
coverage fact already makes it reference the round-`r` anchor; and it is
supported by the same argument one round higher. Hence three populated
rounds and a run of two reliable anchors — where the core's three-round
rule needs a run that spans eligibility.

**BML3** consumes no clause of the commit rule. Coverage gives the block
a support quorum and BM2 carries it upward, so inclusion does not depend
on which anchors the rule admits, only on one being admitted above.
Together with BML4 this is the Validity property of Definition 1 for
reliable authors.

**BML4** plays the role of the paper's Lemma 10 — that commits keep
happening — without its probability. It quantifies the universe *inside*
the conclusion, as the core's
`CommitsAt` does and for the same reason: the rotation names the round,
and any DAG grown two rounds past it and covered from `R` commits it.
Fixing a universe first would cap how far the rotation may reach.

**BML5 is a theorem here where the core's counterpart is an assumption.**
The core's `FairRunOn` needs runs of three, and its docstring records the
pigeonhole for per-slot rotation as prose rather than proving it;
`WaveRobin.lean` supplies runs of three by rotating in waves instead.
Black Marlin needs runs of two, and that case is a short counting
argument: if no two cyclically adjacent anchors were reliable, the
successor map would inject the reliable set into the Byzantine one,
giving `n − f ≤ f` against `3f + 1 ≤ n`. So the rotation Black Marlin
actually deploys — `RR(r) = r mod n` — discharges the clause outright,
at every committee and whichever validators are Byzantine. This is a
consequence of the two-round rule rather than of the mechanisation:
three consecutive reliable leaders is a strictly harder fact than two,
and the second commit clause is what lets the rule ask only for two.

The witness is a second universe (`LeanDagTest/BlackMarlin/Liveness.lean`)
— four rounds, every block referencing the whole round beneath it.
Figure 1 cannot serve, and `decide` says why: its point is that
validator `0` omits the round-3 anchor from its round-4 block, which is
exactly a failure of coverage among the reliable validators.

## 9. The round rule, and the reactive schedule

`delivery(r)` is one half of the protocol; the other is L38–L41, which
says when a round is concluded. A validator waits for blocks from `n − f`
parties and then for **either** the round's anchor together with the two
anchors below it supported, **or** the round's timeout. The dual
condition is what makes the protocol responsive: it runs at the actual
delivery time rather than at `∆`, and it does not deadlock when an anchor
is Byzantine.

`LeanDag/BlackMarlin/Model/Round.lean` states the three clauses as
`QuorumIn`, `AnchorIn` and `SuppAnchorIn` over a `View`, and their
conjunction as `ConcludesAt`. `SuppAnchorIn` reads the same `SupportedIn`
the commit rule reads, so the round rule and the commit rule share their
arithmetic. The two lower clauses are written `∀ ρ, ρ + 1 = r → …` and
`∀ ρ, ρ + 2 = r → …` rather than with truncated subtraction, so the first
two rounds — where the paper's initialisation has no such anchors to
check — are vacuous rather than a separate branch.

`Pace` extends the core's `PaceCore` (report §6.9): the views,
convergence, the progress rule and production are inherited. Two clauses
are new. `anchor_or_wait` is the round rule read on the block a validator
produces — at the round above a reliable anchor, a block either
references that anchor or its builder waited the full timeout —  and it
is the same clause as the core's `ReactivePace.vote_or_wait`, since
concluding a round requires holding that round's anchor.
`prompt_conclude` bounds the exit from above, and it is **not** the same
as the core's `prompt_vote`: there the exit fires once the leader's block
is held, here once the whole round rule is satisfied.

Six claims, in `LeanDag/BlackMarlin/Reactive/Statement.lean`:

| | Claim | Paper |
|:---|:---|:---|
| BMR1 | `Votes` — every reliable block above a reliable anchor references it | — |
| BMR2 | `ReactiveCommit` — a run of two is committed, with no coverage hypothesis | — |
| BMR3 | `Exit` — the exit fires, given a run of **three** reliable anchors | — |
| BMR4 | `ExitSustained` — but only to enter: one further anchor per round after that | — |
| BMR5 | `Latency` — `D + δ + proc`, and `Δ + δ + 2 · proc` past GST | Lemma 6, role |
| BMR6 | `NoTimeout` — the timeout never fires when those undercut it | Lemma 9, role |

**BMR2 replaces BML1's coverage hypothesis.** `SynchronisedOn` asks that
every reliable block reference every reliable block below it, which a
reactive builder deliberately does not do. What survives is exactly what
the commit rule counts, and `anchor_or_wait` guarantees it — so reactive
liveness needs no coverage assumption at all.

**BMR3 is the cost of the extra clauses, and it is a run of three.** For
the exit to be guaranteed at round `r + 2`, the anchors of rounds `r`,
`r + 1` and `r + 2` must all be reliable: `quorum` and `anchor` come from
the round-`(r+2)` blocks, `suppAnchor(r+1)` from those blocks referencing
the round-`(r+1)` anchor, and `suppAnchor(r)` from the round-`(r+1)`
blocks referencing the round-`r` anchor. The commit rule asks for two
(§8); the fast path asks for three.

**BMR4 says the third is paid once.** `suppAnchor(r)` was already checked
to conclude round `r + 1`, and holdings only grow, so a validator already
on the fast path needs one further reliable anchor per round. Entering
costs a run of three; remaining costs a run of two. This is where the
run-of-three pigeonhole the core sidesteps re-enters the Black Marlin
arc — not for the commit rule, where BML5 discharges a run of two
outright, but for the guarantee that no timeout ever fires.

The witnesses are two (`LeanDagTest/BlackMarlin/Reactive.lean`).
`ConcludesAt` and its clauses are settled by `decide` on the covered
four-round model: round `3` may be concluded and round `4` may not. The
pacing structure is witnessed on `Ugrow`, the growing model the core's
reactive arc uses, at the same holdings and the same build spacing of
`6`; processing is `7` rather than the core's `5`, because the exit is
bounded by the round rule rather than by holding one block, and the
timeout is `25`, which is what lets both routes fire on one model.

## 10. Agreement

Definition 1's **Agreement** — if an honest party delivers a block, every
honest party eventually delivers it. Four claims, in
`LeanDag/BlackMarlin/Agreement/Statement.lean`:

| | Claim | Paper |
|:---|:---|:---|
| BMA1 | `Monotone` — a block delivered with a committed anchor is delivered with every committed anchor from that round on | Lemma 5, corollary |
| BMA2 | `LocalCommit` — a run of two is committed by each reliable validator on its **own view**, at an explicit time | Lemma 11, half |
| BMA3 | `Delivered` — the two composed | Definition 1, Agreement |
| BMA4 | `RunRecurs` — such a round exists above every round | — |

**BMA2 is the new work.** BML1 and BMR2 say a verdict is *available* over
the universe; Definition 1 speaks about what a party outputs. BMA2 runs
the same run-of-two argument inside `viewAt v t` rather than inside the
universe, with `PaceCore.holds_roundBlocks` putting the two rounds the
rule reads into every reliable validator's hands by
`max (latest (r+1)) (latest (r+2)) + Δ`. It needs no hypothesis beyond
BMR2's: that every build past round `R` lies past GST is derived from
`built_lt`, since the round number itself bounds the build time from
below.

**What is stated, and what is not.** A validator delivers `B` when it
calls `commit(A)` for an anchor it committed with `B ∈ past(A)`, so the
claims are about `B ∈ history U L` for the anchor `L` each validator
commits. Two things stand between that and the `ab-deliver` events of
Definition 1. The recursion of `commit` visits the undelivered anchors of
`strong(A)` before flushing, which fixes the **order** in which blocks
are delivered; that is §11. And the per-`(creator, round)` filter of L27
decides which of an equivocator's twins is delivered, which the
segmentation and the deterministic sort `τ` together arbitrate; `τ` is
not modelled. So the claims here are agreement on the delivered **set**,
with the order treated separately.

The witness is the covered four-round model for BMA1 — rounds `0` and `1`
are committed there and round `2` is not, the DAG stopping before its
link can be supported — and the pace of §9 for BMA2.

## 11. The delivered order

`commit(B)` does not deliver `past(B)` in one piece. It descends through
the undelivered anchors of `strong(B)`, flushing one `τ`-sorted segment
per anchor round from the lowest up (L18–L32). That segmentation *is* the
delivered order, and it is also what makes two validators' orders agree:
a validator that committed at rounds `3` and `5` and one that committed
only at `7` flush the same segments, because the second one's descent
visits `5`, `4` and `3` on the way down. `Model/Ledger.lean` models the
record the descent leaves rather than the recursion that builds it, as
the core models `Decided` rather than the implementation.

| | Claim | Paper |
|:---|:---|:---|
| BMD1 | `StepUnique` — the descent has one candidate where it steps by one round | — |
| BMD1′ | `CorrectAnchorUnique` — and at a round whose anchor is reliable, however deep the cone | — |
| BMD2 | `AgreeStep` — records agreeing at a round agree at the round below | — |
| BMD3 | `AgreeBelow` — and throughout any stretch they both descend | — |
| BMD4 | `CommittedPins` — records flushing committed anchors at one round agree there | Lemma 2 |
| BMD5 | `LinkPopulates` — the link clause keeps the descent from skipping | — |
| BMD6 | `Ledger` — no retraction, agreement, and one position per block | Definition 1, Total Order |

**BMD1 and BMD1′ say a tie needs two things at once.** The candidates at
round `ρ` below a round-`(ρ+1)` block are that block's references, and
`ValidWrt.distinct_creators` allows one block per author — so a
consecutive step has at most one candidate, whoever anchors. And at a
round whose elected validator is reliable the candidates are a singleton
however deep the cone, since non-equivocation gives it one block there.
So a choice requires a **skipped anchor round** — the elected validator
produced nothing, or its block is not referenced — **and** an
equivocating anchor at the round the descent then lands on. Either alone
leaves the descent determinate.

A skip stops the propagation of BMD2 and BMD3 there, and affects nothing
else: BML3's inclusion, BMA3's agreement and the whole of §4 are
statements about causal history rather than about segment boundaries, and
none of them reads the record.

**BMD5 is the point of the phase.** The commit rule's second clause was
used in exactly one case of one theorem for safety (§4). Here it does a
second job: above a committed anchor sits a *supported* anchor, which BM2
puts in the cone of every block from three rounds up — so the round above
a committed anchor is never the one skipped. The clause that makes
adjacent committed anchors comparable is also what keeps the delivery
order determinate around them.

**What is left over.** Where the descent skips a round *and* the round it
lands on has an equivocating anchor, nothing above applies,
and the paper's rule for that case cannot be transcribed. Algorithm 1
uses `maxAnchor(A)` as a set on L21 and as an element on L22, binds `A`
as a member of `A` on L24, and leaves the function undefined when the
candidate set holds no anchor. So BMD3 carries its stretch as a
hypothesis rather than deriving it, and the residual case is recorded
rather than resolved.

Ordering *within* a segment is `τ`, which the rule does not constrain and
this arc does not model, so the ledger is a set and a record's rounds are
the positions in it. BMD6's last two clauses — a block enters at exactly
one round, and records that agree concur on which — are total-order
safety at that granularity.

The witness is the covered four-round model with its four anchors: the
candidate sets are singletons on data, and validator `3`'s genesis block
is placed at round `1`, with the anti-vacuity that it is not in the
round-0 anchor's cone.

## 12. What is not covered

**Lemma 10.** No counterpart, and none needed: BML5 makes the recurring
run deterministic where the paper bounds an expectation.

**Lemmas 6 and 9 in their own terms.** BMR5 and BMR6 play their roles —
a bound on the time to conclude a round, and the timeout not firing when
anchors are reliable — but state them in `∆`, the actual delivery `δ` and
the processing bound, above the pacing structure rather than over a
message schedule.

**Delivery completeness.** BML3 covers reliable authors. That *every*
block reaches the ledger needs the weak-reference window of §4.3.

**Integrity**, the third property of Definition 1. It rests on the
delivered set `D`, which is not modelled. Validity is BML3 with BML4,
Agreement is §10, and Total Order is §11 at the granularity of
segments.

**The deterministic sort.** `τ` orders each delivered segment. §11 gives
Total Order at the granularity of segments — a block enters at exactly
one round, and records that agree concur on which; the order *within* a
segment needs `τ` modelled.

**The skipped-round tie-break.** L21–L24, whose text does not parse
(§11). Everything §11 proves is about a descent that steps by one
round.
