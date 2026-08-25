# Black Marlin: the commit rule

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

The design record for `LeanDag/BlackMarlin/`: the commit rule of *DAG it
off: Latency Prefers No Common Coins* (Amores-Sesar, Grøndal, Holmgård
and Ottendal, arXiv:2508.14716v3), and its safety.

## 1. The protocol, and what this arc covers

Black Marlin is a partially synchronous DAG protocol at `n ≥ 3f + 1`
with neither reliable broadcast nor a common coin. It elects one
**anchor** per round by round robin, and it commits three rounds after
proposal. A round advances when a validator holds blocks from `n − f`
parties, has the anchor of the round, and sees the two anchors below it
supported; a timeout supplies the second disjunct when an anchor is
Byzantine, which is what keeps the protocol responsive.

This arc covers `delivery(r)` (Algorithm 2, L14–L17) and §5.1 of the
paper — the commit rule and every safety result stated about it. The
round structure, the timeouts, the weak-reference window and §5.2's
liveness are not covered; §8 says what taking them on would require.

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
blocks. The paper's side condition on `supp` — a supporter's block
references no second block of `B`'s author and round — is the core's
`ValidWrt.distinct_creators` and needs no restatement.

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
highest-round undelivered anchor in the strong past, and breaks ties
deterministically when the elected validator equivocated. That choice
fixes the order in which anchors are visited; it does not enlarge the
set of blocks delivered, which is why BM5 and BM6 are stated about
`history` and the recursion is not modelled.

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
  Model/         definitions only, theorem-free: Rules, Decision
                 (decidable instances by `inferInstanceAs` included: definitions, not proofs)
  Helpers/       generated lemma infrastructure; unaudited
  Safety/Statement.lean   imports Model/ only; definitions, prose, `def Statement : Prop`
  Safety/Proof.lean       `theorem holds : Statement`; unaudited
LeanDagTest/BlackMarlin/  witness models; the instantiations are audited
scripts/check-arc-holes.py   sorry/admit/axiom/native_decide/unsafe/partial absent;
                             Statement.lean files proof-free; Model/ files theorem-free
```

The audit surface is `Model/`, `Safety/Statement.lean`, the witness
instantiations and the checker. `scripts/check-arc-holes.py` covers both
partitioned arcs; it was named for Mahi-Mahi and is renamed here, its
checks unchanged.

**Relation to the core.** The core is consumed read-only: `Block`,
`BlockDag`, `Causality`, `CausalHistory`, `History`, `Support`,
`Validators`, and `Schedule` for BM7 alone. The self-parent clause of
§5(i) is the one place a change to the core would strengthen a result,
and it is reported rather than made.

## 8. What is not covered

**Liveness (§5.2 of the paper).** Lemmas 6 to 11 and Theorem 12 rest on
the round structure — the timeout, the `3∆` weak-reference window, and
the dual condition under which a round is concluded — none of which is
modelled here. Lemma 10 is also probabilistic, bounding the expected
number of rounds to a correct anchor, where this repository's liveness
results are stated above the structural condition of *eventual DAG
synchrony* (`liveness.md`); the two would have to be reconciled before
the paper's argument could be transcribed.

**Delivery completeness.** That every block reaches the ledger, rather
than every committed anchor's history nesting, needs the weak-reference
window of §4.3 and is a validity property in the paper's sense
(Definition 1), not a safety one.

**The deterministic sort.** `τ` orders each delivered increment, and
Total Order in Definition 1 is a statement about the resulting sequence.
BM6 gives the nesting the sequence is built from; turning it into a
sequence needs `τ` modelled.
