# lean-dag — Async BlueBottle: design record

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for the **Async BlueBottle** arc: the
asynchronous variant of BB-Core, the consensus core of BlueBottle,

> P. Vander Vos, A. Sonnino, G. Tsimos, P. Jovanovic, L. Kokoris-Kogias.
> *BlueBottle: Fast and Robust Blockchains through Subsystem
> Specialization.* arXiv:2511.15361, 2025 — Appendix G, "Asynchronous
> BB-Core".

BB-Core is the two-round rule this repository formalizes as
**Odontoceti** (`odontoceti.md`, report §10). Its asynchronous variant
stretches the wave to three rounds with merged certificates: a leader
proposed at round `r` is voted on and decided at round `r + 2`, a
round-`(r + 2)` block voting through its **causal cone**, and the leader
is named by a common coin after the fact. The arc proves the rule safe
on the unmodified DAG layer at the committee `n ≥ 5f + 1`, and live with
**no synchrony hypothesis** under Mahi-Mahi's unpredictable-leader
clause, which the coin makes true; the counting that makes the clause
non-vacuous is the paper's Lemmas 27–31, proved at every `n ≥ 5f + 1`.
Results carry **ABB**-labels. Everything lives in `LeanDag/AsyncBlueBottle/`
with witnesses in `LeanDagTest/AsyncBlueBottle/`, consuming the core,
Odontoceti's fault model and Mahi-Mahi's vote read-only, under the
statement/proof discipline of §9.

## 0. Overview

**The protocol, as the paper and the implementation define it.** The
source of truth is Algorithm 2 of the paper with its orange lines, and
`crates/consensus/src/{protocol.rs,base.rs,wave.rs}` in the `mysticeti`
repository (`Protocol::blue_bottle_asynchronous`). Relative to BB-Core
it changes two parameters and nothing else:

| | BB-Core (Odontoceti) | BB-Core-Async |
|:---|:---|:---|
| `wave_length` | 2 | **3** |
| decision round of a slot at `r` | `r + 1` | **`r + 2`** |
| a vote for `L` | a round-`(r+1)` block referencing `L` | a round-`(r+2)` block whose **cone** supports `L` (`find_support`, a depth-first search to the first block of `L`'s author and round) |
| direct commit / skip | `n − f` distinct authors | `n − f` distinct authors |
| indirect test | `n − 3f` supporters in the anchor's cone | `n − 3f` voters in the anchor's cone |
| anchor floor | `r + 2` | **`r + 3`** |
| tie among candidates | least digest | least digest |
| waiting for the leader | yes | **no** (`leader_wait: false`) |
| leader election | round-robin | a threshold common coin (Appendix G.1); round-robin in the implementation |

The arc is therefore a composition of two arcs already in the tree:
**Odontoceti's arithmetic** (O1–O4′) with the decision round moved from
`r + 1` to `r + 2` and reference-support replaced by the cone vote, and
**Mahi-Mahi's liveness** (`good`, the clause, the common core) at a fixed
three-round wave. It is not Mahi-Mahi at `w = 3`, which is the core's
certificate rule — votes at `r + 1`, certificates at `r + 2` — but a
single count at `r + 2`; the single count is what the committee of size
`5f + 1` is required for, and the blame is Mahi-Mahi's at wave four, on
the record (ABB1″).

**The results.**

- **ABB1–ABB5 — safety** (§4): commit excludes skip, two commits name
  one block, a skipped slot passes the weak test nowhere, a commit
  passes it from every block three rounds up, a commit excludes every
  rival, and two views deciding one slot agree. ABB1 and ABB1′ hold at
  `n ≥ 3f + 1`; ABB2 and ABB4′ are where `n ≥ 5f + 1` is required.
- **ABB6–ABB8 — the counting lemma** (§5), with no network hypothesis:
  some correct validator's block is directly committed in every wave a
  reliable quorum populates; at least `n − 3f` of them are; and with
  `3f + 1` distinct leaders at a round one is committed, for every
  schedule.
- **ABB9 — liveness under `UnpredictableWithin`** (§6), Mahi-Mahi's
  clause at this wave: a good leader's slot commits on any view caught
  up to its decision round, commits recur in every window, every slot
  below a spanning run is decided, and every reliable validator commits
  a universally voted candidate on its own view at an explicit time.
- **ABB10 — partial synchrony recovered** (§6): under `SynchronisedOn`
  at one round the leader is good, and the clause is derived from the
  core's `FairWithin`.
- **Two findings on data** (§4, §7): two equivocating twins can both
  pass the weak test at one anchor, so agreement needs the canonical
  candidate the paper's Observation 4 assumes away; and the paper's
  `TryDirectDecide` is order-dependent under equivocation, which the
  implementation's slot-level blame avoids.
- **Conformance** (§8): the rule is banded, agrees, names its
  candidate, has the indirect property, a support with the three laws,
  and the descent laws, so every mechanism of the tree applies to it.

### 0.1 Correspondence with the paper's Appendix G

| paper | here | remark |
|:---|:---|:---|
| Definitions 3, 4 (weak, strong certificate) | `WeakLink`, `DirectCommit` | on distinct authors, as the definitions say and Algorithm 2 does not |
| Lemma 18 (strong-to-weak propagation) | ABB3 | |
| Lemma 19 (strong certificate exclusivity) | ABB1′ (strong case), ABB4′ (weak case) | |
| Lemma 20 (commit excludes direct skip) | ABB1, ABB2 | |
| Lemma 21 (direct commit excludes indirect skip) | the laws' `commit_link`, from ABB3 | |
| Observation 4 (one valid block per author and round) | **not assumed**; the canonical candidate replaces it | §4 |
| Lemmas 22, 23 (agreement) | ABB5 | |
| Lemmas 27–30 (the core set `C_R`, `|C_R| ≥ 2f + 1`) | ABB7 | at every `n ≥ 5f + 1`, as `n − 3f` |
| Lemma 31 (`p⋆ = 1` when `l > 3f`) | ABB8 | the probabilistic part is prose over ABB7 |
| Lemma 32 (eventual slot resolution) | ABB9c | the chain argument as a run, `mahi-mahi.md` §5.5 |
| Algorithm 2, `TryDirectDecide` | the `hazard6` witness | §7 |

## 1. The rule at a three-round wave

Fix a `Slots` instance as in the core; the slot `k` is proposed at
`r = slotRound k`.

| round | role |
|:---|:---|
| `r` | proposal: the candidate blocks of `leader k` |
| `r + 1` | dissemination only; the rule never reads it |
| `r + 2` | voting and decision: the cone votes and blames |
| `≥ r + 3` | the anchor floor |

A round-`(r + 2)` block `q` **votes** for a candidate `L` at `(a, r)` when
`L` is the canonical block of `a` at `r` in `q`'s cone — Mahi-Mahi's
`Votes`, the least block of that author and round in `history U q`
under `[LinearOrder BlockId]` — and **blames** the slot when no block of
`(a, r)` lies in its cone (`MahiMahi.Blames`, the implementation's
`find_support = None`). The rule layer (`Model/Rules.lean`):

```lean
def decisionRoundAt (r : ℕ) : ℕ := r + 2
def voters (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (decisionRoundAt r)).filter (fun q => MahiMahi.Votes U q L)
def DirectCommit (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (supporters U L r).card
def DirectSkip (U : BlockUniverse Validator BlockId Payload) (a : Validator) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blamers U a r).card
def WeakLink (U : BlockUniverse Validator BlockId Payload) (A L : BlockId) (r : ℕ) : Prop :=
  Fintype.card Validator - 3 * F.f ≤ (coneSupporters U A L r).card
```

`supporters` and `blamers` are the distinct authors of the voters and
blamers; `coneSupporters U A L r` the distinct authors of the voters for
`L` in the anchor `A`'s cone. The committee is Odontoceti's `Faults5`,
`n ≥ 5f + 1`, so the DAG quorum and both direct thresholds are `n − f`
and the weak threshold `n − 3f` is at least `2f + 1`; at `n = 5f + 1`
these are the paper's `4f + 1` and `2f + 1`. Every predicate is
decidable, which is what lets the witnesses run by `decide`.

## 2. The reuse boundary

The DAG layer is the core's, verbatim, as for Odontoceti: at `n ≥ 5f+1`
the quorums are `n − f`, `ValidWrt` is the paper's validity clause for
clause, and the `full6` witness proves the reuse claim as a computation.
Two things are imported from the sibling arcs and nothing is changed in
either:

- from **Odontoceti**, the fault model `Faults5`;
- from **Mahi-Mahi**, `candidatesAt`, `Votes`, `Blames` and their lemmas
  (`eq_of_votes`, `not_blames_of_votes`, `votes_of_reaches`), the band
  transport of the vote (`votes_band`, `blames_band`), the common core,
  `reaches_of_synchronisedOn`, and `AgreeUpto`.

What the arc has of its own is the single count at `r + 2`: the five
arithmetic lemmas, the in-cone voter set and its transport, and the
double count of §5.

## 3. The decision relation

`asyncBlueBottleAnchored` is the anchored relation (`Common/Anchored.lean`)
at the arc's data: `waveAt = 2` — the decision round `r + 2`, the
protocol's three-round wave less one, as Mahi-Mahi's `w − 1` — the
cone-vote quorum direct commit, the slot-level direct skip, one rung of
link `WeakLink`, and the tie `L < L'`. Eligibility is
`Eligible k j ↔ slotRound k + 3 ≤ slotRound j`, the code's
`leader_round + wave_length ≤ anchor.round`. `Decided` is the relation's,
so agreement, monotonicity in the view, the bounded relation and the
descent are proved once in the common layer and instantiated here.

**Canonicity.** As in Odontoceti (`odontoceti.md` §6, F1), the indirect
commit names the *least* candidate passing the test. The paper's
Observation 4 assumes at most one block per author and round counts as
valid, and its Lemmas 22 and 23 rest on it; the DAG of its own Figure 1
holds an equivocation, and so does the implementation, whose
`decide_leader_from_anchor` breaks ties by digest. Without the tie two
twins can both pass the weak test at one anchor — `twin6_both_pass`,
§7 — and agreement would be false.

## 4. Safety (ABB1–ABB5)

`Safety/Statement.lean`, universe-level unless said:

- **ABB1, `CommitExcludesSkip`.** A committed candidate's slot is not
  skipped: voters and blamers together number at most `n + f`, since a
  correct author's one decision-round block cannot both vote for `L`
  and hold no candidate (`MahiMahi.not_blames_of_votes`), and two
  quorums are more. At `n ≥ 3f + 1`.
- **ABB1′, `CommitUnique`.** Two committed blocks of one author and
  round coincide: a correct common voter's block votes for one block of
  that author and round (`MahiMahi.eq_of_votes`). At `n ≥ 3f + 1`.
- **ABB2, `SkipExcludesLink`.** A skipped slot's candidate has at most
  `2f` supporters, below `n − 3f`. The counting is Odontoceti's O2 with
  the exact complement identity replaced by
  `card_add_card_le_of_inter_subset` on the Byzantine set.
- **ABB3, `Propagation`.** A commit passes the weak test from every
  block at round `≥ r + 3`: a round-`(r + 3)` block's `n − f`
  distinct-author references meet the `n − f` supporters in `n − 2f`
  authors, and each correct one's referenced round-`(r + 2)` block *is*
  its voting block, so `n − 3f` of them lie in the cone; cones nest, so
  the bound never decays. Odontoceti's O3 one round up.
- **ABB4′, `CommitExcludesRival`.** `n − f` voters and `n − 3f` in-cone
  voters for a twin share `n − 5f ≥ 1` correct authors, each voting for
  two twins — impossible. Where `n ≥ 5f + 1` is required.
- **ABB1″, `SkipIsMahiMahi`.** `DirectSkip U a r ↔ MahiMahi.DirectSkip U 4 a r`:
  Mahi-Mahi's voting round at wave four is `r + 2`, so the blame is
  Mahi-Mahi's block for block. The half of the "trivial mix" that is a
  transcription of Mahi-Mahi, stated.
- **ABB5, `Agreement`.** Two views deciding one slot agree, whatever
  routes each took — `AnchoredRule.decided_unique` at
  `asyncBlueBottleLaws`, whose laws are Odontoceti's field for field
  with the five lemmas above, `skip_congr` rewritten Mahi-Mahi style.

There is no conservativity conjunct onto a rule of the tree, since none
decides at `r + 2` by a single count: Odontoceti decides at `r + 1`, and
Mahi-Mahi at `w = 3` is the core's certificate rule. ABB1″ is what
stands in its place.

## 5. `good` and the counting lemma (ABB6–ABB8)

`goodAt U r` is the set of validators whose round-`r` block is directly
committed, `good U k` the same at a slot's round: Mahi-Mahi's `good` with
`w` erased (`Model/Good.lean`). The counting results bound it below
under the fault model, validity and population by a reliable quorum `T`,
and nothing else (`Counting/Statement.lean`):

- **`CommonCore`** is Mahi-Mahi's, character for character, and the
  proof cites Mahi-Mahi's (the core's T3c carried upward).
- **ABB6, `GoodNonempty`.** With `T` populating the decision round
  `r + 2`: some correct validator's round-`r` block is committed. The
  common core of round `r` is reached by every round-`(r + 2)` block,
  and reaching a correct block is voting for it. One populated round,
  at `n ≥ 3f + 1`.
- **ABB7, `GoodCard`.** With `T` populating `r + 1` and `r + 2`:
  `n ≤ |goodAt U r ∩ Correct| + 3f`. The paper's Lemmas 27–30 count, at
  `n = 5f + 1`, the correct round-`r` blocks referenced by `f + 1`
  honest round-`(r + 1)` blocks and find `2f + 1`; the same double count
  at general `n` — each reliable round-`(r + 1)` block references at
  least `n − f − |byzantine|` correct authors, a correct block with
  fewer than `f + 1` reliable referrers absorbs at most `f` edges —
  yields `n − 3f`, which is `2f + 1` at the boundary and more above it.
  Such a block is reached by every round-`(r + 2)` block, which omits at
  most `f` authors and so meets one of its `f + 1` referrers
  (`reaches_of_honest_support_of_card`). The double count is
  `card_mul_le_of_bipartite` (`Helpers/Counting.lean`), a threshold form
  of Mathlib's `Finset.card_nsmul_le_card_nsmul`, and the arithmetic is
  isolated in `goodCard_arith`. Stated additively, as every threshold of
  the tree is.
- **ABB8, `MultiLeader`.** With `3f + 1` distinct leaders at a round,
  one is good: `n − 3f` good correct validators and `3f + 1` leaders
  cannot be disjoint in `n`. The paper's Lemma 31 has `p⋆ = 1` for
  `l > 3f`; the relative bound makes it hold at every `n ≥ 5f + 1`, not
  only at the boundary.

The bounds count distinct correct authors, so an equivocating author's
twins, which can split the voters, are never counted — the reading under
which Mahi-Mahi's five-round count was corrected (`mahi-mahi.md` §4.2).

## 6. Liveness (ABB9), and partial synchrony (ABB10)

The model has no adversary and no time, so "the leader is revealed by
the coin after the wave" cannot be said directly; what can be said is
its observable consequence on the pair (schedule, DAG), Mahi-Mahi's
clause at this wave (`Model/Unpredictable.lean`):

```lean
def UnpredictableWithin (U : BlockUniverse Validator BlockId Payload) (c N : ℕ) : Prop :=
  ∀ k,
    (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound (k + c) ≤ N →
    ∃ k', k ≤ k' ∧ k' < k + c ∧ S.leader k' ∈ good U k'
```

with its run form `UnpredictableRunWithin`. The paper supplies it by a
threshold-signature common coin with an asynchronous key setup
(Appendix G.1), which the model does not formalize; a uniform draw lands
in `good` with probability at least `(n − 3f)/n` by ABB7, and the
measure stays in prose exactly as GST does for the core. Every
statement carries the horizon `N`, since `good` is empty past some round
in any finite DAG (`mahi-mahi.md` §5.4).

**ABB9** (`Liveness/Statement.lean`), every conclusion on a view a
validator can hold: **a**, a good leader's slot is committed on any view
caught up to its decision round; **b**, under the single-hit clause
every window below the horizon commits a slot; **c**, under the run form
with a spanning run every slot below the run is decided, the common
descent `decided_below_of_run` with the tie broken by the order; **d**,
on any pacing structure a candidate every reliable decision-round block
votes for is committed by every reliable validator on its own view at
`max (latest (r + 2)) gst + delay`, convergence read as eventual
delivery only; **e**, two universes agreeing up to `r + 2` have the same
`goodAt` at `r` (Mahi-Mahi's `AgreeUpto`).

**ABB10** (`Synchrony/Statement.lean`): under `SynchronisedOn U T R` at
the slot's round and population at `r`, `r + 1` and `r + 2`, a reliable
leader is good — `MahiMahi.reaches_of_synchronisedOn`, into which the
wave length never enters — and hence under coverage from the start the
clause is derived from the core's `FairWithin`. The two liveness
accounts are one: under synchrony the clause is discharged by fairness,
under asynchrony by the coin.

## 7. Witnesses (`LeanDagTest/AsyncBlueBottle/`)

Six validators, `f = 1`, validator `0` Byzantine, quorum `5`, weak
threshold `3` — Odontoceti's boundary instance. The schedules are local
instances: round-robin from validator `1` (`Model.lean`, `Counting.lean`,
`Liveness.lean`), so that slot `0` has a correct leader, and from
validator `0` in `Twins.lean`, where slot `0` must be the equivocator's.
Every definition is settled by `decide` before anything is proved from
it.

| file | witness | what it pins |
|:--|:--|:--|
| `Model.lean` | `full6` | four fully connected rounds: the wave arithmetic at rounds `0` and `3`, the anchor floor, `candidatesAt`/`Votes`/`Blames` at the decision round, a direct commit with six voters, `WeakLink` from a round-`3` block |
| `Model.lean` | `aim6` | the aiming pattern: the leader's block present and kept out of every cone but its own, five blamers — exactly the quorum — a **direct skip** as a derivation |
| `Model.lean` | `five6`, `four6` | the direct commit at exactly five voters, and neither rule at four |
| `Model.lean` | `icommit6` | a three–three split, undecided directly, **indirectly committed** through the slot-`3` anchor with `coneSupporters` exactly `{1, 2, 3}` |
| `Model.lean` | `iskip6` | a two–four split, **indirectly skipped**: two voters reach no cone's threshold |
| `Twins.lean` | `twin6` | two twins with three voters each; a round-`3` block sees all of round `2` and **both pass `WeakLink`** (`twin6_both_pass`); at the actual anchor only the least passes, and the derivation commits it |
| `Twins.lean` | `hazard6` | both twins in every cone, every vote to the least; the least twin directly committed while the other has a quorum of per-candidate non-voters (`hazard6_skipped_twin`); the slot-level blame is empty |
| `Counting.lean` | `aim6`, `multi` | `goodAt aim6 0 = {0, 2, 3, 4, 5}` — round-robin names exactly the starved validator; the common core on data; the statement hypotheses and `n − 3f ≤ 4` on data; four leaders per round include a good one |
| `Liveness.lean` | clause | both forms hold on `full6`; `¬ UnpredictableWithin aim6 1 3` under round-robin while `FairScheduleOn Correct` holds; `SpansEligible 3` at one leader per round; ABB9a on data |
| `Axioms.lean` | — | every `holds` depends on the three standard axioms |

**Two findings for the paper.**

- **Agreement needs a canonical candidate.** Observation 4 ("at most
  one block signed by `w` is counted as valid in round `r`") is not a
  property of the DAG the paper builds — Figure 1 shows `P1′` — and it
  is what Lemmas 22 and 23 rest on. Without it two twins can both pass
  the weak test at one anchor (`twin6_both_pass`: the counting that
  would separate them needs `2(n − 3f) − f > n`, false at `n = 5f + 1`),
  and an `∃`-style indirect commit admits conflicting derivations. The
  implementation breaks the tie by digest; the arc states that
  determinism as the tie of the anchored rule. Odontoceti's F1
  (`odontoceti.md` §6), which applies to both variants.
- **Algorithm 2's direct rule is order-dependent under equivocation.**
  `TryDirectDecide` iterates the leader's blocks and returns `Skip` at
  the first with `4f + 1` non-votes, before testing a twin's strong
  certificate. The `4f + 1` voters of twin `b₂` are non-voters of twin
  `b₁`, so a validator holding both twins may skip the slot while one
  holding only `b₂` commits it. `hazard6` realises the configuration:
  twin `0` is directly committed and `SkippedLeader(6)` holds. Under
  Observation 4 the loop has one iteration and the hazard cannot arise;
  it arises as soon as both twins are valid. The implementation blames
  the slot (`enough_leader_blame`: `find_support = None`) and tests the
  blame before the support, which is safe and is what the arc
  formalizes; the pseudocode should do the same, for both variants.

Recorded modelling choices, as for Mahi-Mahi: canonical support by the
least block in the cone rather than depth-first order (`mahi-mahi.md`
§2); the blame on the slot; the weak test on distinct authors, the
paper's Definitions 3–4 rather than Algorithm 2's block count;
`DirectCommit U L r` does not pin `L`'s round to `r` — `Votes` reads the
candidate's own round — and every consumer goes through `IsLeaderBlock`,
which does.

## 8. Conformance (`Carrier.lean`, `Properties.lean`, `Record.lean`)

The carrier is the anchored rule's. `Quorate`, `SelfParent`, `NoEquiv`,
`Agree`, `CommitsCandidate` and `CommitsDirect` are one line each. The
band laws transport the direct commit and skip through Mahi-Mahi's
`votes_band` and `blames_band` — a band of this carrier is a band of
Mahi-Mahi's, both reading the record's `ids` and `block` — and the weak
link through `coneSupporters_band`, Odontoceti's transport with the
reference replaced by the vote; a candidate the band did not carry has
no voter in an old anchor's cone, since a voter for it holds it in its
own cone and an old cone holds only old blocks. The support `abbSupport`
certifies by the cone vote at `waveAt = 2`: `Local` is `votes_band` at
the band a `RebasedAbove` is, `OfCoverage` is `reaches_of_votes` followed
by `votes_of_reaches`, and `Commits` the direct commit on a caught-up
view. `Indirect` is the relation's at gap three, `Descent` at slack `f`,
and the headlines `safety` and `liveness` are the generic ones.
`SkipsUnsupported` is not claimed: an unsupported slot at `r + 1` can
still be reached at `r + 2` through a Byzantine round-`(r + 1)` block.

## 9. Layout and discipline

```
LeanDag/AsyncBlueBottle/
  Model/         definitions only, theorem-free: Rules, Decision, Good, Unpredictable
  Helpers/       generated lemma infrastructure; unaudited
  <Result>/Statement.lean   imports Model/ (and the core); `def Statement : Prop`; never a proof
  <Result>/Proof.lean       `theorem holds : Statement`; unaudited
  Carrier, Properties, Record   conformance to `target-properties.md`
LeanDagTest/AsyncBlueBottle/  witness models; the instantiations are audited
```

The audit surface is `Model/`, every `Statement.lean`, the witness
instantiations and `scripts/check-arc-holes.py`, which lists the arc.
Results: `Safety` (ABB1–ABB5, ABB1″), `Counting` (`CommonCore`,
ABB6–ABB8), `Liveness` (ABB9a–e), `Synchrony` (ABB10a–b). The core,
Odontoceti and Mahi-Mahi are consumed read-only; every file outside
`LeanDag/AsyncBlueBottle/`, `LeanDagTest/AsyncBlueBottle/` and the
documents that was touched is a root import list, an audit script's
table, or a document.

## 10. Phases

| phase | deliverable |
|:--|:--|
| 1 | `Model/Rules.lean`, `Model/Decision.lean`; `full6`, `aim6`, `five6`, `four6`, `icommit6`, `iskip6`, `twin6`, `hazard6` |
| 2 | `Safety/` (ABB1–ABB5, ABB1″) |
| 3 | `Model/Good.lean`, `Counting/` (ABB6–ABB8), the double count; the counting witnesses |
| 4 | `Model/Unpredictable.lean`, `Liveness/` (ABB9); the clause witnesses |
| 5 | `Synchrony/` (ABB10) |
| 6 | `Carrier.lean`, `Properties.lean`, `Record.lean` |
| 7 | this record; report §24; `related.md`; README |

Two reviewing agents read the frozen phases 1–3 against Odontoceti and
Mahi-Mahi before phase 6; what they changed is recorded where it
applies: a positive direct-skip witness and the boundary witnesses
(§7), the relative bound `n − 3f` in place of the paper's `2f + 1` (§5),
ABB1″ (§4), the coin as the paper describes it (§6), and Mahi-Mahi's
`AgreeUpto` reused rather than copied (§2).

Follow-ups, not in scope: a Barnacle base and live rule instance
(`LeanDagTest/Barnacle/Rules/`), a reactive variant
(`LeanDag/Reactive/`), and the Steelhead composition with Odontoceti at
a kinded schedule (`kinds.md`), for which the rule's `waveAt` is already
a function of the kind.
