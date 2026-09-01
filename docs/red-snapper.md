# lean-dag — RedSnapper: design record

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

This document is the design record for the **RedSnapper** arc: the
owned-object fast path of the RedSnapper paper (`~/GitHub/redsnapper-paper`,
"Snapper" in the manuscript) layered over an uncertified DAG whose
consensus is treated as a black box. Validators publish a *stance* per
object version in the blocks they already produce; transaction
certificates, skip certificates and unlock certificates are read from
the DAG; a conflict between two transactions spending one owned object
is resolved in the epoch rather than at its boundary. At `n ≥ 3f + 1`
the univalent cases are decided from the DAG and the bivalent case at a
committed anchor; at `n ≥ 5f + 1` a validator may safely revoke an
earlier vote on `2f + 1` opposing votes, a coin coordinates the moves,
and a freeze-and-count fallback at an anchor bounds the resolution. A
protocol-independent section characterises when revocation is safe and
when a quorum of votes is guaranteed to expose it. The arc proves the
certificates exclusive, the verdicts unique across views and routes,
the conflict resolved under a structural rendering of synchrony, and
the `5f + 1` revocation rules safe with the recovery fallback; it
states the revocation arithmetic first, as the seam both protocols
consume. Results carry **RS**-labels; everything lives in
`LeanDag/RedSnapper/` under the statement/proof partition (§5), with
`decide` witnesses in `LeanDagTest/RedSnapper/`, consuming nothing from
the core.

This record is written at Phase 0 and states the plan; the final
position is recorded at the last phase.

## 0. Overview

The arc's one structural observation is that **the two protocols differ
in one inequality**. Both count the same two thresholds: a quorum
`n − f` (the paper's `2f + 1` at `n = 3f + 1`, its `4f + 1` at
`n = 5f + 1`) and a half `2f + 1`. At `n ≥ 3f + 1` the half is the
revocation threshold of the paper's Theorem "vote revocation": `2f + 1`
opposing votes prove that a validator's earlier vote can no longer
complete a quorum. What the larger committee adds is *exposure*: among
any `n − f` votes one side reaches `2f + 1` exactly when
`n ≥ 5f + 1`. Below that bound the protocol may collect a quorum of
votes and still be unable to move, which is the bivalent case that
`n = 3f + 1` sends to consensus; at or above it every quorum licenses a
move, which is what the coin-driven protocol relies on. RS1 states this
arithmetic once, in the paper's protocol-independent form and at the
two thresholds, and both protocols consume it.

Three consequences shape the arc.

- **Safety has no behavioural content beyond monotonicity.** Every
  safety lemma at `3f + 1` uses of a correct validator only that it does
  not equivocate, that its blocks form a chain, and that its stance on
  an object moves along `none → {tx, ⊥}`, `tx → {tx, ⊥}`, `⊥ → ⊥`. The
  full voting rule — when a correct validator adopts, keeps or retracts
  — enters only the liveness claims (D5).
- **Consensus is one global object.** The paper's interface properties
  (C1)–(C3) say the committed anchor sequence and every anchor's causal
  history are the same at every correct validator. The arc takes the
  anchor sequence as a component of the universe; the anchor-route
  verdicts are then functions of global data, and agreement across
  validators reduces to agreement across views for the consensusless
  routes (D4, D6).
- **The `5f + 1` results generalise to `n ≥ 5f + 1`.** With the
  thresholds written as `n − f` and `2f + 1`, every counting step of
  the paper's `5f + 1` section closes (`|S| ≥ n − 2f`,
  `n − |S| ≤ 2f < 2f + 1`; `|F ∩ S| ≥ n − 3f ≥ 2f + 1`), as Odontoceti's
  did (D1).

### 0.1 Correspondence with the paper

| Paper (`redsnapper-paper/`) | Lean (planned) |
|:---|:---|
| System model, `f`, correct validators (`2.Prelim.tex`) | `Model/Faults.lean` — `Faults`, `quorum`, `half`, `Five`, `Correct` |
| §10 Fundamental limits of vote revocation | `Model/Revocation.lean` — `Profile`, `supporters`, `opposers`, `voters`; `Revocation/` (RS1) |
| Blocks, `Link`, `RoundParents` (`Alg:FastPathPredicates`) | `Model/{Block, Universe, View, CausalHistory}.lean` — `Block`, `ValidWrt`, `Universe`, `View`, `Reaches` |
| Transactions, `OwnedInputs`, `Includes`, `Candidates`, `ConflictedObjs` | `Model/{Block, Transaction}.lean` — `Transactions`, `Conflict`, `Owned`, `Includes`, `IsCandidate`, `Conflicted` |
| `Stance`, `AckedBefore`; the `held` automaton of §7 | `Model/Stance.lean` — `StanceIs`, `AckedBefore`, `StanceDiscipline` |
| `IsFastVoteTX`, `IsSkipVoteObj`, `IsUnlockVoteObj` | `Model/Votes.lean` — `IsFastVote`, `IsBotVote`, `IsSkipVote`, `IsUnlockVote` |
| `IsFastCertTX`, `HasCertTX`, `CertVisible`, `IsSkipCertObj`, `IsUnlockCertObj`; `DAG[r]` | `Model/Certificates.lean` — `AtLeast`, `blocksAt`, `IsFastCert`, `HasCert`, `CertVisible`, `IsSkipCert`, `IsUnlockCert`, `FastQuorumAt` |
| Lemmas single-ack, cert-unique, univalent, fast-unlock-exclusion, cert-propagation | `CertificateExclusion/` (RS2) — `HonestSingleAck`, `CertUniqueness`, `AckSkipExclusion`, `AckUnlockExclusionBelow`, `CertPropagation` |
| Consensus interface (C1)–(C4), `Dead`, `Resolves` | `Model/{Anchors, Dead}.lean` — `Anchors`, `DeadGiven`, `ResolveReadyGiven`, `ReleasedBelow`, `ResolvesAt`, `DeadAt` |
| `TryFastDecideTX`, `TrySkipDecideObj`, `FinalizeOnCommitTX`, `ResolveOnCommitObj` | `Model/Verdict.lean` — `Fate`, `FastQuorumAtInView`, `SkipQuorumAtInView`, `TxVerdict` |
| Theorem commit-safety, Lemma mixed-object safety | `TxAgreement/` (RS3) — `VerdictAgreement`, `NoConflictingFinal`, `MixedViaAnchor` |
| Lemmas fp-liveness, equiv-live; `CastVotes` | `Model/{Liveness, HonestVoting}.lean` — `PopulatedOn`, `SynchronisedOn`, `VotingRule`; `Uncontested/` (RS4) — `FastLiveness`, `FastVerdict`; `ConflictResolution/` (RS5) — `Trichotomy`, `AnchorDecides` |
| §8 certificates, refutations, moves (`Alg:FastPathPredicates5f+1`) | `Model/Five/{Certificates, Moves}.lean` — `IsAntiVote`, `IsFullCert`, `IsHalfCert`, `IsRefutation`, `IsFullUnlockCert`, `MoveDiscipline` |
| §8 freeze, `Triggers`, `TriggerAnchor`, `Frozen`, `Resolves`; `ResolveOnCommitObj`'s `F`, `W` | `Model/Five/Freeze.lean` — `AtLeastV`, `OwnedCandidate`, `Triggers`, `TriggerAt`, `Frozen`, `FreezeQuorum`, `ResolvesFiveAt`, `EligibleFive`, `FreezeDiscipline`; `Block.freezes` |
| `TryFullDecideTX`, `TryFullUnlockObj`, `ResolveOnCommitObj` | `Model/Five/Verdict.lean` — `VerdictFive` over a linear-order parameter `prio` (the min-hash tie-break, D8-style) |
| Lemmas single-stance-5f … full-cert-unique | `Five/FullCertSafety/` (RS6) — `SingleStance`, `CommitExcludesRefutation`, `UnlockExcludesRefutation`, `CommitExcludesUnlock`, `FullCertUniqueness` |
| Lemmas recovery-determinism, recovery-reflects, recovery-safety | `Five/RecoverySafety/` (RS7) — `ResolutionUnique`, `RecoveryReflects`, `RecoverySafetyBot`, `RecoverySafetyWin` |
| Theorem safety-5f | `Five/Agreement/` (RS8) — `VerdictAgreement`, `NoConflictingFinal` |
| Phase 3 of `CastVotes` (`Alg:Voting5f+1`), the coin | `Model/Five/Coin.lean` — `CoinRule` (the coin as its output `w`, D8), `StancedAt`, `AgreeUpto` (measurability, Mahi-Mahi's MM2′ pattern) |
| Lemma coin-success | `Five/CoinSuccess/` (RS9a) — `CoinConcentrated`, `CoinFragmented`, `CoinSuccessCount` (the probability bound as its numerator: a good-target set of at least `half`), `CoinMeasurable` |
| Lemma recovery-termination | `Five/RecoveryTermination/` (RS9b) — `TriggerExists`, `ResolutionExists`, `RecoveryDecides` |

Names follow the paper's where it has them (`Candidates`, `Stance`,
`HasCert`); faulty validators are Byzantine, the rest correct.

## 1. Decisions

Each decision is stated with its reason and what it changes downstream.

**D1 — Thresholds `n − f` and `2f + 1`, committees `n ≥ 3f + 1` and
`n ≥ 5f + 1`.** The paper fixes `n = 3f + 1` with every threshold
`2f + 1`, and `n = 5f + 1` with `4f + 1` and `2f + 1`. The arc's
`Faults` class assumes `3f + 1 ≤ n`; `quorum = n − f` and
`half = 2f + 1` are the two thresholds; the `Five` mixin adds
`5f + 1 ≤ n`. At the tight committees the definitions evaluate to the
paper's numbers. Reason: two quorums of `2f + 1` do not intersect in a
correct validator above `n = 3f + 1`, so the paper's constants do not
generalise and `n − f` is what every argument counts; this is the
core's convention. Consequence: the `5f + 1` section is proved for
every `n ≥ 5f + 1`, and RS1's corollaries are stated at `quorum` and
`half` so that the exposure bound *is* the `Five` premise. The two
consensusless finality quorums — the fast route's certificates and the
skip route's skip certificates, both `2f + 1` blocks in the paper — are
read at `quorum`: what certificate propagation counts, and, above
`n = 3f + 1`, a deliberate strengthening of the skip route's premise
that any skip-route liveness claim must meet.

**D2 — One owned input per transaction.** §8 defines `IsOwned` as
exactly one input; §7's `Dead` and the transaction-closed fixpoint
`RecoveryObjs` exist only to keep a validator's stance coherent across
several owned inputs. With one input the fixpoint collapses —
`RecoveryObjs(b) = ConflictedObjs(b)`, since each disjunct of `Dead`
already implies a visible conflict — and `Dead` survives only as the
filter that stops a certified transaction from being committed after
its object was released at an earlier anchor. Consequence: no closure
operator in the trusted core; multi-input transactions are a candidate
follow-up arc, not a fidelity gap of this one.

**D3 — Object versions atomic; `Spendable` dropped from
`Candidates`.** The paper's `Spendable` is a recursion on the version
index through certificates and anchors, and no safety lemma consumes
it. The arc treats an object version as an opaque element of `Obj`;
`Candidates(b, o)` is every valid transaction in `b`'s causal history
spending `o`. Consequence: the object-reuse lemma (`o^{j+1}` becomes
spendable once `o^j` is decided) is out of scope, and the gap is
recorded on the definition. The direction of the gap flips with the
side of a claim: enlarging `Candidates` is conservative inside the
safety statements, but inside the hypothesis-predicate `VotingRule` it
narrows applicability — an execution whose sole included candidate is
unspendable satisfies the paper's rule and not the arc's.

**D4 — Consensus as a chained anchor sequence.** The universe carries
the committed anchors as a sequence of block ids in the universe,
committed order being sequence order, with every earlier anchor in the
causal history of every later one. (C1)–(C3) are then the fact that the
sequence is one object; (C4) is a liveness hypothesis, anchors above
every round. The chaining is what the paper's `Dead` and `Spendable`
assume when they test an earlier anchor by `Link(A, b)` (§3, finding 3);
it is true of Mysticeti and could later be derived from the core's
`commitSeq` in a grounding phase.

**D5 — Honest behaviour in two predicates.** On correct-authored blocks
of the universe: a *safety-side* predicate — non-equivocation, the
self-parent chain, and stance monotonicity along `none → {tx, ⊥}`,
`tx → {tx, ⊥}`, `⊥ → ⊥` at `3f + 1`; at `5f + 1`, a stance changes only
on a refutation of the old stance among the round parents, a frozen
stance never changes, and a stance `tx` implies `tx` is a candidate at
that block — and a *liveness-side* predicate, the full `CastVotes` rule.
Reason: every safety lemma was traced and uses nothing beyond the
former; stating the minimum on the safety side is what makes the safety
results say what they claim about the protocol's freedom.

**D6 — Verdicts as an order-free inductive relation.** `Verdict U V tx v`
with one constructor per route — fast finality, skip, finalize at an
anchor, resolve at an anchor (commit or drop) — the paper's stateful
guards (`fastCommittedTX`, `skippedTX`, `decidedObj`, "the first
anchor") encoded as explicit least-anchor clauses, as Hydrozoan's
`Decided` encodes the nearest anchor. Consensusless routes are read
through views and under-report; anchor routes are functions of the
global data of D4. Agreement is uniqueness of `v` across views and
constructors, the shape of `SlotAgreement.DecidedUnique`.

**D7 — Equivocation voids a stance at the latest declaring round.** The
`3f + 1` predicate file voids the stance on equivocation at *any*
common round; §8 and the §7 prose void it only when the latest declaring
round holds two blocks. The arc takes the latter, the weaker premise;
the proofs need only that a correct validator's stance is unique.

**D8 — The coin is a parameter.** `coin : Obj → ℕ → Validator` is a
function of the model. The arc proves the deterministic core of the
coin lemma — if the coin selects a holder of a stance held by `2f + 1`
correct validators, or any correct validator when no stance has that
many, every correct validator holds one stance a round later — and the
cardinality of the favourable set; the probability and the expectation
bound of the latency theorem are left as arithmetic outside the arc.

**D9 — Mixed transactions as a tag.** A transaction is owned or mixed;
the consensusless routes are gated by owned. The paper's mixed-object
safety lemma is then a corollary inside RS3; its liveness lemma reduces
to (C4) and is not stated.

**D10 — One arc, results namespaced by committee.** `LeanDag/RedSnapper/`
holds a shared `Model/` — faults, blocks, transactions, stances,
anchors — and results under `RedSnapper.*` for the `3f + 1` protocol and
`RedSnapper.Five.*` for the `5f + 1` one, since the two share everything
except thresholds and the honest-move rule.

## 2. Phases

| phase | audit surface | result |
| :-- | :-- | :-- |
| 0 | this record; branch `red-snapper` | D1–D10 |
| 1 | `Model/Faults.lean`, `Model/Revocation.lean`; the committee and profile witnesses | |
| 2 | `Revocation/Statement.lean` | RS1: the support bound and the revocation threshold, its tightness, the exposure characterisation, the three corollaries at `quorum` and `half` |
| 3 | `Model/{Block, Universe, View, CausalHistory, Transaction, Stance}.lean`; witnesses for equivocation, a chain, a stance read through twins | |
| 4 | `Model/{Votes, Certificates}.lean`; `CertificateExclusion/Statement.lean` | RS2: honest single ACK, certificate uniqueness, ack/skip exclusivity, a fast commit excludes an unlock certificate, certificate propagation |
| 5 | `Model/{Anchors, Dead, Verdict}.lean`; `TxAgreement/Statement.lean` | RS3: verdict uniqueness across views and routes; no two conflicting transactions finalised; one finalised transaction per object; the mixed corollary |
| 6 | `Model/{Liveness, HonestVoting}.lean`; `Uncontested/`, `ConflictResolution/` | RS4: a sole candidate reaches fast finality in two synchronised rounds; RS5: by `r + 2` every synchronised block holds an ack certificate or an unlock certificate in its history, so every synchronised anchor above `r + 2` resolves the object |
| 7 | `Model/Five/{Certificates, Moves}.lean`; `Five/FullCertSafety/` | RS6: single stance; a full certificate excludes refutations of its ACK, a full unlock certificate excludes refutations of `⊥`, the two certificates exclude each other, and conflicting full certificates never coexist — all at `n ≥ 3f + 1` (finding 19) |
| 8 | `Model/{Block (the defaulted `freezes` field), Five/Freeze, Five/Verdict}.lean`; `Five/RecoverySafety/`, `Five/Agreement/` | RS7: resolution uniqueness; a hidden commit is reflected (`W = {tx}`, candidacy derived — finding 21); an empty election forbids any full certificate; no rival certificate above a resolution. RS8: verdict agreement and no conflicting finalisation across views and routes |
| 9 | `Model/Five/Coin.lean`; `Five/CoinSuccess/`, `Five/RecoveryTermination/` | RS9: the coin round unifies the committee — the concentrated case at any committee, the fragmented case (all movable at once) under `Five`, at least `half` good targets, and the good set fixed before a post-round draw (`AgreeUpto`); the trigger, the resolution, and a verdict for every candidate exist under the structural C4/C5 |
| 10 | this record's final position; report chapter; README; the tripwire | |

Phases 1 and 2 are reviewed together: the statement fixes what the
model must carry. Each phase runs as statements → review → freeze →
proofs and witnesses, with a cold-context vacuity auditor over the
frozen files in parallel → commit.

## 3. Findings for the paper

Recorded at Phase 0 from the reading; those the mechanisation confirms
or refines are updated at the last phase.

1. **Stale schema in the proofs.** Lemma univalent-exclusive and the
   Preliminaries refer to `noacks`/`nacks`/`unlocks` fields; the
   algorithms use `b.Stance`. Lemma finalize-safety uses
   `committedTX`/`droppedTX`; the algorithm has
   `fastCommittedTX`/`skippedTX`. Theorem commit-safety names
   `TryDirectDecide`, `TryIndirectDecide`, `ResolveOnCommitTX`.
2. **Routes count blocks, not authors.** `TryFastDecideTX` and
   `TrySkipDecideObj` test `|{b ∈ B : …}| ≥ 2f + 1`; the prose says
   "from distinct validators". Byzantine twins inflate a block count.
   The arc counts authors.
3. **"Earlier anchor" by `Link`.** `Dead` and `Spendable` test an
   earlier anchor by `Link(A, b)`; the proofs reason by commit order and
   local state. The two agree only if earlier anchors lie in later
   anchors' histories — true of Mysticeti, stated nowhere (D4).
4. **Fast commit and the unlock certificate.** The lemma's title says
   "while an unlock certificate exists"; its proof covers rounds `≤ r`,
   and the round-counting is not the reason: a correct validator at `⊥`
   never returns to `tx`. The `> r` half holds by a different argument
   (the certificate is visible from `r + 1` on, so ACKers keep their
   ACK and at most `2f` validators can retract).
5. **Case 3 of conflict resolution.** The lemma claims an unlock
   certificate forms at `r + 2`. With `f + 1` correct ACKers and
   Byzantine ACKs shown to one of them, that validator certifies and
   keeps, the others retract, and no `2f + 1` retractions exist. What
   holds, and what RS5 states, is the disjunction: an ack certificate
   in every synchronised `r + 2` block's history, or an unlock
   certificate at `r + 2`.
6. **Certificate propagation.** The proof's "a correct validator's block
   fails to link its own block" is not the argument; the induction on
   rounds with quorum intersection over authors and non-equivocation of
   correct validators is.
7. **(C5) is undefined.** Lemma recovery-termination and Theorem
   latency-5f assume it; only (C1)–(C4) exist.
8. **Half certificate versus refutation of `⊥`.** Lemmas
   unlock-excludes-half and full-excludes-unlock say a correct validator
   leaves `⊥` only on a half certificate; the algorithm's `Movable` uses
   a refutation of `⊥` — `2f + 1` non-`⊥` stances, possibly split across
   transactions. The counting closes either way; the text describes an
   older algorithm. RS6 takes the algorithm's form (confirmed by the
   mechanisation: `U6Ref`'s refutation of `⊥` is split two rival ACKs
   against two, and neither rival reaches a half certificate).
9. **Theorem safety-5f cites the wrong lemma.** "A full unlock
   certificate before `A` would have made `W` empty by Lemma
   full-excludes-unlock" needs unlock-excludes-half: permanent `⊥`
   holders leave at most `2f` frozen stances at any transaction.
10. **Skip certificates are per object.** Lemma univalent-exclusive and
    Lemma cross-route are stated "for the same `tx`".
11. **Shared-only transactions.** §7 says a valid inclusion of a
    shared-only transaction is a vote; the `Candidates` comment says
    `Valid` rejects a transaction with no owned input.
12. **Equivocation clause.** Any common round in the `3f + 1` predicate
    file; the latest declaring round in §8 and the §7 prose (D7).
13. **`Adopt` no longer links the transaction** at `5f + 1`; the
    recovery-safety step "a frozen stance `tx` places `tx` in `A`'s
    history" rests on the phase-3 guard `tx ∈ Candidates(b, o)`.
14. **`n = 5f + 1` exactly.** With thresholds `n − f` and `2f + 1` the
    section generalises to `n ≥ 5f + 1` (D1); the subsection titles'
    `n > 5f + 1` and `n > 3f + 1` are then literal.
15. **Hygiene.** §5 cites `sec:fastunlock`, `sec:fastfinality`,
    `lem:ackuniqueness`, `lem:fullcertuniqueness`, none defined;
    `3.RelatedWork.tex` and `9.parallelCertification .tex` are empty.
16. **Tightness has a side condition.** "Moreover, this threshold is
    tight" holds for `f ≤ C ≤ n` only: for `C > n` no certificate can
    form and `R = 0` suffices; for `C < f` the threshold `n + f − C + 1`
    exceeds `n` and cannot be met. RS1's `Tight` carries the condition
    (confirmed by the mechanisation: both sides are refuted by witnesses).
17. **The self-parent chain is an assumption the model never states.**
    The proofs use that a correct validator's blocks form a chain ("as it
    links its own block in every round"); the Preliminaries do not say
    so. It is indispensable, not convenient: without it a correct
    validator's earlier ACK can lie outside its later block's history,
    and the ack-versus-skip argument ("a skip voter never ACKed") does
    not close. The arc states it as `Universe.self_parent`, from which
    every correct validator has a block at every round below its own.
18. **The uncontested-liveness premise counts invalid rivals, and
    globally.** Lemma fp-liveness assumes "no conflicting transaction";
    RS4 transcribes it as no conflicting transaction *included anywhere
    in the universe*, which an included invalid rival voids (witnessed)
    although the algorithm and the conclusion are untouched, and which a
    rival first included far above the decision round voids too. The
    premise should read: no *valid* conflicting transaction included
    before certification.
19. **The `5f + 1` certificate-safety lemmas need only `3f + 1`.**
    Lemmas single-stance-5f through full-cert-unique close at any
    committee `n ≥ 3f + 1`: the persisting core of a full certificate
    has `n − 2f` correct members, the rest of the committee cannot fill
    a refutation (`2f < 2f + 1`) nor a rival quorum (`2f < n − f`), and
    no step uses `n ≥ 5f + 1`. RS6 is stated and proved without the
    `Five` mixin. The wide committee buys *exposure* — a quorum of
    votes always leaves the refutation reachable (§10's corollary,
    RS1's `ExposureAtQuorum`) — that is, the liveness of revocation,
    not its safety; the paper could say so. The parameterisation is
    load-bearing: with the literal `4f + 1` threshold the lemmas fail
    for `n ≥ 5f + 2` — the correct core is `3f + 1` and the remaining
    `n − 3f − 1 ≥ 2f + 1` validators fill a refutation — so the paper's
    fixed threshold carries a hidden *upper* bound on `n` that D1's
    `quorum = n − f` removes (compare finding 14).
20. **The recovery layer is where `5f + 1` is load-bearing.**
    Complementing finding 19: Lemma recovery-reflects and claim 1 of
    recovery-safety consume the bound — the frozen set omits at most
    `f` validators, so `|F ∩ S| ≥ 2f + 1` needs `|F| ≥ 4f + 1`, hence
    `n ≥ 5f + 1`. Claim 2 does not: an eligible transaction's `2f + 1`
    frozen supporters contain `f + 1` permanently correct ones at any
    committee. RS7 takes `Five` as a hypothesis exactly where it is
    consumed; RS8 inherits it through the reflection claim alone.
21. **Lemma recovery-reflects holds without its candidacy premise, at
    any round.** The paper assumes `tx ∈ Candidates(A, o^j)`;
    mechanised, candidacy is *derived*: a frozen correct supporter's
    marker block declares the ACK, the `Adopt` guard makes the
    transaction a candidate of the marker block, and inclusion travels
    into the resolving anchor's history. The strengthened form also
    relates the certificate's round to the resolution not at all, which
    closes Theorem safety-5f's cross-route cases — including the step
    finding 9 flags — with no case analysis on rounds.

## 4. Out of scope

- **Delivery, GST, timeouts.** Synchrony is rendered structurally as in
  Hydrozoan (`PopulatedOn`, `SynchronisedOn`); the arc grounds
  satisfiability, not operational realisability.
- **Object versioning and reuse** (D3); **multi-input transactions**
  (D2); **probabilities and the expected latency** (D8).
- **The consensus protocol itself.** Anchors are given (D4); deriving
  them from the core's Mysticeti is a possible grounding phase.
- **The probabilistic and timing remainder of §4's liveness.** Lemma
  coin-success is mechanised as its deterministic core plus the
  cardinality of the good-target set (RS9a): under a uniform draw the
  bound `half / n` is the stated numerator over the committee, and
  `CoinMeasurable` fixes the good set before a post-round draw; the
  division, independence across attempts, the geometric expectation,
  and Theorem latency-5f's round bookkeeping stay on paper. Lemma
  uncontended-liveness at `5f + 1` is isomorphic to RS4 and not
  restated; Lemma reuse-5f lives on `Spendable`, dropped by D3.
- **Execution, reverts, epoch change**, and the paper's §5 liveness
  claim for shared objects.

## 5. Layout and discipline

The arc adopts the statement/proof partition of the Hydrozoan arc
(`hydrozoan.md` §10) and is in `ARCS` of `scripts/check-arc-holes.py`.

```
LeanDag/RedSnapper/
  Model/         definitions only — no theorem and no proof term:
                 Faults, Revocation (§10), Block, Universe, View,
                 CausalHistory, Transaction, Stance, Votes, Certificates,
                 Anchors, Dead, Verdict, Liveness, HonestVoting, Five/…
  Helpers/       lemma and construction infrastructure; unaudited
  <Result>/Statement.lean   imports Model/ only; `def Statement : Prop`; never a proof
  <Result>/Proof.lean       `theorem holds : Statement`; unaudited
LeanDagTest/RedSnapper/  witness models; audited
```

Results: `Revocation` (RS1), `CertificateExclusion` (RS2),
`TxAgreement` (RS3), `Uncontested` (RS4), `ConflictResolution` (RS5),
`Five/FullCertSafety` (RS6), `Five/RecoverySafety` (RS7),
`Five/Agreement` (RS8), `Five/CoinAgreement` and
`Five/RecoveryTermination` (RS9).

**The freeze protocol.** For each phase, the audit surface — `Model/`
definitions, `Statement.lean`, witness instantiations — is written
first, in its own files, reviewed, and frozen on the author's go; proofs
are then written until they verify, with a cold-context reviewing agent
over the frozen files and the witnesses in parallel, hunting vacuous
claims and missing witnesses; its findings are relayed, fixes to frozen
files need the go again, and the phase is committed green.
Human-readable and machine-checked content never share a file.

**Relation to the core.** None consumed: the arc carries its own fault
model, blocks, universe and reachability, so that its trusted core is
exactly the paper's model. The modelling style is the core's (a
structural block universe, `Finset` counting discharged by `omega`).
