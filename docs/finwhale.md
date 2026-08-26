# FinWhale — the fast path, and what its safety proof consumes

The design record for `LeanDag/FinWhale/`. There is no report chapter
yet; this is where the reasoning behind the model lives.

The protocol is Ladelsky and Friedman, *FinWhale: An Optimally Resilient
Two-Round Terminating DAG Protocol*, arXiv:2606.26292v2 (18 August 2026).
Lemma and theorem numbers below are that version's.

## 1. What the protocol is, and what is modelled

FinWhale is Mysticeti with a fast path. The DAG and the slow-path commit
rule are Mysticeti's, in the form Starfish corrects; the addition is a
**fast path** that commits a leader block two message delays after it is
proposed, and the structures that let a validator combine the two paths
without a validator on the slow path disagreeing with one on the fast
path.

The arc models the decision layer: block validity, votes, FP-evidence,
SP-certificates, the direct commit and skip rules, the anchor, and the
reverse pass that turns them into a verdict per leader slot. It models
neither the timers nor the delivery of non-leader blocks; the network and
the round-advance loop enter only through the development's own pacing
line, which §10 uses to derive the condition liveness consumes. Every
result is about which leader slots are committed and which blocks are
delivered in what order.

**Why the DAG type is new.** FinWhale strengthens Mysticeti's validity
rule with a clause about the leader two rounds down (§2), and the fast
path's counting rests on it. `FinWhale.ValidHere` therefore has four
clauses rather than the core's three. `FinWhale.Dag` keeps a
`correct_single` field — one block per correct validator per round — as
the core does, because equivocating blocks are admitted of faulty
validators only.

## 2. The committee, and where the numbers come from

`Params` fixes `p` with `1 ≤ p ≤ f` and `n + 1 = 3f + 2p`, stated
additively so that `omega` never meets a truncated subtraction. Three
quantities follow, and the arc keeps them apart:

| Quantity | Value | Where it is used |
|:---|:---|:---|
| `quorumCard` | `n − f` | block validity: how many parents a block carries |
| `spQuorum` | `2f + p` | the slow path: certificates, votes, the skip rule |
| `fastCard` | `n − p` | the fast path: votes for a fast commit |

`spQuorum_eq_ceil` checks that `2f + p` is the paper's
`⌈(n + f + 1)/2⌉`. The three are ordered `spQuorum ≤ quorumCard ≤
fastCard`, and neither inequality is strict in general: at `p = 1` the
slow-path quorum and the validity quorum coincide, and at `p = f` the
validity quorum and the fast-path threshold do. The witnesses of §7 use
`p = 2` with `f = 2`, where the first inequality is strict.

## 3. Where the paper is read one way rather than another

Three readings are argued rather than assumed.

**Validity's leader clause is about what parents reference.** The paper
asks that a block's parent set be *leader-consistent* with respect to the
leader two rounds down, or exclude that leader's block. Leader-consistency
is a condition on the round-`r` blocks the parents vote for, not on who
authored the parents. Writing it over the parents' authors would make the
clause say something the fast path's counting does not support:
`leader_not_parent_of_exposes` needs the *exclusion* half to be about
authorship and the *consistency* half to be about references, and both
are stated that way in `ValidHere.leader_clause`.

**"Exposes equivocation" has two glosses, and they agree here.** The
paper writes that a round-`(r+2)` block exposes equivocation if "its
parent set is not leader-consistent, i.e., its causal history contains
multiple conflicting versions of the leader's block". At this depth the
two coincide: the block's parents sit at round `r + 1` and their
references at round `r`, so the round-`r` blocks in its causal history are
exactly what its parents vote for, and validity gives each parent at most
one edge per validator, so no single parent votes for two versions.
`ExposesEquivocation` is the parent-set form, which is the one validity
constrains.

**Lemma 4's proof names the wrong round.** Its equivocating case says the
block "does not reference the `r − 1` block of the Byzantine leader". The
parents of a round-`(r+2)` block are round-`(r+1)` blocks, and the block
excluded is the leader's block of round `r + 1`. The count the argument
uses — at most `f − 1` Byzantine parents — is what `parents_byzantine_lt`
states, and is unaffected.

## 4. Lemma 4, and why the committee is tight

Lemma 4 is the fast path's safety statement: if `n − p` distinct
validators vote for a leader block `b` of round `r`, then *every*
round-`(r+2)` block is FP-evidence for `b`. Both branches of the
FP-evidence definition are reached, and `Counting.lean` is the arithmetic
of each.

- A block that has not seen the equivocation carries `n − f` parents and
  meets the correct voters — at least `2f + p − 1` of them, by
  `honest_voters` — in `f + p − 1` validators (`nonequivocating_voters`).
- A block that has seen it may not reference the equivocating leader, so
  at most `f − 1` of its parents are Byzantine. Its correct parents number
  `n − 2f + 1`, of which at most `p` fail to vote (`honest_nonvoters`),
  leaving `f + p` voting for `b`, and at most `f + p − 1` voting for any
  conflicting block (`equivocating_voters`, `conflicting_voters_le`).

`equivocating_margin` is the tightness: at `n = 3f + 2p − 1` the
equivocating branch reaches exactly `f + p`, the threshold the definition
asks for, and at one validator fewer it reaches `f + p − 1`, one short,
for every `f` and `p` in range. The committee is the least at which
Lemma 4 holds.

`honest_voters` is stated as `2f + p ≤ |voters ∩ Correct| + 1` rather
than as a subtraction, for the same reason as `Params`.

## 5. The skip rule, and where correctness is genuinely consumed

The direct skip rule has two halves: a quorum of round-`(r+1)` validators
declining to vote for every block of the slot (`SPSkip`), and a quorum of
round-`(r+2)` blocks that are FP-evidence for nothing in the slot
(`NonFPEvidence`). Lemma 6 says a commit and a skip cannot both happen,
and the two halves need different arguments.

The slow-path half (`no_skip_of_quorum`) meets a quorum of voters and a
quorum of non-voters in `f + 1` validators and needs one of them to be
correct, since a correct validator's round-`(r+1)` block either references
the leader block or does not.

The fast-path half (`no_skip_of_fpEvidence`) meets a quorum of
FP-evidence blocks and a quorum of Non-FP-evidence blocks. Here the
counts are by *author*, and a distinct author is not enough: a Byzantine
author may write one block of each kind and satisfy both counts with no
contradiction. The argument needs a *correct* author, whose single
round-`(r+2)` block cannot be FP-evidence for `b` and for nothing at
once. That is the one place in the skip argument where correctness rather
than distinctness is consumed.

Lemma 9's third case — no round-`(r+2)` block is FP-evidence for a block
conflicting with a fast-committed one — is proved from the two branches
of the FP-evidence definition (`not_fpEvidence_conflicting`), not from
Lemma 4. The slow-path twin (`not_fpEvidence_of_spCertificate`) reads an
SP-certificate as a count of parents voting and runs the same case split.

## 6. The anchor, and why a deterministic tie-break is safe here

The indirect rule decides a slot from a committed **anchor** above it:
the anchor either reaches an SP-certificate for a block of the slot or
reaches a quorum of FP-evidence blocks for one. The paper notes that both
may hold at once for conflicting blocks and resolves the choice
"according to a deterministic rule".

That is the shape of the defect the Black Marlin arc reports (report
§18): a support-blind deterministic choice among an equivocator's blocks.
FinWhale escapes it, for two reasons that are separate.

**The tie-break's input is the anchor's causal history and nothing else.**
`IndirectCommit` is a predicate of the anchor, the slot and the candidate;
no view occurs in it. A validator holding the anchor holds everything the
anchor reaches, since views are closed under references
(`indirect_view_independent`), so two validators that commit the same
anchor feed the same data to the same rule. Black Marlin's descent failed
because its two validators descended from *different* anchors.

**The pattern arises only where nobody could decide directly.** A direct
commit of `b` rules out an indirect commit of a conflicting `b′` by either
path (`no_indirectCommit_of_directCommit`), and a direct skip rules out an
indirect commit outright (`no_indirectCommit_of_directSkip`).

The converse direction is Lemma 7's indirect half: a direct commit leaves
a trail every anchor at round `r + 3` or above reaches
(`indirectCommit_of_directCommit`), so the rule always has a candidate to
name. Under the slow path this is Lemma 3 (`reaches_spCertificate`);
under the fast path it is Lemma 5, and the arc proves it at any height by
descending to round `r + 3` first (`reaches_round`) and applying Lemma 4
to the parents there (`reaches_fpEvidence_quorum`). The paper's Lemma 5
concludes `n − f` FP-evidence blocks; the arc concludes `2f + p`, which
is what the indirect rule reads and is implied by the paper's count.

## 7. Lemma 12, and the interface it consumes

Lemma 12 — two validators never decide a leader slot differently — is
where the model has to be careful, because the two validators evaluate
the direct rules on *different views*.

`WellFormed` is the reverse pass as a condition on a verdict assignment
rather than as a procedure, and it takes the direct rules as parameters:
`dcommit r l` is "this validator sees a direct commit of `l` at `r`", and
`dskip r` likewise. `choose` — the deterministic tie-break — is shared,
because it reads only the anchor and the round. Giving both validators
the same direct predicates would make the theorem trivial.

`Exclusions` is what the two views must satisfy against each other, as
nine fields: the commit is unique across views, a commit in one bars a
skip in the other, a direct commit pins whatever the rule names, a direct
commit forces the rule to name something, and a direct skip bars it from
naming anything. `exclusions_of_dag` discharges all nine from the
DAG-level theorems, under the reading that a view is a sub-DAG, so a
direct verdict in a view is a direct verdict of the universe.

The induction is the paper's maximality argument, made downward-explicit.
Both DAGs are finite, so nothing above some `N` is decided, and the proof
runs on the distance from `N`. At each slot either a direct rule fires,
and the exclusions settle it, or both validators decided from an anchor.
The second case is what the induction is for: two differing anchors
would put a slot above `r` that one validator skips and the other
commits, which the induction hypothesis forbids (`anchor_unique`).

## 8. From one slot to the sequence

`commitSeq` is a validator's committed leader sequence: the committed
blocks of its decided slots, in slot order. Lemma 13 is that two such
sequences are prefix-comparable.

`linearise` is the delivery order: walk the leader sequence and after each
leader append the blocks of its causal history that have not been
delivered. Theorem 14 is that a longer leader sequence extends the
delivery order rather than revising it, because `linearise` only appends;
Theorem 15 is that no block is delivered twice, because each leader
appends only what the accumulator does not already hold. `safety`
composes Lemma 12, Lemma 13 and Theorem 14 into one statement about two
validators of one DAG.

## 9. The witnesses

`LeanDagTest/FinWhale/Model.lean` settles every definition by `decide` on
concrete executions before anything is proved from it. The committee is
`f = 2` and `p = 2`, so `n = 9`, the slow-path quorum is `6`, validity
asks for `7` parents and the fast path for `7` votes; at `p = 1` the first
two coincide and the gap between them would go untested.

Three executions, because the rules exclude one another.

- `Dfast`, four rounds: the round-0 leader block is committed by both
  paths, every round-2 block is FP-evidence for it (Lemma 4 on data), and
  a round-3 block reaches a certificate in one step.
- `Dequiv`, three rounds and a second round-0 block by the Byzantine
  leader: neither version is committed or skipped, and the two branches of
  FP-evidence separate — block `18` has seen both versions and carries the
  `f + p = 4` parents the equivocating branch asks for, block `19` has
  seen one and falls under the branch asking `f + p − 1 = 3`, and block
  `20` has seen both and carries too few of either. Validity forces block
  `18` to drop the leader's own round-1 block, which is
  `leader_not_parent_of_exposes` on data.
- `Dskip`, three rounds: no round-1 block references the leader, all nine
  validators decline, and no anchor can reverse the skip.

A fourth, `Dsync`, is the liveness input: three rounds in which every
block references the whole round below, so coverage over the correct
validators holds. The round-0 leader is correct there, and the slow-path
commit and the fast commit are both derived through §10's route rather
than settled by `decide`. The rotation is exercised too: `fwLeader` is a
`RoundRobin`, and Lemma 22 names a correct triple in the window from
round `0`.

The reverse pass has its own witness, on verdicts rather than blocks:
slots `3` to `5` committed directly, `1` and `2` skipped directly, and
slot `0` decided indirectly from its anchor, which the model shows is
slot `3` and nothing else. `WellFormed` is discharged for it field by
field, and Lemma 23 is then applied to that triple.

The list layer is exercised on concrete verdicts: a commit sequence, its
extension, and the delivery order that repeats a block of two causal
histories and delivers it once.

## 10. Liveness

Lemmas 16 and 17 are a timing argument — round synchronisation within
`∆`, and delivery before the round timeout expires — and what they
establish is a condition on the DAG: after GST every correct validator's
block references every correct block of the round below. That condition
is `SynchronisedFrom`, and this arc derives it rather than assuming it.

**The derivation is the development's own pacing line** (report §6.9). A
`ViewPace` carries view convergence — a validator's holdings reach every
other within `delay` past GST — together with the pacemaker's progress
and catch-up rules. From those, `ViewPace.driftOn_of_catchup` derives the
drift bound `delay + proc` with no hypothesis about the starting spread,
and `ViewPace.synchronisedOn_of_converges` wins the race between drift
and the timeout, giving coverage from any round past GST once the timeout
clears `2∆ + proc`. Both are the core's, used read-only.
`synchronised_of_viewPace` and `populated_of_viewPace` carry them to a
FinWhale DAG.

The bridge is a hypothesis about two structures rather than a coercion.
`ViewPace` is stated over a `BlockUniverse`, whose validity rule carries
the self-parent clause; `FinWhale.ValidHere` does not, because no result
of the safety arc reads it. The paper's block structure has it — "every
block includes an edge that references the previous block created by the
same validator" — so a FinWhale execution satisfies both rules, and the
bridge asks only that the two structures describe the same blocks.

Above coverage the rest is counting.

- **Lemma 18** is coverage read at the leader: every correct round-`(r+1)`
  block references the correct leader's round-`r` block.
- **Lemma 19**: a correct round-`(r+2)` block references every correct
  round-`(r+1)` block, each of which votes for the leader, so it carries
  `n − f ≥ 2f + p` parents voting — an SP-certificate. The paper's
  parent-selection argument is what coverage replaces: a correct leader
  does not equivocate, so the leader clause drops no correct parent.
- **Lemma 20**: those certificates number `n − f ≥ 2f + p`, which is a
  slow-path commit, at every `p` in range.
- **Theorem 21**: where at most `p` validators are actually Byzantine, the
  correct validators number `n − p`, and their votes alone are a fast
  commit.

`directCommit_of_viewPace` is the composition: a `ViewPace`, a round past
GST, the backoff, and a correct leader give a direct commit. No timing
hypothesis appears in it.

**Lemma 22, and where its proof stops working.** The lemma says any
window of `3f + 3` rounds contains three consecutive rounds with correct
leaders. The paper's proof counts maximal runs of correct leaders in the
cyclic order, then observes that such a window "contains a full cycle of
`n` rounds plus the first two rounds of the next cycle". That step needs
`3f + 3 ≥ n + 2`, and at `n = 3f + 2p − 1` it holds only for `p = 1`. For
`p ≥ 2` the window is shorter than a cycle, and the argument does not
apply.

The statement is true at every `p`, by two arguments rather than one.
`three_correct_of_roundRobin` is the cyclic half and gives a triple
within any `n + 2` rounds; it counts incidences rather than runs, which
avoids reasoning about maximal runs: if every cyclic triple held a
Byzantine leader, each Byzantine validator would answer for at most three
of the `n` triples, so `n ≤ 3f`, against `3f + 1 ≤ n`. This half uses the
fault bound alone, not `Params`. `three_correct_window` is the pigeonhole
half, for `3f + 3 ≤ n`: the window then lies inside one cycle, so its
leaders are distinct, and `f + 1` disjoint triples would need `f + 1`
distinct Byzantine validators. `lemma22` is the paper's statement, by the
first argument at `p = 1` — where `3f + 3` is exactly `n + 2` — and the
second at `p ≥ 2`.

The core's `FairRunOn` records the pigeonhole for runs of three as prose
rather than proving it, and `WaveRobin.lean` supplies runs of three by
rotating in waves instead. `three_correct_window` is that pigeonhole,
proved, for the round-robin schedule.

**Lemma 23 is a statement about one DAG, not about time.** The paper
reads it as "after GST any undecided slot eventually gets decided", where
eventually means in a later and larger DAG. Written that way it would
contradict the finiteness Lemma 12 consumes: nothing above some `N` is
decided in a DAG that stops. What holds of a single DAG is the content of
the argument, and `lemma23` states it — a slot below a committed triple
is decided. Growth enters through the hypothesis instead: a larger DAG
carries a triple further up, and every slot below it is decided.

The proof is the paper's maximality argument with the maximum made
explicit. If some slot below the triple were undecided, take the highest
such (`Nat.findGreatest`). Everything above it up to the triple is then
decided, so the first non-skipped slot above it is a commit, which is its
anchor, and `WellFormed.indirect_commit` decides it — a contradiction.
The triple is what covers the three offsets: the anchor must sit above
`r + 2`, so for a slot within two of the triple's start only its later
members qualify.

`committed_triple` supplies the triple from §10's liveness: Lemma 22
names three consecutive correct leaders, Lemma 20 commits each of their
blocks. One hypothesis carries the growth there — `hsees`, that a direct
commit of the universe is a direct commit of this validator's view. Read
the other way it says the certificates have arrived, which is the
"eventually" of the paper's statement, and it is the converse of what
`exclusions_of_dag` consumes for safety. `all_decided` composes the two,
and covers the slots before GST as well: only the triple has to sit past
the coverage round, since the reverse pass decides everything below it.

**Theorems 24 and 26.** With every slot decided, Lemma 12's agreement
becomes equality: `theorem24` says two validators deliver the *same*
sequence at a common horizon, not merely comparable ones. `lemma25` puts
a committed leader block into the commit sequence, and `mem_linearise`
puts everything in its causal history into the delivery order — either an
earlier leader delivered it, or this one does. `theorem26` is the
composition, and `reaches_of_synchronised` is the DAG-level step that
feeds it: coverage puts a correct validator's block in the causal history
of the next round's correct leader.

`delivered_of_viewPace` and `agreement_of_viewPace` are the two theorems
end to end, from a `ViewPace` and nothing else of the network. In the
second, the two finiteness conditions sit together rather than in
conflict: `hbound` says nothing above `M` is decided, and the horizon is
placed below what the DAG's own reach decides.

## 11. What is not modelled, and what is not done

`safety` states its own side conditions, and each is either a fact about
the DAG or a faithfulness condition on the model. Three are worth naming
as gaps rather than facts.

**Views are read as sub-DAGs, not modelled.** `exclusions_of_dag` takes
`∀ r l, dc r l → l ∈ slotBlocks D r ∧ DirectCommit D l` as a hypothesis.
Modelling a view as its own `Dag` and proving the direct rules monotone
under inclusion would discharge it.

**The reverse pass is a condition, not a procedure.** `WellFormed`
constrains a verdict assignment; nothing here constructs one, and nothing
shows a validator running the pass produces one.

**Termination is a hypothesis.** `hbound` says both validators have
finitely many decided slots, and `hk` says a commit sequence stops at the
first undecided slot; neither is derived.

**Liveness rests on the pacing line rather than on `∆`.** Lemmas 16 and
17 are derived from `ViewPace` rather than proved from the timeouts, as
§10 records. What that leaves outstanding is not a lemma of the paper but
the pacing structure itself: no execution is exhibited as a `ViewPace`
here, so the timing argument is discharged against the core's
formalisation of it, not against the protocol's pseudocode.

**Two hypotheses carry what growth would.** `hsees` says the deciding
validator's view holds the direct commits the universe holds, and
`hhist` says the list a leader contributes to the order is its causal
history. Both are conditions on the model rather than facts about it.
