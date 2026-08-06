# Eventual DAG Synchrony: a machine-checked account of safety and liveness for uncertified DAG consensus

**Report outline.** This document fixes the structure, definitions, assumptions
and results of the report. All displayed Lean is copied from the source and
type-checks against the built library.

*Editorial notes appear in italics and are addressed to the author; they mark
material still to be written and do not form part of the report.*

---

## Abstract

> *[To be written. The argument, in order:*
>
> *(i) DAG-based BFT protocols are widely deployed, but their liveness arguments
> are conventionally stated in terms of per-message delivery bounds, which
> obliges the entire proof to carry a time model that the commit rule itself
> never mentions.*
>
> *(ii) We propose* **eventual DAG synchrony**, *a structural condition on the
> DAG: beyond some round, every correct block references every correct block of
> the round below.*
>
> *(iii) We give a machine-checked development of safety and liveness for a
> Mysticeti-style commit rule above this condition, in which no theorem mentions
> time.*
>
> *(iv) We show this property is derived rather than assumed: it follows from
> standard partial synchrony together with the protocol's own build rules, so
> nothing beyond the conventional model is assumed.*
>
> *(v) We give its quantitative form: a correct leader is committed once correct
> validators wait 2Δ.]*

---

## 1. Introduction

### 1.1 DAG-based consensus

Validators broadcast round-indexed blocks, each referencing a quorum of blocks
from the round below. The resulting structure is a directed acyclic graph, and
consensus is obtained by reading that graph rather than by running a separate
voting protocol.

The variant treated here is *uncertified* in the sense of Mysticeti: there is no
explicit certificate round and no certificate message. A block two rounds above a
leader constitutes a certificate for it precisely when the block's own references
happen to contain a quorum of blocks that reference the leader. Certification is
therefore a property of the graph, discovered by the reader, rather than an
action taken by a writer. This is what permits the entire commit rule to be
expressed as cardinality comparisons over finite sets, and it is what makes the
development below possible with no cryptographic layer.

### 1.2 The synchrony assumption in liveness arguments

Liveness for protocols of this family is conventionally established under a
partial-synchrony assumption stated per message: after a global stabilisation
time, a message between correct parties arrives within a bound Δ. Such an
assumption obliges the argument to reason about the mechanics by which the DAG
is transmitted, in terms of individual messages, when the object being reasoned
about is the DAG itself.

Two costs follow. First, a message-level assumption obliges every subsequent
statement to be quantified over instants, and every lemma to re-establish that
enough has arrived. Second, and more fundamentally, the commit rule does not
mention time at all: it counts references. The resulting mismatch is substantial
proof effort with no corresponding proof content.

### 1.3 Contributions

1. **Eventual DAG synchrony**, formulated structurally as `SynchronisedOn`:
   beyond round `R`, every correct block references every correct block of the
   round below. The statement mentions no clock, no message and no Δ, and it is
   a *derived* property of executions rather than an assumption (§4.4).

2. A machine-checked **safety** development — agreement, uniqueness of the
   committed leader sequence, and non-retraction of the ledger — which assumes
   nothing whatsoever about the network, not even eventual delivery.

3. A machine-checked **liveness** development above the structural condition, in
   which no theorem mentions time. Priority is not claimed: Qiu, Xiao and Shao
   [QXS26] give machine-checked safety and liveness for Mysticeti in Rocq, by
   refinement into LiDO-DAG. What is claimed is the *form* of the account —
   theirs is operational, quantified over traces and instants; here liveness is
   stated as a condition on the DAG, and the dependence on time is confined to a
   single file (§6.8, §7.5).

4. **Two independent derivations** of the structural property, from an abstract
   delivery model (§6.7) and from GST (§6.8), in each case together with the
   protocol's build rules. Nothing beyond standard partial synchrony is
   assumed.

5. A precise account of the **trust boundary** (§4). What is assumed reduces to
   the fault bound and two network conditions; every other condition is a clause
   of the protocol, which a designer controls. In particular reference coverage
   is derived rather than assumed, and the one point at which a network parameter
   constrains the specification is the wait threshold of §7.1.

6. **Quantitative forms** (§6.10): the round from which coverage holds, given
   explicitly; a bound on the slot at which the next commit occurs; and an
   operational statement — a correct leader is committed once every correct
   validator waits `D₀ + Δ`, which is `2Δ` under a common start.

### 1.4 Scope and non-goals

The development is deliberately bounded in five respects.

- **No pipelined leader schedule.** `Slots.spacing` (P6) places consecutive
  leader slots at least three rounds apart, which is what makes every later slot
  available as an anchor for the indirect rule (§3.4). Mysticeti as published
  assigns a leader slot in *every* round, its logical views standing in
  one-to-one correspondence with DAG rounds, and that pipelining is the source of
  its latency claim. The object formalised here therefore has Mysticeti's
  uncertified DAG and Mysticeti's commit rule under a Cordial-Miners-like leader
  spacing. Everything stated is true of that object; the interleaving of
  simultaneously undecided slots which pipelining creates is not treated.
- **No cryptography.** Signatures, authentication and equivocation detection are
  outside the model. Non-equivocation of correct validators is a clause of the
  protocol (§4.1), recorded structurally (§2.3) and not enforced by a mechanism.
- **No executions.** The object of study is a DAG together with invariants, not
  a transition system with traces. What an operational model would establish as a
  reachability invariant of the protocol is here recorded as a structural
  condition.
- **No intra-flush ordering.** The committed-leader sequence and the ledger *set*
  are shown agreed; totally ordering the blocks released by a single commit
  requires a tie-break which the development declines to assume (§5.6).
- **No wall-clock latency.** The wait bound of §6.10 is a duration, but the total
  elapsed time to a commit is not derived (§9).

---

## 2. System model

### 2.1 Validators and the fault model

```lean
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  f : ℕ
  byzantine : Finset Validator
  card_validators : Fintype.card Validator = 3 * f + 1
  card_byzantine : byzantine.card ≤ f

def Correct : Finset Validator := (F.byzantine)ᶜ
```

A quorum is `2f+1`. The derived fact `card_correct : 2 * F.f + 1 ≤ Correct.card`
records that the correct validators themselves form a quorum, and is used at
exactly one place in the liveness development (§6.3).

As a set, `Correct` is a complement and carries no behavioural content. Membership
is satisfied, in particular, by a validator that crashes at round 0 and never
speaks again. This is deliberate: it allows every safety result to hold of
crashed validators. The behaviour of a correct validator is supplied separately,
by the protocol clauses of §4.1, and the reader should keep the two apart —
`Correct` names *which* validators execute the algorithm, while §4.1 says *what*
the algorithm is. Since a crashed validator satisfies the first and not the
second, the liveness development must invoke the protocol clauses explicitly
(§6.0).

### 2.2 Blocks and validity

```lean
structure Block (Validator BlockId Payload : Type*) where
  round : ℕ
  creator : Validator
  refs : Finset BlockId
  payload : Payload
```

Blocks are addressed by identifier: `refs : Finset BlockId` rather than
`Finset Block`. A view and the universe consequently share a single
interpretation function `U.block`, so two validators may disagree about which
blocks they hold but never about what an identifier denotes. `Payload` is opaque
and plays no role.

```lean
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  quorum : 0 < b.round → 2 * F.f + 1 ≤ (creators blk b).card
```

Three points of formulation are load-bearing.

The predecessor condition is stated additively rather than as
`(blk i).round = b.round - 1`. Besides avoiding truncated subtraction on `ℕ`,
this makes the genesis case derivable rather than a separate branch: at round 0
the equation `(blk i).round + 1 = 0` is unsatisfiable, so `refs = ∅` follows
(`ValidWrt.refs_empty_of_round_zero`).

The quorum condition is stated on the *creator set*, not on `refs.card`. This is
the faithful reading of "references 2f+1 blocks of the previous round", which
means 2f+1 distinct *validators*; `ValidWrt.card_creators` and `ValidWrt.card_refs` relate the two
under the distinctness condition.

`distinct_creators` is used in exactly one proof, that of certificate uniqueness
(§5.4).

### 2.3 The block universe and views

```lean
structure BlockUniverse (Validator BlockId Payload : Type*) … where
  ids : Finset BlockId
  block : BlockId → Block Validator BlockId Payload
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  valid : ∀ i ∈ ids, ValidWrt block (block i)
  no_equivocation : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator ∈ Correct →
    (block i).creator = (block j).creator →
    (block i).round = (block j).round → i = j
```

Non-equivocation is stated at the level of the universe, and must be. A
per-view formulation is strictly weaker: two views could each satisfy "at most
one block per correct author per round" while holding *different* such blocks,
which is precisely a correct validator equivocating, with both views
well-formed. Every cross-view result requires the two blocks to be identified as
a single identifier, and only a universe-level statement delivers this. Views
inherit the property, which is why `View` carries no corresponding field.

The condition is independent of the others: duplicating a correct-authored block
under a fresh identifier preserves `complete` and `valid` and violates only
`no_equivocation`.

It is also the sole point at which the behaviour of a correct validator is
recorded on the safety side, and it is a clause of the protocol rather than an
assumption (P5): a correct validator produces one block per round because the
algorithm so directs. Since the object of study is a DAG rather than an
execution (§1.4), the clause appears as a structural condition on the universe;
in an operational model it would be established as an invariant of reachable
states.

```lean
structure View (Validator BlockId Payload : Type*) … (U : BlockUniverse …) where
  ids : Finset BlockId
  subset_ids : ids ⊆ U.ids
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids
```

A view is a downward-closed subset of the universe sharing its interpretation
function, and inherits validity and non-equivocation.

Both `ids` fields are finite sets. Finiteness is not incidental: it is what gives
`authorsAt` a cardinality, and every quorum argument in the development counts
one. It also determines the shape of the growth clause P8 (§6.3).

### 2.4 Causal history

```lean
def RefStep (U) (i j : BlockId) : Prop := j ∈ (U.block i).refs
def Reaches (U) : BlockId → BlockId → Prop := Relation.ReflTransGen (RefStep U)
```

### 2.5 Notation for counting

| Notation | Meaning |
|---|---|
| `blocksAt U n` | the identifiers in `U` at round `n` |
| `authorsAt U n` | their creators |
| `creatorsOf U.block s` | the creators of an arbitrary set of identifiers |
| `supporters U b n` | round-`n` authors whose blocks reference `b` |
| `correctSupporters U b n` | those among them that are correct |
| `blames U L n` | round-`n` authors whose blocks omit `L` |

`creatorsOf` is defined on an arbitrary `Finset BlockId` rather than on a
block's references, since the persistence theorem, the commit rule and the
block-level intersection lemma all quantify over identifier sets that are not
any block's references. Such sets carry no distinctness invariant of their own,
which is why every quorum hypothesis in the development is stated on the creator
set: a Byzantine author could otherwise inflate a set with equivocating blocks.

---

## 3. The commit rule

Validators emit a single kind of object, the block of §2.2. Every role described
below is assigned by the reader of the DAG, not by its writer.

### 3.1 Certificates

```lean
def votesIn (U) (C L : BlockId) : Finset BlockId :=
  (U.block C).refs.filter (fun q => L ∈ (U.block q).refs)

def Certifies (U) (C L : BlockId) : Prop :=
  2 * F.f + 1 ≤ (creatorsOf U.block (votesIn U C L)).card

def certificates (U) (L : BlockId) (r : ℕ) : Finset BlockId :=
  (blocksAt U (r + 2)).filter (fun C => Certifies U C L)
```

A round-`(r+2)` block certifies a round-`r` block `L` exactly when its own
references contain blocks by a quorum of distinct validators, each of which
references `L`.

> *[Figure 1]* Three rounds: `L` at round `r`; voters at `r+1` whose references
> contain `L`; a certificate at `r+2` whose references contain a quorum of those
> voters.

### 3.2 The direct rules

```lean
def DirectCommit (U) (L : BlockId) (r : ℕ) : Prop :=
  2 * F.f + 1 ≤ (creatorsOf U.block (certificates U L r)).card

def DirectSkip (U) (L : BlockId) (r : ℕ) : Prop :=
  2 * F.f + 1 ≤ (blames U L (r + 1)).card
```

A validator applies these to what it holds. The view-relative forms
`DirectCommitIn` and `DirectSkipIn` intersect the relevant sets with `V.ids`;
`directCommit_of_directCommitIn` and `directSkip_of_directSkipIn` record that a
view can only under-report, so that a local judgement is always a genuine
universe-level one and the universe-level theorems apply without recounting.

### 3.3 The indirect rule

A slot which the direct rules leave undecided is settled by examining the causal
history of a later, committed *anchor*.

```lean
def CertifiedIn (U) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ C ∈ certificates U L r, Reaches U A C
```

This test is universe-level by design. `certifiedIn_iff_of_view` establishes that
restricting the search to a view holding the anchor yields the same answer, so
nothing is lost; and the universe-level formulation is what makes decisions
monotone under view growth (§6.5). Were the test view-relative, the premise of
the indirect *skip* rule would be anti-monotone, and enlarging a view could
convert a skip into a commit.

### 3.4 The slot schedule

```lean
class Slots (Validator : Type*) where
  slotRound : ℕ → ℕ
  leader : ℕ → Validator
  spacing : ∀ k, slotRound k + 3 ≤ slotRound (k + 1)

def IsLeaderBlock (U) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k
```

The spacing of three rounds is a safety parameter rather than a throughput one:
it is exactly what places every subsequent anchor at round `≥ r+3`, which is the
hypothesis of the agreement between the direct and indirect rules (§5.3), and
`slotRound_add_three_le` extends it to arbitrary later slots.

`IsLeaderBlock` characterises the *candidates* for a slot rather than selecting
one. A Byzantine leader may have several; a correct leader has at most one, by
non-equivocation. Quantifying over candidates is what allows the case of an
absent leader to be discharged vacuously (§6.6).

### 3.5 The decision relation

```lean
inductive Decided (U) (V : View …) : ℕ → Option BlockId → Prop
  | directCommit {k L} :
      IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      Decided U V k (some L)
  | directSkip {k} :
      (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      Decided U V k none
  | indirectCommit {k j A L} :
      k < j → Decided U V j (some A) → (∀ i, k < i → i < j → Decided U V i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      Decided U V k (some L)
  | indirectSkip {k j A} :
      k < j → Decided U V j (some A) → (∀ i, k < i → i < j → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      Decided U V k none
```

Here `some L` records a commitment and `none` a skip.

The relation is not a function. A decision procedure would recurse upward in
slot index with no *a priori* bound, requiring fuel or partiality for no benefit,
since nothing in the development needs to compute.

The two indirect cases anchor on the *nearest* committed slot above `k`. The
direct reading of "nearest" — that no slot strictly between is committed — is a
negative premise, which an inductive definition cannot carry. It is stated
positively, as the requirement that every slot strictly between be decided
`none`. The two are equivalent, since the sweep decides every slot it passes,
and the positive form keeps every recursive occurrence strictly positive. This
formulation is consumed directly in the principal case of the agreement proof
(§5.5).

### 3.6 The ledger

```lean
def commitSeq (g : ℕ → Option BlockId) (n : ℕ) : List BlockId :=
  (List.range n).filterMap g

def ledgerSet (U) (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ Reaches U L b}

def OutputAt (U) (g : ℕ → Option BlockId) (b : BlockId) (k : ℕ) : Prop :=
  (∃ L, g k = some L ∧ Reaches U L b) ∧
    ∀ j, j < k → ∀ L, g j = some L → ¬ Reaches U L b
```

Committing the leader of a slot releases its entire causal history. `OutputAt`
identifies the slot at which a block first enters the ledger. Here `g` ranges
over a validator's assignment of verdicts to slots.

---

## 4. The trust boundary

Three kinds of condition appear in the development, and the report distinguishes
them throughout, because they differ in who controls them.

**Specification.** A *correct* validator is by definition one that executes the
algorithm. The clauses of §4.1 are therefore not hypotheses about an uncertain
world; they are the algorithm, and a designer is free to choose them.

**Fault model.** How many validators fail to execute the algorithm, and how
their number is bounded (§4.2). Assumed.

**Network.** Delivery. The network is adversarial and lies outside the trusted
computing base (§4.3). Assumed.

Logically all of these are antecedents: each is a field of a structure or class,
and every theorem quantifying over a block universe or over the relevant
instances carries it. None is an axiom in the sense of §10, and their joint
satisfiability is a proof obligation discharged by exhibition (§8) rather than
something the logic must be trusted for. The distinction drawn here is
epistemic, not logical, and it is what determines where the trust boundary of
the system actually falls.

### 4.1 The protocol

| | Clause | Formalisation |
|---|---|---|
| P1 | references lie one round below | `ValidWrt.predecessor` |
| P2 | no block cites one author twice | `ValidWrt.distinct_creators` |
| P3 | non-genesis blocks cite `2f+1` distinct authors | `ValidWrt.quorum` |
| P4 | a block is held only with its causal history | `BlockUniverse.complete` |
| P5 | one block per round: correct validators do not equivocate | `BlockUniverse.no_equivocation` |
| P6 | slots are at least three rounds apart | `Slots.spacing` |
| P7 | a validator references everything it held | `Delivery.includes` |
| P8 | a validator has a genesis block, and builds on holding a quorum | `Live.genesis`, `Live.builds` |
| P9 | a validator waits a full timeout, and does not dawdle | `Timing.waits`, `Timing.prompt` |
| P10 | the leader schedule names reliable validators arbitrarily far out | `FairScheduleOn` |

P1–P6 are consumed by the safety development, P7–P10 additionally by liveness.

P10 is a joint condition rather than a pure specification: the schedule is the
designer's, but which validators are reliable is not. Round-robin discharges it
whenever the reliable set is of quorum size, since at most `f` of every `3f+1`
consecutive leaders then lie outside it; `rrSlots` witnesses this with a window
of `f + 1` (§8).

**P8 deserves the most emphasis of any clause here**, and is easily mistaken for
a routine one. It states that a correct validator holding a quorum at round `r`
*has* a block at round `r+1`; equivalently, that correct validators do not
advance past a round without building in it. Qiu, Xiao and Shao [QXS26] show
this clause cannot be dropped: with honest validators free to jump over rounds,
they exhibit an infinite execution of Mysticeti in which at most `2f`
certificates are ever created for any round, so no slot is directly committed
and — direct commitment being what the indirect rule rests on — nothing is
committed at all. Their fix is a restriction on round-jumping; Starfish [PMV25]
adds the same condition as pacemaker rule A2, requiring a validator to have
created its round-`(r-1)` block before advancing to round `r`. The clause is also
not automatic in practice: [QXS26] audited the Sui implementation and found it
susceptible to exactly this attack.

So P8 is the point at which the liveness development is conditional on something
that deployed code has been observed not to satisfy. It is nonetheless a clause
of the protocol in the sense of this section — a designer can implement it, and
both cited works tell one how — which is why it appears here rather than in §4.3.
The form assumed here is stronger than either published fix: `Live.builds`
demands a block at every round unconditionally, where [QXS26] excuse a validator
that has already decided round `r'-2`, and admit a *global catchup time* before
which the rule need not hold. No minimality is claimed for the clause.

P2 is a second place where the model does not simply transcribe the protocol.
Mysticeti's validity check requires a block to cite `2f+1` *distinct* authors at
the round below but does not forbid citing an equivocating author's second block
as well; uniqueness of support is recovered instead by defining a supporter to be
one that references the *first* leader-slot block among its references. P2
forbids the duplicate citation outright, and uniqueness then follows without a
tie-break — this is P2's sole use, in M5′ (§5.4). The two devices agree in
effect, but P2 is the stronger requirement, and a reader comparing the model
against a deployed implementation will find a validity condition Mysticeti does
not impose.

P5 deserves emphasis, since it is conventionally described as an assumption. It
is a clause of the algorithm — a correct validator produces one block per round
because that is what it was told to do — and it is the sole point at which the
behaviour of a correct validator is recorded on the safety side. Nothing else in
the model constrains it, `Correct` being a set complement (§2.1).

P9 is the clause whose *sufficiency* is not under the designer's control: the
timeout may be chosen freely, but whether the chosen value is long enough
depends on the network. §6.10 determines the threshold it must meet, and §7.1
discusses the consequences.

### 4.2 The fault model

| | Assumption | Formalisation |
|---|---|---|
| A1 | there are `3f+1` validators | `Faults.card_validators` |
| A2 | at most `f` are Byzantine | `Faults.card_byzantine` |

Byzantine validators are unconstrained: they may publish nothing, publish
selectively, or equivocate freely.

**The combined budget.** The principal liveness argument counts to `2f+1` and no
higher, so what it requires is a quorum of validators that are both correct and
timely, rather than the participation of every correct one. Formulating this as
`T ⊆ Correct` with `2f+1 ≤ T.card` — a hypothesis of L4 and L6 — yields the
operative budget:

> `actual_byzantine + persistently_slow_correct ≤ f`

A correct validator which is persistently slow consumes budget exactly as a
Byzantine one does. This is a hybrid condition: correctness is a fault-model
matter, timeliness a network one. At `f = 1` there are four validators and
`|Correct| = 3 = 2f+1` exactly, so no slack exists and every correct validator
must be timely; slack appears only when fewer than `f` validators are in fact
faulty, and the `T`-parameterised statements make it available automatically.
The specialisations at `T := Correct` (`directCommit_of_correct_leader`,
`decided_of_correct_leader`, `commits_recur`) recover the conventional
statements.

### 4.3 The network

| | Assumption | Formalisation |
|---|---|---|
| N1 | a quorum that exists is eventually held | `DeliversQuorum` |
| N2 | beyond GST, a block is delivered within Δ | `Timing.covers`, `EventuallyDelivers` |

N1 requires eventual delivery only, not synchrony, and is what carries the
results holding before GST. N2 is partial synchrony in the standard sense.

**These two are the whole of the trust placed in the environment.** The safety
results of §5 use neither: they hold under arbitrary asynchrony, arbitrary loss
and arbitrary divergence between views.

### 4.4 Derived, not assumed

Eventual DAG synchrony is not an assumption of the development. It is a property
of executions, obtained from the network assumption together with the protocol:

| Route | From | Result |
|---|---|---|
| Delivery | N2 (`EventuallyDelivers`) with P7 | `synchronised_of_delivery` |
| Timing | N2 (`Timing.covers`) with P9 | `Timing.synchronisedOn_of_timing` |

It is stated as a hypothesis of L4 and L6 in order to keep those arguments free
of temporal notions (§6.9), and supplied to them by the results above. §7
discusses the formulation.

**What "derived" does and does not mean here.** Both routes derive coverage from
a network assumption *together with clauses of the protocol* — P7 on the delivery
route, P9 on the timing route — and both are consumed by L4 alongside `Populated`,
which comes from P8. The claim is therefore not that eventual DAG synchrony holds
in any execution of any DAG protocol; it is that it need not be *postulated*
separately, because the network assumption already standard in this literature,
combined with build rules a designer controls, entails it.

The distinction matters because the corresponding claims in the source literature
have not survived scrutiny. Mysticeti's Lemma 8 and Cordial Miners' Proposition
38 both assert that honest validators are synchronised after GST; [PMV25] reports
that both leave gaps, and [QXS26] shows the gap is not merely expositional — with
round-jumping unrestricted the conclusion is false. The present development is
not exposed to that counterexample, but the reason is P8, which excludes
round-jumping by fiat (§4.1). Read correctly, this is the stronger position: it
identifies precisely which protocol clause the structural condition is bought
with, rather than asserting the condition and leaving the price implicit.

### 4.5 Quantitative clauses

The results of §6.10 require the following in addition. R1–R3 are further
specification, strengthening clauses already present; only the round-`0` spread
of R4 is an assumption, and it concerns deployment rather than the network.

| | Clause | Kind | Yields |
|---|---|---|---|
| R1 | `Rated timeout`: `∀ n, n ≤ timeout n` | specification | an explicit round `R` |
| R2 | `FairWithin T w`: a `T`-leader within every window of `w` slots | specification | a bounded committing slot |
| R3 | `BoundedSpacing s`: slots at most `s` rounds apart | specification | that slot's round, and a horizon |
| R4 | `∀ n, D₀ + Δ ≤ timeout n`, with round-`0` spread at most `D₀` | specification; `D₀` deployment | the wait bound `Delay(Δ)` |

Every result of §5 and §6.1–§6.9 stands without them.

**R4's deployment component is avoidable.** `driftFrom_of_prompt` shows drift is
*preserved*, not established, so a bound on the round-`0` spread has to be
supplied from outside; `D₀` is the only quantity in the development whose value
depends on how validators are started rather than on the network or the
specification. Starfish [PMV25] obtains the corresponding statement — its Lemma
4, that honest validators enter every round past GST within Δ of each other — as
a consequence of a further protocol clause rather than as a hypothesis: its rule
B2 requires a validator to broadcast its unknown history on *advancing a round*,
not only on creating a block. Adopting such a clause would discharge the
round-`0` spread instead of assuming it, and would remove the only deployment
assumption in §4. It is not adopted here, and B2 has no force in the present
model in any case, since P8 makes advancement and block creation coincide.

---

## 5. Safety

### 5.1 Quorum intersection and non-equivocation

**T0.**
```lean
theorem exists_correct_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : 2 * F.f + 1 ≤ Q₁.card) (h₂ : 2 * F.f + 1 ≤ Q₂.card) :
    ∃ v ∈ Q₁ ∩ Q₂, v ∈ (Correct : Finset Validator)
```

Its block-level counterpart T0′ (`exists_correct_mem_creators_inter`) states that
two identifier sets whose creator sets are quorums share a correct author.

**T1.**
```lean
theorem BlockUniverse.eq_of_creator_eq {v : Validator} {i j : BlockId}
    (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∈ Correct)
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) : i = j
```

The statement is organised around the author `v` rather than around
`(U.block i).creator`, since that is the form in which every use site arrives: a
quorum intersection yields a correct validator, and T1 converts two blocks known
to be authored by it into a single identifier.

The composite `BlockUniverse.exists_common_mem_of_quorums` combines the two: two quorum-backed
sets of round-`n` blocks share a *block*. This is the recurring step by which one
layer of certification is removed.

**T2** (`round_le_of_reaches`) states that causal history is non-increasing in
round.

**T6a.**
```lean
theorem View.mem_of_reaches (hc : c ∈ V.ids) (h : Reaches U c b) : b ∈ V.ids
theorem View.exists_reaches_iff (hc : c ∈ V.ids) :
    (∃ b, b ∈ V.ids ∧ P b ∧ Reaches U c b) ↔ (∃ b, P b ∧ Reaches U c b)
```

Causal history does not escape a view. The second form is what makes a
view-relative certificate search well defined: two validators holding different
views but the same anchor cannot disagree about its outcome.

### 5.2 Persistence

**T3.**
```lean
theorem reaches_of_quorum_support
    {b : BlockId} {r : ℕ} {Q : Finset BlockId} (hQ : Q ⊆ U.ids)
    (hQround : ∀ q ∈ Q, (U.block q).round = r + 1)
    (hQref : ∀ q ∈ Q, b ∈ (U.block q).refs)
    (hQquorum : 2 * F.f + 1 ≤ (creatorsOf U.block Q).card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 2 ≤ (U.block c).round) :
    Reaches U c b
```

Once a quorum of round-`(r+1)` blocks references `b`, every block from round
`r+2` onwards has `b` in its causal history. Neither membership of `b` in the
universe nor its round need be assumed; both follow from the quorum hypothesis
(`mem_ids_and_round_of_quorum_support`).

The bound `r+2` is tight.

> *[Editorial: reproduce the counterexample at `r+1`. With `f = 1` and validators
> `{A,B,C,D}`, let `b` be `A`'s round-`r` block, referenced by the round-`(r+1)`
> blocks of `A`, `B` and `C`; `D`'s round-`(r+1)` block may reference `{B,C,D}`
> instead, and since all its references lie at round `r`, it does not reach `b`.
> Quorum intersection requires two reference quorums to compare, and `r+2` is the
> first round which supplies them.]*

Quorum intersection is used exactly once, in the base case; height above that
layer is carried by transitivity alone (`reaches_pred_of_round_le`).

**T3c.**
```lean
theorem exists_common_correct_ancestor {r : ℕ} {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ Correct ∧
      ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c bw
```

The sole premise is that some round-`(r+2)` block exists — a fact about the DAG
in hand rather than an assumption that any party makes progress. The proof rests
on a double-counting argument (T3a, `exists_correct_common_support`).

> *[Editorial: state the counting. Each correct round-`(r+1)` block names at
> least `2f+1-b` correct round-`r` authors, and there are `l` such blocks spread
> over `c = 3f+1-b` correct validators, so some author collects at least
> `l(2f+1-b)/c`. The arithmetic obligation reduces to `c² ≤ f(l+c)`, which
> `l ≤ c` converts to `c ≤ 2f`, contradicting `c ≥ 2f+1`.]*

### 5.3 Consistency of the direct rules

**M3** (`certificates_eq_empty_of_directSkip`). A directly skipped block has no
certificate anywhere in the universe, not merely none within some view. Given
`2f+1` blamers, and since a correct validator cannot appear on both sides
(`blames_inter_supporters_subset_byzantine`), the supporters number at most `2f`
(`card_supporters_le_of_card_blames`), one short of a quorum.

The universe-wide strength is what allows a skip to require no anchor to justify
it, and it is what makes the skip half of M4 unconditional.

**M1** (`not_directCommit_of_directSkip`) follows immediately.

**M2** (`exists_certificate_reaches_of_directCommit`). Once a block is directly
committed, its certificate is unavoidable: every block from round `r+3` onwards
has one in its causal history. The bound is tight, since a round-`(r+2)` block
which is not itself a certificate reaches none. This is the origin of P6.

**M4** (`indirect_agrees_with_direct`). Where the direct rule decides, the
indirect rule agrees. The two halves are asymmetric: the commit half requires the
anchor to lie at round `≥ r+3`, since the certificate must be reachable, whereas
the skip half requires no hypothesis at all, since by M3 no certificate exists
anywhere to be reached.

### 5.4 Certificate uniqueness

**M5′.**
```lean
theorem eq_of_certificates_nonempty {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : (certificates U L₁ r).Nonempty) (h₂ : (certificates U L₂ r).Nonempty)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂
```

A slot admits at most one certifiable block. This is stronger than the
corresponding statement about direct commits, and it is the form the indirect
rule requires, since that rule commits on the strength of a single certificate
lying in reach rather than of a quorum of them.

The proof requires no relationship between the two certificates. Each names
`2f+1` distinct voters, so the voter sets intersect in a correct validator `w`
(T0′); `w`'s unique round-`(r+1)` block votes for both (T1); and P2 forbids one
block from referencing two round-`r` blocks by a single author. This is the only
use of P2 in the development.

**M5** (`eq_of_directCommit_of_creator_eq`) follows as a corollary.

### 5.5 Agreement

**M6.**
```lean
theorem decided_agree {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : Decided U V₁ k v₁) (h₂ : Decided U V₂ k v₂) :
    v₁ = v₂
```

No two validators reach conflicting decisions for a slot, whatever views they
hold and by whichever route they decided. As is conventional, this is a
*no-conflicting-decision* statement: a validator which has not yet decided is not
in disagreement.

The proof (`decided_unique`) is by structural induction on the first derivation.
Of the sixteen pairings of constructors, fifteen close directly — commitment
against commitment by M5′, and the crossings of direct against indirect by the
cross-view form of M1, by `certifiedIn_of_directCommitIn`, or by M3. The
remaining case, indirect commitment against indirect skip, is settled by
trichotomy on the two anchors, and it is here that the positive formulation of
"nearest anchor" (§3.5) is consumed: the negative reading supplies no
sub-derivation on which the induction could rest.

> *[Figure 2]* The principal case: two validators, two anchors, and the
> trichotomy on their indices.

Two corollaries are stated in the form applications require:
`eq_of_decided_commit` (no two validators commit different blocks for a slot) and
`not_decided_skip_of_decided_commit` (no validator skips a slot another has
committed).

### 5.6 Ledger stability

```lean
theorem commitSeq_agree
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    commitSeq g₁ n = commitSeq g₂ n

theorem ledgerSet_mono  (h : n ≤ m) : ledgerSet U g n ⊆ ledgerSet U g m
theorem ledgerSet_agree …             : ledgerSet U g₁ n = ledgerSet U g₂ n
theorem outputAt_unique (h₁ : OutputAt U g b k₁) (h₂ : OutputAt U g b k₂) : k₁ = k₂
theorem outputAt_agree  … (hk : k < n) (ho : OutputAt U g₁ b k) : OutputAt U g₂ b k
```

Two validators which have settled the first `n` slots read off the same sequence
of committed leaders; the ledger grows monotonically; the two validators output
the same set of blocks; and each block enters at exactly one slot, on which they
agree.

None of these statements mentions an order on identifiers. Ordering the blocks
released by a single commit requires a tie-break — a linear order on identifiers
or an equivalent — which the development deliberately does not assume. Whether
and when a block is output requires no order, and it is precisely these
properties that retraction would violate.

---

## 6. Liveness

### 6.0 What liveness requires beyond membership of `Correct`

Membership of `Correct` says which validators execute the algorithm; it says
nothing about what the algorithm does (§2.1). Liveness statements are therefore
vacuous until the relevant protocol clauses are invoked, and three are:

- **(a)** validators produce blocks (P8);
- **(b)** validators wait before building, and do not dawdle (P9);
- **(c)** the schedule names reliable leaders arbitrarily far out (P10).

Clauses (a) and (b) act in opposition, and P9 brackets them precisely: `prompt`
is a ceiling, requiring that a validator eventually build; `waits` is a floor,
requiring that it not build too early.

Reference coverage is not among them. It is not a clause a validator could
execute, since it refers to `Correct`, which no validator can observe; it is
what (a) and (b) *produce* against a synchronous network, and it is derived
accordingly (§4.4, §7.2).

### 6.1 Density

**L0.**
```lean
theorem card_authorsAt_of_lt {r n : ℕ} (hn : n < r) {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    2 * F.f + 1 ≤ (authorsAt U n).card
```

If any block exists at round `r`, every round below `r` has at least `2f+1`
distinct authors. The result requires no assumption beyond validity. Its content
is not that the DAG grows, but that it cannot grow tall and thin: a single block
high in the DAG forces a quorum of authors at every round beneath it.

### 6.2 The delivery layer

```lean
structure Delivery (U) where
  held : Validator → ℕ → Finset BlockId
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  includes : ∀ v ∈ Correct, ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    held v n ⊆ (U.block b).refs

def DeliversQuorum (D : Delivery U) : Prop :=
  ∀ n, 2 * F.f + 1 ≤ (authorsAt U n).card →
    ∀ v ∈ Correct, 2 * F.f + 1 ≤ (creatorsOf U.block (D.held v n)).card
```

The indexing of `held` is essential: `held v n` denotes what `v` had in hand *at
the moment it built its round-`(n+1)` block*, not what `v` eventually receives.
This is the build-time index which a view cannot supply (§7.1).

The structure contains no clock. In the absence of a time model, "waited longer"
can manifest only as a larger `held`, which is what allows the timing layer of
§6.8 to be placed beneath without disturbing anything above it.

`DeliversQuorum` is stated conditionally — existence of a quorum first, holding
of one second — since unconditionally it would assert the very block production
that §6.3 sets out to establish. It carries no round bound, and so holds before
GST as well as after.

### 6.3 Progress, and the horizon

```lean
def PopulatedOn (U) (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r

structure Live (U) (D : Delivery U) (N : ℕ) : Prop where
  genesis : Populated U 0
  builds : ∀ r < N, ∀ v ∈ Correct,
    2 * F.f + 1 ≤ (creatorsOf U.block (D.held v r)).card →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r + 1
```

**L1.**
```lean
theorem no_stall {D : Delivery U} (H : Live U D N) (hd : DeliversQuorum D) :
    ∀ r ≤ N, Populated U r
```

Every correct validator has a block at every round up to the horizon. The
induction proceeds in two steps: the inductive hypothesis makes `Correct` a
subset of `authorsAt U r`, so a quorum exists; `DeliversQuorum` converts this
into each correct validator *holding* a quorum; and only then does `builds`
apply. The second step is what prevents the theorem from asserting that
validators build upon blocks they may never have received.

The horizon `N` is not a technical convenience. Since `U.ids` is finite, a
formulation without the bound `r < N` would require infinitely many distinct
blocks in a finite set, so that no universe satisfies it and every theorem
assuming it is vacuous.

Three consequences follow.

First, `N` is a demand upon the DAG rather than a bound upon it: `Live U D N`
requires that correct validators actually possess blocks at every round up to
`N`, so that a larger `N` is a *stronger* hypothesis satisfied by *fewer*
universes. Generality is obtained by universal quantification over `N`, not by
choosing it large.

Second, `N` and `R` measure independent quantities — extent and quality
respectively — and all four combinations occur.

> *[Editorial: reproduce the 2×2 table. `N` large with `R` small: tall and
> synchronous, commits. `N` large with `R` large or never: grows, commits
> nothing. `N` small with `R` small: synchronous but too short to commit. `N`
> small with `R` large: short and asynchronous.]*

Third, unboundedness becomes a property of a *family* of universes. The assertion
that the ledger grows without bound is not that one DAG commits infinitely often
— no finite DAG can — but that no slot is the last one which some sufficiently
grown DAG commits.

L1 is the only result in which the horizon does any work; the principal
commitment theorem does not mention `N`.

### 6.4 Eventual DAG synchrony

```lean
def SynchronisedOn (U) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ T →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ T → a ∈ (U.block b).refs
```

The condition is restricted to correct authors on both sides, and both
restrictions are load-bearing.

Nothing may be assumed about the existence of Byzantine blocks: a Byzantine
validator may publish nothing, or publish and reveal selectively, so no argument
may depend upon its blocks being available. Nothing need be assumed either, since
the commitment argument counts only correct certificates and the correct
validators form a quorum. The stronger reading — that every block is referenced —
would amount to assuming that Byzantine validators behave.

Well-formedness survives the restriction: a correct block referencing every
correct block of the round below already names at least `2f+1` distinct creators,
so P3 is satisfied without any Byzantine reference.

The predicate is antitone in `T` (`SynchronisedOn.mono`), which allows results
established at `T := Correct` to be supplied to the quorum-relative statements of
§6.6.

The condition is derived, not assumed (§4.4); §7 discusses its formulation.

### 6.5 Monotonicity and propagation

**L2.**
```lean
theorem decided_mono (hsub : V.ids ⊆ V'.ids) (h : Decided U V k v) : Decided U V' k v
```

A validator never revises a decision as its view grows. This is to be
distinguished from the safety results: those establish that decisions do not
*conflict*, whereas this establishes that they do not *change*. The proof rests on
the universe-level formulation of the indirect test (§3.3).

**L3.**
```lean
def View.full (U) : View Validator BlockId Payload U   -- ids := U.ids
theorem decided_full (h : Decided U V k v) : Decided U (View.full U) k v
```

Every verdict reached on any view holds on the full view. Since the full view is
every correct validator's eventual view, this is the formal content of the
informal claim that all correct validators eventually reach the same decision. It
also fixes the interpretation of `U`: not every block anyone ever wrote, but every
block some correct validator ever held. A Byzantine block revealed to nobody is
simply not in the universe.

### 6.6 Commitment, skipping and recurrence

**L4.**
```lean
theorem directCommit_of_leader_mem (hcard : 2 * F.f + 1 ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

with `decided_of_leader_mem` giving the corresponding statement about `Decided`.

The intermediate step, `certifies_of_synchronisedOn` — a correct round-`(r+2)`
block certifies any correct round-`r` block — is the statement appearing as Lemma
10 of Mysticeti, that after GST every honest validator eventually creates a
certificate for a leader block created by an honest validator. That lemma is the
one Sailfish identified as flawed and [QXS26] refuted outright. It is a theorem
here, and its hypotheses show why: `PopulatedOn` at rounds `r+1` and `r+2`
requires *every* validator of `T` to have a block at those rounds, and the
counterexample of [QXS26] is precisely a countermodel to that, arranging for only
`f+2` to `f+3` of the `2f+1` honest validators to build in any given round. The
counterexample therefore refutes neither L4 nor anything else below; what it
refutes is the availability of L4's hypothesis under Mysticeti as published, and
so, in the terms of §4.1, it refutes P8 (§4.4).

The argument consists of two applications of coverage and nothing further. Every
correct round-`(r+1)` block references `L`, since `L` is correct-authored and
coverage applies at round `r`; every correct round-`(r+2)` block references all
of those, so its votes for `L` originate with every correct validator and hence
with a quorum, and it certifies (`certifies_of_synchronisedOn`); and since the
correct validators form a quorum, the certificates themselves do. The round-level
form `directCommit_of_synchronisedOn` is stated without reference to `Slots`,
since nothing in the argument depends on `L` being a leader block.

The hypotheses are three local population facts. Neither the horizon, nor growth,
nor any limiting construction appears.

**L5.**
```lean
theorem decided_none_of_leader_absent {V : View …}
    (h : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k) :
    Decided U V k none
```

If the leader of a slot published nothing, every view decides `none`. The premise
of `Decided.directSkip` quantifies over candidates and is therefore satisfied
vacuously; a formulation which selected a distinguished leader block would have
had nothing to select.

**L6.**
```lean
def FairScheduleOn (T : Finset Validator) : Prop := ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T

theorem commits_recur_on (hT : T ⊆ Correct) (hcard : 2 * F.f + 1 ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      ∀ U D N, Live U D N → DeliversQuorum D → SynchronisedOn U T R →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L)
```

The order of quantification carries the content. The alternative reading — that
given `Live U D N`, for every `k` there exists a committing `k' ≥ k` with
`slotRound k' + 2 ≤ N` — is false: fairness promises a correct leader somewhere
beyond `k`, and that slot may lie beyond the horizon, with nothing to license
requesting a nearer one. As stated, `k'` depends only upon the schedule, which is
a property of the `Slots` instance and not of any DAG; the universe is then
required to have grown far enough. This is also the correct reading of the claim
that the ledger grows without bound (§6.3).

The unboundedness of slot rounds required by the proof is supplied by
`le_slotRound : 3 * k ≤ S.slotRound k`.

### 6.7 Deriving coverage: the delivery route

```lean
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ Correct, ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ Correct → a ∈ D.held v n

theorem synchronised_of_delivery (D : Delivery U) (h : EventuallyDelivers D R) :
    Synchronised U R
```

The proof is the chain `refs ⊇ held ⊇` every correct block below.

The two premises are of different kinds, and separating them is the point. P7
(`includes`) is a clause of the protocol, which an implementation executes and an
observer can check; `EventuallyDelivers` is a pure network guarantee, and is the
only thing assumed here. Nothing becomes unconditional: absent a time model the
chain must terminate at a delivery assumption.

`EventuallyDelivers` is view convergence *indexed to the moment of building*: it
does not state that correct blocks eventually reach `v`, but that they are members
of `D.held v n`. That indexing performs the work, and it is exactly what a
view-shaped statement lacks (§7.1).

### 6.8 Deriving coverage: the timing route

```lean
structure Timing (U) (T : Finset Validator) (N : ℕ) where
  blk : Validator → ℕ → BlockId
  built : Validator → ℕ → ℕ
  timeout : ℕ → ℕ
  gst : ℕ
  delay : ℕ
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  blk_mem / blk_creator / blk_round : …
  waits   : ∀ v ∈ T, ∀ n < N, built v n + timeout n ≤ built v (n + 1)
  timeout_pos : ∀ n, 1 ≤ timeout n
  covers  : ∀ v ∈ T, ∀ w ∈ T, ∀ n < N, gst ≤ built w n →
    built w n + delay ≤ built v (n + 1) → blk w n ∈ (U.block (blk v (n + 1))).refs
  latest : ℕ → ℕ
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  latest_mem : ∀ n ≤ N, ∃ w ∈ T, latest n ≤ built w n
  prompt  : ∀ v ∈ T, ∀ n < N,
    built v (n + 1) ≤ max (built v n + timeout n) (latest n + delay)
```

The field `covers` is the partial-synchrony assumption, and it is the only
network field. `waits` and `prompt` are the two protocol build rules, bounding
build times from below and above respectively. `latest` is required to be
*attained* (`latest_mem`) and not merely an upper bound, since as a bare bound it
would carry no information. The horizon is required for the reason given in §6.3.

**Drift is derived rather than assumed.**
```lean
def Timing.DriftFrom (n₀ D : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, n₀ ≤ n → n ≤ N → tm.built w n ≤ tm.built v n + D

theorem Timing.driftFrom_of_prompt {n₀ : ℕ}
    (hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D)
    (hto : ∀ n, n₀ ≤ n → tm.delay ≤ tm.timeout n) :
    tm.DriftFrom n₀ D
```

The inductive step is a case distinction on the maximum in `prompt`. In the
timeout-limited case every validator advances by the same `timeout n` and the
spread is unchanged; in the delivery-limited case a validator completes by
`latest n + delay`, and since `latest` is attained the inductive bound applies to
the validator attaining it. The result establishes that drift is *preserved*, not
that it is compressed: every clock advances by the same timeout. Preservation is
what the subsequent argument requires. `Timing.le_built` records that rounds
advance real time, so that a round beyond GST was necessarily built beyond GST.

**Coverage, derived.**
```lean
theorem Timing.synchronisedOn_of_timing (hT : T ⊆ Correct)
    (hD : tm.DriftFrom R D) (hgst : tm.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + tm.delay ≤ tm.timeout n) :
    SynchronisedOn U T R
```

Four inequalities compose — drift, the timeout threshold, and the waiting rule —
to yield `built w n + delay ≤ built v (n+1)`, which is exactly the hypothesis of
`covers`. Non-equivocation completes the argument: `SynchronisedOn` quantifies
over every `T`-authored block, and T1 identifies each with the block the structure
names. This is why `T ⊆ Correct` is required here, a Byzantine author being
permitted several blocks in a round while `blk` names one.

The hypothesis `hbackoff` is a *threshold* condition rather than a growth
condition: the timeout must remain above `D + delay` from `R` onwards. A constant
timeout satisfies it, as does any schedule which stabilises above the bound.
`exists_backoff_ge` and `exists_synchronisedOn_of_backoff` package one sufficient
condition — a monotone, unbounded backoff — which is the appropriate one when Δ
is unknown; §6.10 supplies two further routes.

### 6.9 The layering

> *[Figure 3]* The layering, and the trust boundary.
>
> ```
>   L6   commits recur            ─┐
>   L4   a correct leader commits  │  no time appears in this region
>   L1   no stall                  │
>   L0   density                  ─┘
>         ▲
>         │   SynchronisedOn   — derived, not assumed
>         │
>   L7a   from   N2  EventuallyDelivers   +   P7  includes
>   L7b   from   N2  Timing.covers        +   P9  waits, prompt
>                └──── assumed ────┘          └──── specified ────┘
> ```

No theorem above `SynchronisedOn` mentions time, and no theorem below it mentions
certificates. The figure also locates the trust boundary: of the four premises
beneath the line, the two on the left are assumptions about an adversarial
network and the two on the right are clauses of the algorithm.

### 6.10 Quantitative results

The results of this section are collected in a separate module which nothing else
imports. Each strengthens a result above and is purchased with a strengthened
clause (§4.5); a reader declining those clauses retains §6.1–§6.9 intact.

**The weak hypotheses admit no bound.** Two of the results above conclude with
an existential statement that supplies no bound on its witness —
`∃ R, SynchronisedOn U T R`, and `∃ k', k ≤ k' ∧ …`. This is not slack in the
proofs. Each governing hypothesis has the same form, and under such hypotheses
no bound exists. The hypothesis
`∀ m, ∃ n, m ≤ tm.timeout n` admits `timeout n = ⌊log₂(n+1)⌋`, which is monotone
and unbounded yet requires `n ≥ 2^(D+delay) − 1` to clear the threshold, and
slower schedules displace `R` without limit; `FairScheduleOn T` admits a schedule
naming `T`-leaders at slots `0, 10, 1000, …`. A bound therefore requires a *rated*
hypothesis rather than a better proof.

**The round of coverage.**
```lean
def Rated (timeout : ℕ → ℕ) : Prop := ∀ n, n ≤ timeout n

theorem synchronisedOn_of_rate (tm : Timing U T N) (hT : T ⊆ Correct)
    (hrate : Rated tm.timeout) {n₀ : ℕ} (hn₀ : tm.delay ≤ n₀)
    (hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D) :
    SynchronisedOn U T (max (max (D + tm.delay) n₀) tm.gst)
```

Each term of the maximum is interpretable: the threshold the timeout must clear,
the round at which the drift bound is measured, and GST. A hypothesis is removed
as well as added — `backoff_ge_of_rate` requires no monotonicity, the bound at
`n` deriving from `n` itself and so being incapable of lapsing — and
`unbounded_of_rated` confirms that `Rated` strengthens the hypothesis it
replaces.

**The committing slot, and its round.**
```lean
def FairWithin (T : Finset Validator) (w : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ k' < k + w ∧ S.leader k' ∈ T

theorem commits_recur_within … (fair : FairWithin T w) (R k : ℕ) :
    ∃ k', max k R ≤ k' ∧ k' < max k R + w ∧ R ≤ S.slotRound k' ∧ …

theorem commits_recur_by_round … (hs : BoundedSpacing s) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ S.slotRound k' ≤ S.slotRound (max k R) + s * w ∧ …
      S.slotRound (max k R) + s * w + 2 ≤ N → …
```

`FairWithin.fairScheduleOn` records that the rated schedule is a fair one, so
that L6 applies unchanged.

`BoundedSpacing` has no counterpart among the weak hypotheses. `Slots.spacing`
bounds slot rounds from *below*, which is what safety requires, the anchor of M4
being obliged to lie three rounds above. A latency claim requires the opposite
bound, and the class provides none, no safety result having occasion to ask for
one. Supplying the mirror image is what converts a bound on the slot index into a
bound on its round.

**The wait bound.**
```lean
theorem directCommit_of_wait (tm : Timing U T N) (hT : T ⊆ Correct)
    (hcard : 2 * F.f + 1 ≤ T.card)
    (hstart : ∀ v ∈ T, ∀ w ∈ T, tm.built w 0 ≤ tm.built v 0 + D₀)
    (hwait : ∀ n, D₀ + tm.delay ≤ tm.timeout n)
    (hgst : tm.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

> Beyond GST, if every reliable validator waits at least `D₀ + Δ` before
> building, every correct leader is committed, where `D₀` bounds the spread at
> round `0`.

Thus `Delay(Δ) = D₀ + Δ`, specialising to `2Δ` under a common start
(`directCommit_of_wait_two_delay`), with `decided_of_wait` giving the
corresponding statement about `Decided`.

The timeout is here a *constant*: no backoff, no rate condition, no monotonicity
and no existential round appear. This locates the role of the backoff precisely.
A backoff is required only because Δ is unknown; a validator in possession of the
delivery bound requires no adaptation whatever.

The origin of `D₀` merits comment. Since drift is preserved rather than
compressed (§6.8), the bound is not derived from Δ. It is instead taken at round
`0`, where it is a statement about how nearly simultaneously the validators
started, and `driftFrom_of_prompt` carries it forward unchanged. Validators
starting together give `D₀ = 0` and `Delay(Δ) = Δ`; validators started by a
common broadcast give `D₀ ≤ Δ`, since the signal itself requires at most Δ to
arrive. The factor of two is thus the cost of not possessing synchronised clocks.

The value admits an external check. Starfish [PMV25], designing a pacemaker for
this family rather than deriving a threshold, fixes its block-creation timeout at
`δ_TO = 2Δ`; Mysticeti's own creation rule uses a timer of `2Δ` likewise. The
constant obtained here as a derived requirement is thus the one independently
arrived at as a design choice, and §6.8 supplies the reason the factor is two —
`D₀ + Δ` with `D₀ ≤ Δ` under a common broadcast start.

`Timing.populatedOn` is worth noting in the same connection: it supplies L4's
population hypotheses from the `Timing` structure directly, because `Timing.blk`
is total below the horizon. That totality is P8 in its strongest form — a block
at every round, with no exception — and is what makes these statements
independent of `Live` and L1.

`Timing.populatedOn` supplies the three population hypotheses of L4 from the
`Timing` structure itself, which already asserts a block per reliable validator
per round below the horizon. These statements consequently require neither
`Live`, nor `DeliversQuorum`, nor L1: their only temporal hypotheses are the
start spread, the wait, and the position of the slot relative to GST.

---

## 7. Discussion: eventual DAG synchrony

### 7.1 Locating the synchrony assumption

The synchrony assumption may be stated in terms of views:

> beyond GST, if a correct validator holds a view `V₁`, then within Δ the views
> of all correct validators contain `V₁`.

This is a statement about the network, and as such it is complete: it says
everything about delivery that the development requires. It is also attractive
formally, `View` being already a first-class structure with inclusion already
meaningful and every safety result already view-relative, and it yields L3
immediately, the common view being `View.full`.

What it does not do is determine what blocks *look like*. Reference coverage is
a property of blocks, and blocks are produced by validators according to the
protocol, so it depends on the specification as well as on the network. This is
not a deficiency in the assumption; it is a consequence of coverage being a
derived property rather than an assumed one (§4.4).

Three observations follow, and they are the content of the section.

**The protocol must specify a wait, and this is a design obligation rather than
a gap in the assumption.** Consider `f = 1` with validators `{A,B,C,D}`, all four
correct, and instantaneous delivery, so that the network assumption holds in its
strongest form. Suppose the specification directs a validator to build as soon as
it holds `2f+1 = 3` blocks of the round below, and suppose `A`, `B` and `C` are
marginally faster than `D`. Each of them then forms the quorum `{A,B,C}` and
builds before `D`'s block arrives, so no block of theirs ever references `D`'s.
Every block is valid, views converge perfectly, and `SynchronisedOn U Correct R`
fails for every `R`.

What this exhibits is a badly specified protocol under a well-behaved network.
The remedy lies in the specification: P9 directs a validator to wait a full
timeout rather than to build on the arrival of a quorum. The example is worth
including because the incorrect rule is the natural one — the quorum is exactly
what validity requires — and because it shows that promptness and coverage are
in tension, which is what P9's two halves jointly resolve.

**The threshold the specification must meet is `D₀ + Δ`, not Δ.** This is the
one point at which a network parameter enters the protocol's constant, and it is
the substantive quantitative result (§6.10). Validators enter a round at
different times, so a wait must accommodate the propagation bound *and* the
spread between validators; taking the spread at round `0`, where it records how
nearly simultaneously the validators started, and propagating it forward by
`driftFrom_of_prompt`, gives the bound. Under a common start, `D₀ ≤ Δ` and the
threshold is `2Δ`.

Because Δ is not known to an implementation, no constant can be fixed in
advance. A backoff is the specification's response — a search for a sufficient
constant, written into the algorithm — and its only relevant property is that
the search terminates (§7.2).

**The network guarantee must be indexed to the moment of building.** A block's
references are fixed at its construction, so what bears on the derivation is not
what a validator holds eventually but what it held when it built. `View.ids` is a
finite set of identifiers with no temporal index, so a view-convergence statement
cannot be applied directly. `Delivery.held : Validator → ℕ → Finset BlockId`
supplies the index — `held v n` denotes what `v` had in hand when building for
round `n+1` — and with it the delivery route (§6.7) is a single line. A
time-indexed family of views would serve equally well; the requirement is the
index, not the vehicle. This is an observation about formalisation, and it is the
reason `SynchronisedOn` is stated on `refs`.

### 7.2 Why coverage is derived rather than specified

Reference coverage could not have been made a clause of the protocol, which is
the deeper reason it appears as a derived property. `SynchronisedOn` refers to
`Correct`, a model-level object, so an instruction to reference every correct
block of the round below would name two quantities a validator cannot determine:
which of the blocks it holds are correct-authored, and whether all of them have
arrived, a missing block being indistinguishable from one never published.

What a validator can be directed to do is wait a fixed period, build upon
whatever has arrived, and increase the period when progress fails. These are
`waits`, `prompt` and the backoff — P9 together with R1 — all of them
executable.

The signal driving the backoff is the awkward point. Before GST no period is
sufficient, and nothing permits a validator to detect this directly; what it
observes is that commits have ceased. The feedback loop which delivers coverage
is therefore driven by liveness failure, the very condition being proved away.
This is a feedback loop rather than a circularity, but it means the argument
cannot rest on modelling the loop's dynamics.

The development accordingly does not model it. What `synchronisedOn_of_timing`
consumes is a threshold — the timeout remains above `D + delay` from some round
onwards — with no condition on shape, rate, or driving signal. §6.10 carries this
to its conclusion: with Δ known, a constant timeout of `D₀ + Δ` suffices and the
loop disappears.

### 7.3 Consequences of the abstraction

1. The consensus argument is purely combinatorial, involving round indices and
   finite-set cardinalities. Under a message-level assumption every statement
   would carry instants.
2. The temporal content is confined to a single module and consumed through a
   single definition.
3. The condition admits two independent derivations (§6.7, §6.8) and a third,
   quantitative route (§6.10), against an unchanged statement.
4. The condition composes with the safety development, mentioning only `U.ids`,
   `U.block` and `refs` — the vocabulary that development already employs.

### 7.4 Costs

Δ does not appear above the interface. Introducing it would require views indexed
by an instant and every statement quantified over instants, for no proof content.
The quantitative statements recover what is needed *below* the interface without
propagating time upward.

Coverage being derived rather than assumed does not make it unconditional. The
derivation rests on N2, and in the absence of a time model the chain must
terminate at a delivery assumption; what the reformulation achieves is to place
that assumption where it belongs — on the network — and to keep it out of every
statement above.

### 7.5 Related work

**Certified and uncertified DAGs.** In a certified DAG — DAG-Rider, Narwhal with
Tusk or Bullshark [DKSS22, SGSK22], Sailfish [SSKN25] — a block is disseminated
by reliable broadcast and enters the DAG carrying a quorum of signatures, so a
reader may assume any block it sees is non-equivocated and available. The
uncertified variant descends from Hashgraph [Bai16] and Blockmania [DH18],
receives its modern form in Cordial Miners [KNPS23], and reaches its lowest
latency in Mysticeti [Bab+25], which removes the wave structure of Cordial Miners
by assigning a leader slot in every round. The trade is the one described in
§1.1: certification disappears from the critical path, and equivocation and
availability become the reader's problem.

The uncertified structure has since been reused with one parameter varied at a
time: Mahi-Mahi [Jov+24] under asynchrony, committing several leader slots per
round; Odontoceti [Van25] at `n = 5f+1`, buying a two-round commit with a weaker
fault threshold; Starfish [PMV25] with erasure-coded dissemination; Bluestreak
[PVM26] with a sparse reference structure, which abandons the rule that every
block cites a quorum below and so falls outside the present model. Shoal++
[Aru+25] argues from the certified side that certification is not the cause of
latency, and hybridises by committing anchors on `2f+1` uncertified proposals.

**Where the synchrony assumption is located.** In each of the above the
assumption is stated per message, in the sense of Dwork, Lynch and Stockmeyer
[DLS88]: beyond GST a message between correct parties arrives within Δ. The
consequence noted in §1.2 is that every subsequent statement is quantified over
instants. The present formulation instead states the assumption on the DAG, and
§6.7 and §6.8 derive it from the conventional one. The author is not aware of a
prior structural formulation, though the property itself is asserted repeatedly:
Mysticeti's Lemma 8 and Cordial Miners' Proposition 38 both claim post-GST
synchronisation of honest validators, and it is exactly these claims that
[PMV25] reports as gapped and [QXS26] refutes.

**Mechanised consensus.** Safety-only verification of DAG protocols exists in
TLA+ with TLAPS [Ber+24], covering DAG-Rider, Cordial Miners, Hashgraph, an
Aleph variant and eventually synchronous Bullshark, with a modular separation of
DAG construction from ordering. LiDO-DAG [QXS25] provides mechanised safety and
liveness in Rocq for Narwhal, Bullshark and Sailfish — all certified. The work
closest to the present development is [QXS26], which extends that framework to
Mysticeti itself and is discussed at length in §4.1, §4.4 and §6.6. Two
differences of method are worth recording. Theirs is an operational model: a
transition system over traces, with segmented traces encoding the unreliability
of timers before GST, and liveness reduced to safety properties of an abstract
pacemaker by refinement. The account here is structural, and no theorem above
§6.8 mentions time. The benefit of the structural style is visible in §6.6: the
dependence of liveness on the round-jumping clause surfaces as a named hypothesis
of a single lemma rather than as a condition inside a transition relation. The
cost is that the theorems of [QXS26] cannot be stated here at all, "within
bounded time" not being expressible in this vocabulary (§9).

**References.**

- [Aru+25] B. Arun, Z. Li, F. Suri-Payer, S. Das, A. Spiegelman. *Shoal++: High Throughput DAG BFT Can Be Fast and Robust!* NSDI 2025. arXiv:2405.20488.
- [Bab+25] K. Babel, A. Chursin, G. Danezis, A. Kichidis, L. Kokoris-Kogias, A. Koshy, A. Sonnino, M. Tian. *Mysticeti: Reaching the Limits of Latency with Uncertified DAGs.* NDSS 2025. arXiv:2310.14821.
- [Bai16] L. Baird. *The Swirlds Hashgraph Consensus Algorithm.* Swirlds Tech Report SWIRLDS-TR-2016-01, 2016.
- [Ber+24] N. Bertrand, P. Ghorpade, S. Rubin, B. Scholz, P. Subotic. *Reusable Formal Verification of DAG-based Consensus Protocols.* arXiv:2407.02167.
- [DH18] G. Danezis, D. Hrycyszyn. *Blockmania: from Block DAGs to Consensus.* arXiv:1809.01620.
- [DKSS22] G. Danezis, L. Kokoris-Kogias, A. Sonnino, A. Spiegelman. *Narwhal and Tusk: a DAG-based Mempool and Efficient BFT Consensus.* EuroSys 2022.
- [DLS88] C. Dwork, N. Lynch, L. Stockmeyer. *Consensus in the Presence of Partial Synchrony.* JACM 35(2), 1988.
- [Jov+24] P. Jovanovic, L. Kokoris-Kogias, B. Kumara, A. Sonnino, P. Tennage, I. Zablotchi. *Mahi-Mahi: Low-Latency Asynchronous BFT DAG-Based Consensus.* arXiv:2410.08670.
- [KNPS23] I. Keidar, O. Naor, O. Poupko, E. Shapiro. *Cordial Miners: Fast and Efficient Consensus for Every Eventuality.* DISC 2023, LIPIcs 281.
- [PMV25] N. Polyanskii, S. Mueller, I. Vorobyev. *Making Uncertified DAG BFT Provably Live with Linear Payload and Quadratic Metadata Communication* (Starfish). IACR ePrint 2025/567.
- [PVM26] N. Polyanskii, I. Vorobyev, S. Mueller. *Bluestreak: Scaling DAG BFT by Sparsifying Metadata.* IACR ePrint 2026/898.
- [QXS25] L. Qiu, J. Xiao, J.-Y. Shin, Z. Shao. *LiDO-DAG: A Framework for Verifying Safety and Liveness of DAG-Based Consensus Protocols.* PACMPL 9(PLDI), Article 203, 2025. doi:10.1145/3729306.
- [QXS26] L. Qiu, J. Xiao, Z. Shao. *Mechanized Safety and Liveness Proofs for the Mysticeti Consensus Protocol under the LiDO-DAG Framework.* IEEE S&P 2026, 149–168.
- [SGSK22] A. Spiegelman, N. Giridharan, A. Sonnino, L. Kokoris-Kogias. *Bullshark: DAG BFT Protocols Made Practical.* CCS 2022.
- [SSKN25] N. Shrestha, R. Shrothrium, A. Kate, K. Nayak. *Sailfish: Towards Improving the Latency of DAG-based BFT.* IEEE S&P 2025. ePrint 2024/472.
- [Van25] P. Vander Vos. *Odontoceti: Ultra-Fast DAG Consensus with Two Round Commitment.* MSc thesis, arXiv:2510.01216.

---

## 8. Satisfiability

Every structure carrying conditions is exhibited satisfiable by a concrete model
over four validators at `f = 1`. This is a substantive component of the
development rather than a testing exercise: an unsatisfiable hypothesis renders
every theorem above it vacuous, and vacuity is not otherwise detectable.

| Model | Satisfies |
|---|---|
| `Ugrow N` | `Live`, `DeliversQuorum`, `Synchronised`, at every horizon `N` |
| `ugrowDelivery` | `Delivery`, and `EventuallyDelivers` for the delivery route |
| `ugrowHonest` | `Delivery` with a genuinely partial view: the Byzantine validator withholds, and a quorum nonetheless survives |
| `ugrowTiming` | `Timing` in lockstep, with a rated `2^n` backoff |
| `ugrowSkew` | `Timing` with nonzero drift and delay, exercising both cases of `driftFrom_of_prompt` |
| `rrSlots` | `Slots`, round-robin, satisfying `FairWithin T (f+1)` and `BoundedSpacing 3` |
| `Model.lean` | six `BlockUniverse` instances exercising the safety definitions |

Three of the models are tight, which is what renders the constants meaningful.

- `ugrow_not_populated_succ` establishes `¬ Populated (Ugrow N) (N+1)`: the family
  reaches round `N` and stops, so the horizon is exact.
- `ugrowSkew` lies on the boundary of the wait bound. Its round-`0` spread is `2`,
  its `delay` is `2` and its `timeout` is `4`, so that `D₀ = delay` and
  `2·delay = timeout`: every inequality of `directCommit_of_wait_two_delay` holds
  with equality (`ugrowSkew_directCommit_of_wait`). The constant is therefore
  exact rather than a conservative estimate.
- `rrSlots_fairWithin` gives the window `f + 1 = 2`, and `f + 1` is forced, the
  validators outside the reliable set being permitted to occupy consecutive
  positions in the rotation.

One negative observation is worth recording. A model exhibiting *round spread* —
correct validators separated by many rounds — while still committing is impossible
at `f = 1`, since `|Correct| = 3 = 2f+1` exactly, so that every correct validator
is required for a quorum and none may lag. Such a model requires `f ≥ 2`. This is
the combined fault budget of §4.2 appearing as a concrete obstruction rather than
as an inequality.

---

## 9. Limitations

The quantitative bounds are established (§6.10). The following remain open.

**The backoff loop.** `Rated` and the threshold of R4 are stipulated as clauses
of the specification; no realistic adaptive scheme is shown to satisfy them, and
the feedback mechanism of §7.2 is not modelled. Moreover
`Timing.timeout : ℕ → ℕ` is indexed by round and common to the reliable set, so
that a per-validator backoff — in which validators increase their timeouts at
different moments — cannot be expressed, let alone shown to converge. This
requires a refinement of `Timing`.

**Wall-clock latency.** `Delay(Δ)` is a duration, but the total elapsed time to a
commit is not derived: converting a bound of the form "`3k + 8` rounds, each of
at least `2Δ`" into elapsed time requires a lemma accumulating `prompt` across
rounds, which is not present. `Timing.le_built` relates rounds to time in one
direction only.

**Byzantine leaders.** §6.10 bounds the wait until the next reliable leader,
which sidesteps rather than answers the question of how distant an indirect
anchor may be when the leader is Byzantine.

**Leader predictability.** `Slots.leader` is an arbitrary function, so nothing
distinguishes a schedule an adversary can predict from one it cannot, and
targeted denial of service against a known future leader is invisible to the
model. `FairWithin` constrains when reliable leaders occur, not whether they can
be anticipated.

**Block-level total order.** The blocks released by a single commit are not
ordered among themselves, for the reason given in §5.6.

**No liveness below P8.** Every liveness result here is conditional on P8, and
nothing is offered for executions violating it. [QXS26] proves a *weak liveness*
result which is not: without any restriction on round-jumping, every leader block
created by an honest validator after GST acquires at least `f+1` certificates
from honest validators, so it can never be indirectly skipped, only left
undecided. The corresponding statement is not available here, and the obstruction
is identifiable. Density (L0) yields `2f+1` distinct authors at round `r+1`
whenever the DAG reaches above it, hence `f+1` *correct* authors, and coverage
makes each of their blocks reference the leader — so `f+1` correct **supporters**
is within reach from L0 and `SynchronisedOn` alone, with neither `Populated` nor
P8. A certificate, however, requires `2f+1` distinct supporters, and
`SynchronisedOn` is honest-to-honest (§6.6), so the remaining `f` cannot be
obtained; reaching `2f+1` supporters requires `2f+1` correct authors at `r+1`,
which is `Populated` again. [QXS26] bridges the gap with a *predecessor rule* —
a validator creating a block must make it a supporter and a certificate where it
can — for which this model has no counterpart, P7 constraining what a validator
cites given what it holds but not obliging a quorum of supporters to exist. The
supporter-level statement is therefore the available result, and it is not their
theorem.

**Certified DAGs.** The certified variant, in which a certificate round is
explicit, is outside the scope of the present development.

None of these affects whether the stated theorems are true; each concerns how
much they say.

---

## 10. Mechanisation

The development comprises approximately 4,700 lines of Lean 4 (v4.32.2) against
Mathlib, of which some 3,200 constitute the library and 1,500 the models of
§8. A full build reports no errors and no warnings.

**Axiom audit.** Every principal result — `reaches_of_quorum_support`,
`exists_common_correct_ancestor`, `decided_agree`, `commitSeq_agree`,
`outputAt_agree`, `no_stall`, `commits_recur_on`,
`exists_synchronisedOn_of_backoff`, `ugrow_commits_by_round`,
`ugrowSkew_directCommit_of_wait` — depends on exactly `propext`,
`Classical.choice` and `Quot.sound`, which constitute the whole axiom set of Lean
4. No result depends on `sorryAx`, on any bespoke axiom, or on `native_decide`
and the extended trusted base it entails.

| Module | Contents |
|---|---|
| `Validators.lean` | the fault model; T0 |
| `Block.lean` | `Block`, `ValidWrt`; T0′ |
| `BlockDag.lean` | `BlockUniverse`, `View`; T1 |
| `CausalHistory.lean` | `Reaches`; T2, T6a |
| `Support.lean` | counting vocabulary; the hitting, propagation and coverage lemmas |
| `Persistence.lean` | T3 |
| `CommonCore.lean` | T3a, T3c |
| `Mysticeti.lean` | the commit rule; M1–M6; the ledger |
| `Liveness.lean` | L0–L6, L7a |
| `Timing.lean` | L7b |
| `Quantitative.lean` | L8, L9; imported by nothing |
| `LeanDagTest/` | the models of §8 |

Two design records accompany the development: `spec.md` for safety and
`liveness.md` for liveness. These carry the design rationale and the log of
settled and open questions. The report draws its statements from the source.

---

## Appendix A. Statement index

Principal results only; supporting lemmas are omitted.

### Safety

| Label | Statement | Lean | Module |
|---|---|---|---|
| T0 | two quorums share a correct validator | `exists_correct_mem_inter` | `Validators` |
| T0′ | two quorum-backed identifier sets share a correct author | `exists_correct_mem_creators_inter` | `Block` |
| T1 | non-equivocation, in usable form | `BlockUniverse.eq_of_creator_eq` | `BlockDag` |
| — | two quorum-backed sets of round-`n` blocks share a block | `BlockUniverse.exists_common_mem_of_quorums` | `BlockDag` |
| T2 | causal history is non-increasing in round | `round_le_of_reaches` | `CausalHistory` |
| T6a | causal history does not escape a view | `View.mem_of_reaches`, `View.exists_reaches_iff` | `CausalHistory` |
| T3 | persistence | `reaches_of_quorum_support` | `Persistence` |
| T3a | correct-support counting | `exists_correct_common_support` | `CommonCore` |
| T3c | a common correct ancestor | `exists_common_correct_ancestor` | `CommonCore` |
| M1 | no block is both committed and skipped | `not_directCommit_of_directSkip` | `Mysticeti` |
| M2 | a committed block's certificate is unavoidable from `r+3` | `exists_certificate_reaches_of_directCommit` | `Mysticeti` |
| M3 | a skipped block has no certificate anywhere | `certificates_eq_empty_of_directSkip` | `Mysticeti` |
| M4 | the indirect rule agrees with the direct | `indirect_agrees_with_direct`, `certifiedIn_iff_of_view` | `Mysticeti` |
| M5′ | certificate uniqueness | `eq_of_certificates_nonempty` | `Mysticeti` |
| M5 | at most one block per slot is directly committed | `eq_of_directCommit_of_creator_eq` | `Mysticeti` |
| M6 | agreement | `decided_unique`, `decided_agree` | `Mysticeti` |
| — | corollaries of agreement | `eq_of_decided_commit`, `not_decided_skip_of_decided_commit` | `Mysticeti` |
| — | the committed-leader sequence is agreed | `commitSeq_agree` | `Mysticeti` |
| — | the ledger is monotone and agreed | `ledgerSet_mono`, `ledgerSet_agree` | `Mysticeti` |
| — | a block enters at one slot, agreed | `outputAt_unique`, `outputAt_agree` | `Mysticeti` |

### Liveness

| Label | Statement | Lean | Module |
|---|---|---|---|
| L0 | the DAG is dense below its frontier | `card_authorsAt_of_lt` | `Liveness` |
| L1 | no stall | `no_stall` | `Liveness` |
| L2 | decisions are monotone in the view | `decided_mono` | `Liveness` |
| L3 | decisions propagate to the full view | `decided_full` | `Liveness` |
| L4 | a correct leader is committed | `directCommit_of_leader_mem`, `decided_of_leader_mem` | `Liveness` |
| — | at `T := Correct` | `directCommit_of_correct_leader`, `decided_of_correct_leader` | `Liveness` |
| L5 | an absent leader is skipped | `decided_none_of_leader_absent` | `Liveness` |
| L6 | commits recur | `commits_recur_on`, `commits_recur` | `Liveness` |
| L7a | coverage from delivery | `synchronised_of_delivery` | `Liveness` |
| L7b | coverage from GST | `Timing.synchronisedOn_of_timing`, `exists_synchronisedOn_of_backoff` | `Timing` |
| — | drift is derived | `Timing.driftFrom_of_prompt` | `Timing` |
| L8a | the round of coverage, explicitly | `synchronisedOn_of_rate` | `Quantitative` |
| L8b | the committing slot, and its round | `commits_recur_within`, `commits_recur_by_round` | `Quantitative` |
| L9 | the wait bound | `directCommit_of_wait`, `decided_of_wait`, `directCommit_of_wait_two_delay` | `Quantitative` |
