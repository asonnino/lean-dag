---
title: "Eventual DAG Synchrony: a machine-checked account of safety and liveness for uncertified DAG consensus"
---

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

## Abstract

DAG-based Byzantine fault-tolerant protocols are widely deployed, yet their
liveness arguments are conventionally stated in terms of per-message delivery
bounds, which obliges the entire proof to carry a time model that the commit
rule itself never mentions. We propose **eventual DAG synchrony** — a
structural condition on the DAG: beyond some round, every correct block
references every correct block of the round below — and give a machine-checked
development, in Lean 4, of safety and liveness for a Mysticeti-style commit
rule above this condition, in which no liveness theorem mentions time. Safety
assumes nothing about the network at all. The structural condition is derived
rather than assumed: it follows from standard partial synchrony together with
the protocol's own build rules, and its quantitative form states that a
correct leader is committed once correct validators wait `2Δ`.

We further prove what the committed ledger *contains*: every commit
carries, at every round below it, blocks from at least half of the
correct validators — with no synchrony assumption — and once the DAG is
synchronous every correct block enters the agreed ledger within a
schedule-window of its creation, while a six-validator counterexample
shows the same correct validator can be censored for ever without
synchrony, so the upgrade from aggregate to individual inclusion
genuinely costs the synchrony assumption.

On the same foundation, unchanged, we develop three further machine-checked
accounts. First, **denial-of-service resistance**: safety is shown
independent of any anti-equivocation condition, and a correct validator's
storage is bounded under an enforceable, author-blind *novelty budget* — with
a matching construction showing that any bound from reference-validity
conditions alone carries a constant exponential in the fault bound `f`.
Second, **garbage collection**: a per-validator horizon below which nothing
is retained, with commit verdicts invariant across the cut, storage constant
at a lag, and bootstrap by an `(f+1)`-sampled attested base — no consensus on
the cut anywhere. Third, the two-round protocol **Odontoceti**: safety and
liveness of its commit rule, generalized from the published `n = 5f+1` to
`n ≥ 5f+1`, where the formalization surfaces a gap in the published agreement
argument — two equivocating candidates can both pass the indirect commit test
at one anchor, realized on a concrete six-validator counterexample — and
repairs it with a canonical-candidate rule.

The development comprises roughly 15,000 lines of Lean 4 over Mathlib. Every
principal result depends on exactly Lean's three standard axioms; every
definition is exercised on concrete models by `decide` before anything is
proved from it. All displayed Lean in this report is drawn from the source
and type-checks against the built library.

---

## 1. Introduction

Byzantine fault-tolerant consensus built over block DAGs has moved from
research prototypes to production blockchains: validators exchange
round-indexed blocks, each referencing a quorum of the previous round, and
read commitment out of the resulting graph. The latest generation of these
protocols — Mysticeti and its descendants — is *uncertified*: no certificate
is ever constructed or sent, and every consensus-relevant fact is a counting
pattern in the graph itself. This makes the protocols unusually well suited
to mechanised verification — the commit rule is finite-set arithmetic — and
unusually exposed to subtle error, because equivocation and availability,
which certification used to discharge, become the reader's problem in every
proof. This report is a machine-checked account, in Lean 4 over Mathlib, of
this protocol family: a core development of safety and liveness organised
around a structural liveness condition we call *eventual DAG synchrony*,
a chain-quality account of what the committed ledger contains, and, on
that unchanged foundation, three further developments — storage bounds
under adversarial equivocation, garbage collection without consensus on
the cut, and the safety and liveness of the two-round protocol
Odontoceti, including a repair its published argument turns out to
need.

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
   stated as a condition on the DAG, and the dependence on time is confined to
   two files below a `Prop`-valued interface (§6.8–§6.9, §14).

4. **Three derivations** of the structural property — from an abstract
   delivery model (§6.7), from GST (§6.8), and from **view convergence**
   (§6.9) — in each case together with the protocol's build rules, and
   nothing beyond standard partial synchrony. They form a hierarchy
   rather than a menu: the third derives the second, and states the
   network's contribution in a form containing no clause about what
   validators do. On the same foundation, production is derived too
   (`populated_of_viewsConverge`), so the entire liveness account can be
   grounded on one view-shaped assumption.

5. A precise account of the **trust boundary** (§4). What is assumed reduces to
   the fault bound and two network conditions; every other condition is a clause
   of the protocol, which a designer controls. In particular reference coverage
   is derived rather than assumed, and the one point at which a network parameter
   constrains the specification is the wait threshold of §13.1.

6. **Quantitative forms** (§6.11): the round from which coverage holds, given
   explicitly; a bound on the slot at which the next commit occurs; and an
   operational statement — a correct leader is committed once every correct
   validator waits `D₀ + Δ`, which is `2Δ` under a common start.

7. **Chain quality** (§7): every commit's flush carries, at every round
   below it, blocks from at least half of the correct validators —
   proved with no synchrony assumption of any kind — and, once the DAG
   is synchronous, every correct block enters the agreed ledger within
   a schedule-window of its creation (`chain_quality`); a
   counterexample shows the aggregate guarantee provably does not
   imply the individual one without synchrony.

8. **Denial-of-service resistance** (§8): with safety shown independent of
   any anti-equivocation condition, storage is bounded twice over — a general
   per-cone bound under an exposure condition on references, with a matching
   construction showing its exponential constant is essentially forced, and a
   **novelty budget** under which a correct validator's store grows linearly
   forever, stated under enforceable, author-blind conditions only
   (`dos_resistance`).

9. **Garbage collection without consensus** (§9): a horizon below which
   stores retain nothing, with commit verdicts proved invariant across the cut
   under a single premise, storage made *constant* at a lag, bootstrap by an
   `f+1`-sampled attested base rather than any agreement on the cut, and the
   lag envelope pinned theorem by theorem.

10. **Odontoceti, formalized and repaired** (§10): safety and liveness of the
   two-round commit rule, generalized from the paper's fixed `n = 5f+1` to
   `n ≥ 5f+1`, on the unmodified DAG layer — together with four findings about
   the paper's safety argument, one of which (agreement among indirect commits
   resting on candidate-iteration order) is refutable on data without a
   canonicity repair the formalisation supplies.

### 1.4 Scope and non-goals

The development is deliberately bounded in four respects — a fifth, the
restriction to unpipelined schedules, has since been lifted and is recorded
first.

- **Pipelining and multiple leaders enter through the schedule, not the
  rule.** The schedule class constrains only monotonicity, unboundedness and
  keying (§3.4); anchoring is governed by per-pair eligibility. Mysticeti's
  every-round pipelining and its multi-leader rounds are instances, with the
  interleaving of simultaneously undecided slots handled by the committed-run
  results (`decided_of_committed_above`, `decided_below_of_committed_run`,
  `all_decided_below_of_fairRun`); `pipelining-and-multi-leader.md` is the
  design record. An earlier version of this development fixed a
  Cordial-Miners-like three-round spacing; that spacing survives only as a
  conservativity theorem (`eligible_of_lt_of_spacing`).
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
- **No wall-clock latency.** The wait bound of §6.11 is a duration, but the total
  elapsed time to a commit is not derived (§13.6).

### 1.5 Organisation

§2 gives the system model and §3 the commit rule; §4 draws the trust
boundary, separating what is assumed from what the protocol enforces. §5
develops safety (culminating in agreement, `decided_agree`, and the agreed
ledger) and §6 liveness (culminating in recurring commits,
`commits_recur_on`, the three derivations of eventual DAG synchrony, and the
quantitative wait bound). §7 proves the chain-quality account — coverage
without synchrony, inclusion with it (`chain_quality`,
`committed_of_correct_block`). §§8–10 present the three further
developments —
denial-of-service resistance (`dos_resistance`), garbage collection
(`decided_agree_chop`, `card_retained_le`, `bootstrap_agree`), and
Odontoceti (`Odontoceti.decided_unique`,
`Odontoceti.all_decided_below_of_fairRun`). §11 exhibits the witness models,
§12 describes the mechanisation, §13 discusses the formulation, the lessons
of the extensions, and the limitations, §14 surveys related work, and §15
concludes. Appendix A indexes every
principal statement against its Lean name and module. Throughout, displayed
Lean is drawn from the source; binders are occasionally elided for layout,
and `…` marks an elision.


---

## 2. System model

### 2.1 Validators and the fault model

```lean
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  f : ℕ
  byzantine : Finset Validator
  card_validators : 3 * f + 1 ≤ Fintype.card Validator
  card_byzantine : byzantine.card ≤ f

def Correct : Finset Validator := (F.byzantine)ᶜ
```

A quorum is `n − f` for `n ≥ 3f+1` validators — the familiar `2f+1` at the
boundary `n = 3f+1`, where every witness sits. The derived fact
`card_correct : n − f ≤ Correct.card`
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
  quorum : 0 < b.round → (Fintype.card Validator - F.f) ≤ (creators blk b).card
  self_parent : 0 < b.round → ∃ i ∈ b.refs, (blk i).creator = b.creator
```

Four points of formulation are load-bearing.

The predecessor condition is stated additively rather than as
`(blk i).round = b.round - 1`. Besides avoiding truncated subtraction on `ℕ`,
this makes the genesis case derivable rather than a separate branch: at round 0
the equation `(blk i).round + 1 = 0` is unsatisfiable, so `refs = ∅` follows
(`ValidWrt.refs_empty_of_round_zero`).

The quorum condition is stated on the *creator set*, not on `refs.card`. This is
the faithful reading of "references a quorum of blocks of the previous
round", which means `n−f` distinct *validators*; `ValidWrt.card_creators` and `ValidWrt.card_refs` relate the two
under the distinctness condition.

`distinct_creators` is consumed by certificate uniqueness (§5.4) and, in the
two-round setting, by twin uniqueness (§10).

`self_parent` — a non-genesis block references *some* block by its own
creator, not a unique one: an equivocator's blocks form a forest of
predecessor chains, and the condition does not collapse it. Mysticeti and
Odontoceti both mandate the clause. The safety and liveness developments never
consume it; it is load-bearing for the DoS arc (§8), where the self-parent
chain is what turns per-acceptance budgets into per-round rates and a correct
block's cone into a complete record of its author's acceptances.

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

### 2.5 Notation, and the labelling scheme

Global symbols, fixed for the whole report:

| Symbol | Meaning |
|:---|:---|
| `n`, `f` | committee size and fault bound; `n ≥ 3f+1` throughout, `n ≥ 5f+1` in §10 |
| `n − f` | the quorum size; `2f+1` at the boundary `n = 3f+1` |
| `Correct` | the complement of the Byzantine set (§2.1) |
| `r`, `k` | a round; a slot index (§3.4) |
| `U`, `V`, `D` | the block universe, a view, a delivery layer (§2.3, §6.2) |
| `H(b)`, `history U b` | the causal history (cone) of block `b` (§2.4) |
| `Δ`, GST | the post-stabilisation delivery bound and stabilisation time of partial synchrony (§6.8) |
| `R` | the round from which eventual DAG synchrony holds (§6.4) |
| `D₀` | the round-0 spread between correct validators' start times (§6.11) |
| `N` | the growth horizon of `Live` (§6.3) |
| `κ`, `T` | the novelty budget: analysis-side (guarded) and mechanism-side (author-blind) constants (§8.4) |
| `G`, `Λ` | a garbage-collection horizon round, and its lag behind the current round (§9) |

Results carry alphanumeric labels by area: **T** (structural theorems, §2 and
§5.1–§5.2), **M** (the commit rule, §5.3–§5.6), **L** (liveness, §6), **P**
and **N** and **R** (protocol, network and rate clauses of the trust
boundary, §4), **CQ** (chain quality, §7),
**D**/**C**/**B** (the denial-of-service development, §8),
**G** (garbage collection, §9), and **O** (Odontoceti, §10). The labels match
the design records and the source comments; Appendix A maps each to its Lean
name and module.

Counting vocabulary:

| Notation | Meaning |
|:---|:---|
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
  (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (votesIn U C L)).card

def certificates (U) (L : BlockId) (r : ℕ) : Finset BlockId :=
  (blocksAt U (r + 2)).filter (fun C => Certifies U C L)
```

A round-`(r+2)` block certifies a round-`r` block `L` exactly when its own
references contain blocks by a quorum of distinct validators, each of which
references `L`.


### 3.2 The direct rules

```lean
def DirectCommit (U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (certificates U L r)).card

def DirectSkip (U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (blames U L (r + 1)).card
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
  mono : Monotone slotRound
  unbounded : ∀ n, ∃ k, n ≤ slotRound k
  keyed : Function.Injective (fun k => (slotRound k, leader k))

def decisionRound (k : ℕ) : ℕ := S.slotRound k + 2
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j

def IsLeaderBlock (U) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k
```

The class constrains the schedule only to be monotone, unbounded in round, and
*keyed* — distinct slots differ in round or in leader. What safety actually
requires of anchoring is per-pair **eligibility**: an anchor's proposal must
clear the slot's decision round, which is Algorithm 3's filter
`r_decision < s.round`. Under the older formalisation's three-round spacing,
every later slot is eligible (`eligible_of_lt_of_spacing`), so the general
relation is conservative over it; and pipelined and multi-leader schedules —
Mysticeti as published — are instances (`Slots.uniform p m`,
`Slots.uniformSingle`), at the price that a backlog of undecided slots is
cleared by a *run* of consecutive commits rather than any single one
(`decided_below_of_committed_run`, `all_decided_below_of_fairRun`; the design
record is `pipelining-and-multi-leader.md`).

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
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      Decided U V k (some L)
  | indirectSkip {k j A} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      Decided U V k none
```

Here `some L` records a commitment and `none` a skip.

The relation is not a function. A decision procedure would recurse upward in
slot index with no *a priori* bound, requiring fuel or partiality for no benefit,
since nothing in the development needs to compute.

The two indirect cases anchor on the nearest **eligible** committed slot above
`k` — not simply the nearest one. Under pipelining the slots immediately above
`k` sit one and two rounds up, where no certificate for `k` is reachable, and
anchoring there would turn one validator's direct commit into another's
indirect skip; the anchor must clear `k`'s decision round (§3.4), which is
Algorithm 3's own filter. For the same reason the intermediate premise
quantifies over the eligible slots between `k` and the anchor only: the
ineligible ones are routinely committed under pipelining, and requiring them
skipped would leave `k` undecidable forever.

The direct reading of "nearest" — that no eligible slot strictly between is
committed — is a negative premise, which an inductive definition cannot carry.
It is stated positively, as the requirement that every eligible slot strictly
between be decided `none`. The two are equivalent, since the sweep decides
every slot it passes, and the positive form keeps every recursive occurrence
strictly positive; guarding the occurrence behind `Eligible` preserves that,
`Eligible` being a predicate on two naturals which does not mention `Decided`.
This formulation is consumed directly in the principal case of the agreement
proof (§5.5).

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
instances carries it. None is an axiom in the sense of §12, and their joint
satisfiability is a proof obligation discharged by exhibition (§11) rather than
something the logic must be trusted for. The distinction drawn here is
epistemic, not logical, and it is what determines where the trust boundary of
the system actually falls.

### 4.1 The protocol

| | Clause | Formalisation |
|:---|:---|:---|
| P1 | references lie one round below | `ValidWrt.predecessor` |
| P2 | no block cites one author twice | `ValidWrt.distinct_creators` |
| P3 | non-genesis blocks cite `n−f` distinct authors | `ValidWrt.quorum` |
| P3′ | non-genesis blocks cite a block by their own creator | `ValidWrt.self_parent` |
| P4 | a block is held only with its causal history | `BlockUniverse.complete` |
| P5 | one block per round: correct validators do not equivocate | `BlockUniverse.no_equivocation` |
| P6 | the slot schedule is monotone, unbounded and keyed | `Slots.mono`, `Slots.unbounded`, `Slots.keyed` |
| P7 | a validator references everything it accepted | `Delivery.includes` |
| P8 | a validator has a genesis block, and builds on holding a quorum | `Live.genesis`, `Live.builds` |
| P9 | a validator waits a full timeout, and does not dawdle | `Timing.waits`, `Timing.prompt` |
| P10 | the leader schedule names reliable validators arbitrarily far out | `FairScheduleOn` |

P1–P6 are consumed by the safety development, P7–P10 additionally by liveness;
P3′ by neither — it is load-bearing for the DoS arc (§8).

P10 is a joint condition rather than a pure specification: the schedule is the
designer's, but which validators are reliable is not. Round-robin discharges it
whenever the reliable set is of quorum size, since at most `f` of every `n`
consecutive leaders then lie outside it; `rrSlots` witnesses this with a window
of `f + 1` (§11).

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
Mysticeti's validity check requires a block to cite `n−f` *distinct* authors at
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
depends on the network. §6.11 determines the threshold it must meet, and §13.1
discusses the consequences.

### 4.2 The fault model

| | Assumption | Formalisation |
|:---|:---|:---|
| A1 | there are `n ≥ 3f+1` validators | `Faults.card_validators` |
| A2 | at most `f` are Byzantine | `Faults.card_byzantine` |

Byzantine validators are unconstrained: they may publish nothing, publish
selectively, or equivocate freely.

**The combined budget.** The principal liveness argument counts to `n−f` and no
higher, so what it requires is a quorum of validators that are both correct and
timely, rather than the participation of every correct one. Formulating this as
`T ⊆ Correct` with `n−f ≤ T.card` — a hypothesis of L4 and L6 — yields the
operative budget:

> `actual_byzantine + persistently_slow_correct ≤ f`

A correct validator which is persistently slow consumes budget exactly as a
Byzantine one does. This is a hybrid condition: correctness is a fault-model
matter, timeliness a network one. At `f = 1` there are four validators and
`|Correct| = 3 = n−f` exactly, so no slack exists and every correct validator
must be timely; slack appears only when fewer than `f` validators are in fact
faulty, and the `T`-parameterised statements make it available automatically.
The specialisations at `T := Correct` (`directCommit_of_correct_leader`,
`decided_of_correct_leader`, `commits_recur`) recover the conventional
statements.

### 4.3 The network

Two assumptions, and they are the whole of what the development asks of the
environment.

| | Assumption | Formalisation |
|:---|:---|:---|
| N1 | a quorum that exists is eventually held | `DeliversQuorum` |
| N2 | beyond GST, a block is delivered within Δ | `EventuallyDelivers`, `Timing.covers` |

**The vehicle.** Both are stated over the delivery layer (§6.2), whose
central field is

```lean
held : Validator → ℕ → Finset BlockId
```

with `held v n` denoting what `v` had **in hand at the moment it built its
round-`(n+1)` block** — not what `v` eventually receives. The index is the
essential modelling device, and §13.1 argues it is unavoidable: a block's
references are frozen at construction, so the quantity that bears on the
DAG's shape is what was held at build time. A view (`View.ids`) is a finite
set of identifiers with no temporal index and cannot supply it; a
time-indexed family of views would serve equally well.

#### N1 — eventual delivery, without timing

```lean
def DeliversQuorum (D : Delivery U) : Prop :=
  ∀ n, (Fintype.card Validator - F.f) ≤ (authorsAt U n).card →
    ∀ v ∈ (Correct : Finset Validator),
      (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (D.accepted v n)).card
```

*If* a quorum of validators have produced round-`n` blocks — `authorsAt U n`
being the creators of the round-`n` blocks of `U` — *then* every correct
validator accepts round-`n` blocks from a quorum of distinct authors. Four
features of the shape are deliberate.

- **It is conditional: existence first, holding second.** Stated
  unconditionally it would assert that round-`n` blocks exist, which is
  exactly what the liveness argument sets out to prove (§6.3); the
  assumption would then swallow its own conclusion. As stated it says only
  that *what exists is eventually obtained*.
- **It mentions no clock and no round bound.** There is no Δ, no GST, and
  no index past which it begins to hold — so N1 constrains the network
  before stabilisation exactly as after. This is what carries every result
  that does not need synchrony: L1 (`no_stall`, §6.3) turns N1 together
  with the protocol's build clause P8 into `Populated` at every round up to
  the growth horizon, with no temporal input whatever.
- **It is stated on `accepted`, not on `held`.** The quorum must survive
  the acceptance filter — the layer at which a validator takes at most one
  block per author, and at which the novelty budget of §8 imposes a rate
  limit. Since correct blocks are always accepted (`accepts_correct`), the
  two readings differ only on Byzantine duplicates, and stating it on
  `accepted` is what keeps the storage results of §8 compatible with
  liveness.
- **It counts authors, not blocks** (`creatorsOf`), so an equivocator
  flooding a validator with same-round twins contributes one to the
  quorum. Every quorum hypothesis in the development is stated this way
  (§2.5).

#### N2 — partial synchrony, in two guises

N2 appears in two forms because the structural condition of §6.4 is derived
from it twice, once without a clock and once with one (§4.4). The abstract
form, consumed by the delivery route of §6.7:

```lean
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ (Correct : Finset Validator), ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ (Correct : Finset Validator) →
    a ∈ D.held v n
```

From round `R` on, **every** correct block of round `n` is in **every**
correct validator's hands at index `n` — that is, in time to be built upon.
Coverage then follows in one step, `held ⊆ accepted ⊆ refs`, by
`accepts_correct` and the protocol clause P7
(`synchronised_of_delivery`, §6.7).

The timing form, consumed by the GST route of §6.8, is partial synchrony in
the sense of Dwork, Lynch and Stockmeyer [DLS88], written on wall-clock
stamps — `built v n` is the time at which `v` built its round-`n` block,
`blk v n` that block, `gst` the stabilisation time and `delay` the bound Δ
(the full structure is displayed in §6.8):

```lean
covers : ∀ v ∈ T, ∀ w ∈ T, ∀ n < N, gst ≤ built w n →
  built w n + delay ≤ built v (n + 1) →
  blk w n ∈ (U.block (blk v (n + 1))).refs
```

If `w` built its round-`n` block after GST, and `v` began its round-`(n+1)`
block at least Δ later, then `v` references `w`'s block. Note that this too
is conditional, and on a premise the network does not control: that `v`
actually waited. Discharging it is the protocol's obligation, which is why
P9 (`waits`, `prompt`) stands beside N2 in this section rather than inside
it, and why §6.11 must determine *how long* is long enough — `D₀ + Δ`,
which is `2Δ` under a common start. §13.1 gives the counterexample that
makes the point: under instantaneous delivery, a protocol that builds on
the first quorum to arrive can violate coverage for ever, so no strengthening
of N2 alone would suffice.

#### What neither assumption says

- **Nothing about Byzantine senders.** A Byzantine validator may deliver a
  block to some correct validators and not others, may send two
  equivocating blocks to two different correct validators, or may publish
  nothing at all. Both N1 and N2 quantify over *correct* authors only, and
  the safety results tolerate the rest unconditionally: a Byzantine block
  that reaches one view and not another is precisely the situation the
  cross-view theorems of §5 are stated to survive.
- **Nothing about which blocks arrive**, beyond the correct ones after `R`.
  N1 promises a quorum, not a particular sender's block.
- **Nothing before GST**, in N2's case — arbitrary delay, arbitrary
  reordering and arbitrary loss are permitted, and every safety result and
  L1 continue to hold there.

#### Where the assumptions are consumed

Neither assumption is used where its name suggests, and the extracted
support graph (§12) makes the pattern checkable rather than asserted.

**N1 has exactly one primitive consumer: L1 (`no_stall`).** It appears in
the hypotheses of a great many statements — L6, the quantitative results,
the capstones of §§7–10 — but always threaded through to that one place.
Its job is *block production*, not synchrony: a populated round means a
quorum of authors exists, N1 converts that into "every correct validator
has accepted a quorum", and that discharges the premise of P8, which
produces the next round. The chain is `N1 + P8 → Populated`, with no
coverage, no `R` and no Δ anywhere in it. (The only other direct uses are
a repackaging, `card_authorsAt_of_live`, and the garbage-collection
transfer lemma `deliversQuorum_chopD`, which re-establishes N1 on the
truncated universe so that L1 runs there too.)

**And from `R` on, N1 is a theorem rather than an assumption:**

```lean
theorem card_creators_accepted_of_eventuallyDelivers {R : ℕ} (D : Delivery U)
    (hd : EventuallyDelivers D R) (hn : R ≤ n) (hpop : Populated U n)
    {v : Validator} (hv : v ∈ (Correct : Finset Validator)) :
    (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (D.accepted v n)).card
```

N2 puts every correct round-`n` block in `v`'s hands, `accepts_correct`
obliges `v` to accept them, `Populated` supplies one per correct
validator, and `|Correct| ≥ n−f`. So N1's real content is confined to the
pre-GST prefix, which is exactly the price the structural condition
carries.

Before `R` it is *not* derivable, and the reason is worth stating because
it locates a subtlety in the trust boundary. Nothing obliges a validator
to accept a **Byzantine**-authored block: `accepts_correct` covers correct
authors only. With `f` Byzantine validators and `f` slow correct ones, a
validator holds `f+1` correct blocks and `f` Byzantine ones — a quorum in
`held` — but if it declines the Byzantine ones, `accepted` carries only
`f+1` creators, short of the quorum. **N1 is therefore a joint condition
on the network and the acceptance policy**, not a pure network
assumption. That is not a hypothetical concern: the novelty budget of §8
is precisely a rule that declines, which is why `dos_resistance` takes N1
*and* the budget together — the pairing is the formal statement that the
budget must be set loose enough to keep N1 true.

**N2's abstract form is used for five distinct things**, only the first
of which is coverage: L7a (§6.7); the view-gap constant C3′ and hence the
budget sandwich of §8.4, where it says a correct validator's block —
carrying its whole accepted store — arrives and is accepted; the
accepted-quorum lemma above; the bound placing the attested base inside a
correct peer's retained store (G6b, §9.3); and the one-round
universalisation of possession (G9, §9.5). The common thread in the last
four is not "references cover the round below" but "a correct validator's
store reaches every correct validator in time" — a fact about **stores**,
where coverage is a fact about **references**. One assumption serves both
because it is stated on `held`, upstream of the split. N2's timing form,
by contrast, is consumed exactly once, in L7b.

#### How the formulations relate

N2 has more than two statements, and they form a hierarchy rather than a
set of alternatives. Ordered from the most primitive:

| | Statement | Over |
|:---|:---|:---|
| view convergence | after GST, what a correct validator holds reaches every correct validator within Δ | views, at instants |
| `Timing.covers` | after GST, a block built early enough is *referenced* | blocks and references |
| `EventuallyDelivers` | every correct block is held at the moment of building | holdings, at build index |

Each is obtained from the one above it by applying a clause of the
protocol, and §6.9 proves the reductions: `covers` is view convergence
composed with P7 (`references`), and `ViewSync.toTiming` exhibits a
view-convergent execution as a timed one, so every result of §6.8 applies
to it unchanged.

The consequence for this section is a correction and a simplification.
The correction: `Timing.covers` is **not** a pure network assumption. Its
own comment concedes the point — *"a `T`-block built at time `t` is in
every `T`-validator's hands by `t + delay`; **and** a validator
references everything it holds"* — so it fuses N2 with P7 and straddles
the line this section draws. The simplification: once the two are
separated, the network's entire contribution is a single sentence about
views, containing no block, no round and no reference, and every clause
about what validators *do* sits on the protocol side where it belongs.

Two further relations are worth recording, both proved in §6.9. The
bound factors out: convergence within Δ is exactly eventual convergence
whose lag is uniformly bounded after GST
(`convergesWithin_iff_bounded`), so *view convergence under synchrony =
view convergence + a bound*. And eventual convergence **alone** yields
nothing — an unbounded lag cannot be compared with a timeout, so the
block cannot be shown to arrive before the builder acts. The missing
ingredient is not a stronger network but the protocol's waiting rule,
which is why P9 sits beside N2 in this section rather than inside it.

#### The asymmetry, and the payoff

The two are deliberately unequal. N1 is weak — conditional, quorum-sized,
timeless — and does the pre-GST work. N2 is strong — every correct block,
every correct validator, promptly — but is asserted only from GST onward.
Nothing between the two is assumed, and no third condition on the
environment appears anywhere in the development.

**These two are the whole of the trust placed in the environment.** The
safety results of §5 use neither: they hold under arbitrary asynchrony,
arbitrary loss and arbitrary divergence between views. Reference coverage,
the condition on which all of liveness rests, is not a third assumption but
a consequence of N2 with the protocol's own clauses — which is the subject
of §4.4.

### 4.4 Derived, not assumed

Eventual DAG synchrony is not an assumption of the development. It is a property
of executions, obtained from the network assumption together with the protocol:

| Route | From | Result |
|:---|:---|:---|
| Delivery | N2 (`EventuallyDelivers`) with P7 | `synchronised_of_delivery` |
| Timing | N2 (`Timing.covers`) with P9 | `Timing.synchronisedOn_of_timing` |
| View convergence | N2 (`converges`) with P7 and P9 | `ViewSync.synchronisedOn_of_converges` |

The third derives the second (`ViewSync.toTiming`, §6.9), so the routes
are a hierarchy and not a menu; and a fourth result on the same
foundation derives *production* rather than coverage, discharging N1
(`populated_of_viewsConverge`).

It is stated as a hypothesis of L4 and L6 in order to keep those arguments free
of temporal notions (§6.10), and supplied to them by the results above. §13
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

The results of §6.11 require the following in addition. R1–R3 are further
specification, strengthening clauses already present; only the round-`0` spread
of R4 is an assumption, and it concerns deployment rather than the network.

| | Clause | Kind | Yields |
|:---|:---|:---|:---|
| R1 | `Rated timeout`: `∀ n, n ≤ timeout n` | specification | an explicit round `R` |
| R2 | `FairWithin T w`: a `T`-leader within every window of `w` slots | specification | a bounded committing slot |
| R3 | `BoundedSpacing s`: slots at most `s` rounds apart | specification | that slot's round, and a horizon |
| R4 | `∀ n, D₀ + Δ ≤ timeout n`, with round-`0` spread at most `D₀` | specification; `D₀` deployment | the wait bound `Delay(Δ)` |

Every result of §5 and §6.1–§6.10 stands without them.

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
    (h₁ : Fintype.card Validator - F.f ≤ Q₁.card)
    (h₂ : Fintype.card Validator - F.f ≤ Q₂.card) :
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
    (hQquorum : (Fintype.card Validator - F.f) ≤ (creatorsOf U.block Q).card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 2 ≤ (U.block c).round) :
    Reaches U c b
```

Once a quorum of round-`(r+1)` blocks references `b`, every block from round
`r+2` onwards has `b` in its causal history. Neither membership of `b` in the
universe nor its round need be assumed; both follow from the quorum hypothesis
(`mem_ids_and_round_of_quorum_support`).

The bound `r+2` is tight. At `r+1` there is a counterexample: with `f = 1`
and validators `{A,B,C,D}`, let `b` be `A`'s round-`r` block, referenced by
the round-`(r+1)` blocks of `A`, `B` and `C`; `D`'s round-`(r+1)` block may
reference `{B,C,D}`'s round-`r` blocks instead, and since all its references
lie at round `r`, it does not reach `b`. Quorum intersection requires two
reference quorums to compare, and `r+2` is the first round that supplies
them.

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

The counting: with `b ≤ f` the number of Byzantine validators, each correct
round-`(r+1)` block names at least `n−f−b` correct round-`r` authors, and
there are `l ≥ 1` such blocks spread over `c = n−b` correct authors, so some
round-`r` author collects support from at least `l(n−f−b)/c` of them. Were
that always below the needed threshold, the arithmetic obligation would
reduce to `c² ≤ f(l+c)`, which `l ≤ c` converts to `c ≤ 2f` — contradicting
`c ≥ n − f ≥ 2f+1`.

### 5.3 Consistency of the direct rules

**M3** (`certificates_eq_empty_of_directSkip`). A directly skipped block has no
certificate anywhere in the universe, not merely none within some view. Given
`n−f` blamers, and since a correct validator cannot appear on both sides
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
`n−f` distinct voters, so the voter sets intersect in a correct validator `w`
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
accordingly (§4.4, §13.2).

### 6.1 Density

**L0.**
```lean
theorem card_authorsAt_of_lt {r n : ℕ} (hn : n < r) {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    (Fintype.card Validator - F.f) ≤ (authorsAt U n).card
```

If any block exists at round `r`, every round below `r` has at least `n−f`
distinct authors. The result requires no assumption beyond validity. Its content
is not that the DAG grows, but that it cannot grow tall and thin: a single block
high in the DAG forces a quorum of authors at every round beneath it.

### 6.2 The delivery layer

```lean
structure Delivery (U) where
  held : Validator → ℕ → Finset BlockId
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  accepted : Validator → ℕ → Finset BlockId
  accepted_sub : ∀ v n, accepted v n ⊆ held v n
  accepted_inj : ∀ v n, ∀ i ∈ accepted v n, ∀ j ∈ accepted v n,
    (U.block i).creator = (U.block j).creator → i = j
  accepts_correct : ∀ v ∈ Correct, ∀ n, ∀ a ∈ held v n,
    (U.block a).creator ∈ Correct → a ∈ accepted v n
  includes : ∀ v ∈ Correct, ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    accepted v n ⊆ (U.block b).refs
```

The indexing of `held` is essential: `held v n` denotes what `v` had in hand *at
the moment it built its round-`(n+1)` block*, not what `v` eventually receives.
This is the build-time index which a view cannot supply (§13.1). Between holding
and referencing sits **acceptance** — at most one block per author, correct
blocks always taken — which is deliberately where the protocol may refuse:
the DoS arc's novelty budget (§8) is a rule about `accepted`, and the
liveness development reads only `accepted`.

The structure contains no clock. In the absence of a time model, "waited longer"
can manifest only as a larger `held`, which is what allows the timing layer of
§6.8 to be placed beneath without disturbing anything above it.

The network assumption stated over this structure is N1
(`DeliversQuorum`), displayed and discussed in §4.3; the liveness results
below consume it as a hypothesis. Two of its features matter here: it is
conditional, so it does not assert the block production §6.3 establishes,
and it carries no round bound, so the results resting on it hold before GST
as well as after.

### 6.3 Progress, and the horizon

```lean
def PopulatedOn (U) (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r

structure Live (U) (D : Delivery U) (N : ℕ) : Prop where
  genesis : Populated U 0
  builds : ∀ r < N, ∀ v ∈ Correct,
    (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (D.accepted v r)).card →
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

All four combinations occur: `N` large with `R` small is a tall,
synchronous DAG that commits; `N` large with `R` large (or with coverage
never holding) grows for ever and commits nothing; `N` small with `R` small
is synchronous but too short to commit; `N` small with `R` large is short
and asynchronous.

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
correct block of the round below already names at least `n−f` distinct creators,
so P3 is satisfied without any Byzantine reference.

The predicate is antitone in `T` (`SynchronisedOn.mono`), which allows results
established at `T := Correct` to be supplied to the quorum-relative statements of
§6.6.

The condition is derived, not assumed (§4.4); §13 discusses its formulation.

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
theorem directCommit_of_leader_mem (hcard : (Fintype.card Validator - F.f) ≤ T.card)
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

theorem commits_recur_on (hT : T ⊆ Correct)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
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
view-shaped statement lacks (§13.1).

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
is unknown; §6.11 supplies two further routes.

### 6.9 Deriving coverage: the view-convergence route

The two routes above state the network's contribution over objects the
protocol builds — `held` in one case, `refs` in the other. A third states
it over **views**, which is where this development's design notes wanted
it from the outset, and derives the other two rather than standing beside
them.

```lean
structure ViewSync (U) (T : Finset Validator) (N : ℕ) where
  …                                        -- as `Timing`, minus `covers`
  holds : Validator → ℕ → Finset BlockId
  holds_own  : ∀ v ∈ T, ∀ n ≤ N, blk v n ∈ holds v (built v n)
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  converges  : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  references : ∀ v ∈ T, ∀ n < N, ∀ a ∈ holds v (built v (n + 1)),
    (U.block a).round = n → a ∈ (U.block (blk v (n + 1))).refs
```

`holds v t` is what `v` holds **at time `t`** — the temporal index a
`View` cannot supply (§13.1). `converges` is then partial synchrony
stated exactly as one would say it in words: *after GST, whatever a
correct validator holds reaches every correct validator within Δ*. It
mentions no block, no round and no reference.

**What this buys: `covers` was two clauses, not one.** §4.3 recorded that
`Timing.covers` concludes about `refs` and so fuses a network guarantee
with the protocol's referencing rule — its own comment says so. Here they
are apart: `converges` is the network's, `references` is P7 in the timed
setting, and the fused field is a *theorem*:

```lean
theorem covers_of_converges : … vs.blk w n ∈ (U.block (vs.blk v (n + 1))).refs
```

The block is in its author's hands when built (`holds_own`), reaches the
builder within `delay` (`converges`), is still there when the builder
acts (`holds_mono` — which is where the hypothesis
`built w n + delay ≤ built v (n+1)` is spent), and is therefore
referenced (`references`).

**And the routes form a hierarchy, not a pair.** `ViewSync.toTiming`
exhibits a `ViewSync` as a `Timing`, so every result of §6.8 applies
unchanged — drift still derived from `prompt`, the backoff still
terminating, the quantitative bounds of §6.11 unaffected. The timing
route is thus what the view-convergence route *becomes* once P7 is
applied, and the correction to §4.3's earlier claim is that the two forms
of N2 do reduce, once `covers` is unfused.

**The bound, factored out.** `converges` is partial synchrony in its
familiar two-part shape, and the parts separate:

```lean
def ConvergesEventually (holds) (T) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ t, ∃ d, holds w t ⊆ holds v (t + d)

def ConvergesWithin (holds) (T) (gst bound : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + bound)
```

Under monotone holdings these are related by
`convergesWithin_iff_bounded`: convergence within a bound *is* eventual
convergence whose lag is uniformly bounded after `gst`. So

> view convergence under synchrony = view convergence + a bound on the lag,

and `converges` is the second (`ViewSync.convergesWithin`), with the
first following for free (`ViewSync.convergesEventually`).

**The bound is load-bearing, and the reason is worth stating.** Eventual
convergence alone yields nothing: the derivation above needs the block in
the builder's hands *before* it builds, which is arranged by choosing a
timeout that exceeds the lag. A lag that merely exists cannot be compared
with a timeout — the existential `d` is uncomparable with any schedule —
whereas a lag bounded by `delay` can, and `D + delay ≤ timeout n` is
precisely where the comparison happens. This is also why the bound is
asserted only from `gst`: before it there is nothing for a timeout to
clear, which is the content of partial synchrony rather than an artefact
of the encoding.

**Index-aligned agreement, derived.** The statement that build-time views
*agree* — every `T`-authored round-`n` block in every `T`-validator's
holdings at the moment it builds for `n+1` — follows from the same three
ingredients:

```lean
def ViewsAgree (R : ℕ) : Prop :=
  ∀ v ∈ T, ∀ u ∈ T, ∀ n, R ≤ n → n < N →
    vs.blk u n ∈ vs.holds v (vs.built v (n + 1))

theorem viewsAgree_of_converges (hT) (hD : DriftFrom R D) (hgst)
    (hbackoff : ∀ n, R ≤ n → D + vs.delay ≤ vs.timeout n) : vs.ViewsAgree R
```

the bound (to compare a lag with a timeout at all), the drift (to compare
one validator's clock with another's) and the wait (to push the build
past both).

**The untimed variant, and what it conceals.** The same shape can be
written with no clock at all, over `Delivery`:

```lean
def ViewsConverge (D : Delivery U) : Prop :=
  ∀ v ∈ Correct, ∀ w ∈ Correct, ∀ n, ∀ b ∈ D.held v n,
    (U.block b).creator ∈ Correct → b ∈ D.held w n
```

*What a correct validator holds when it builds for round `n`, every
correct validator holds when it builds for round `n`.* No Δ, no GST: the
"eventually" is carried by the build-time index, which is logical rather
than temporal, so a validator that waits arbitrarily long still builds at
index `n`. Restricted to correct-authored blocks, since selective
Byzantine sending must remain permitted (§4.3).

With `HoldsOwn` — an author has its own block in hand when it builds the
next — this yields `EventuallyDelivers` from round `0`, and hence
**production without N1**:

```lean
theorem populated_of_viewsConverge (H : Live U D N)
    (hvc : ViewsConverge D) (hown : HoldsOwn D) : ∀ r ≤ N, Populated U r
```

L1's conclusion, drawn from a view-shaped assumption rather than from
`DeliversQuorum`. The induction is L1's, with the quorum obtained
differently: rather than assuming a quorum is delivered whenever one
exists, the previous round's population supplies `|Correct| ≥ n−f`
correct blocks and convergence puts every one of them in every correct
validator's hands.

Two things must be said about this, because the appearance is that N1 has
been obtained for free. It has not. First, index-aligned sharing of every
correct block is **stronger** than N1, which promises only a quorum and
only when one exists; what is bought is uniformity of shape, not a weaker
hypothesis. Second, and more interesting: **the untimed condition is not
a delivery assumption at all, but a delivery assumption fused with a wait
clause.** In the untimed model that fusion cannot be undone, and the
reason is structural — `Delivery.held v n` is indexed by the *round*, and
`held_spec` confines it to round-`n` blocks, so a round-`n` block can only
ever appear at index `n`. "It arrived, but after `v` had already built"
is not expressible; the model has nowhere to place the arrival event
relative to the build event. Separating the two requires an ordering of
those events — which is to say a clock — and once there is one, the split
is exactly `converges` against `waits`, and `viewsAgree_of_converges` is
the bridge from the unfused pair to what the untimed model must postulate.

### 6.10 The layering

![**The core account: what supports what.** Every arrow is extracted from the compiled Lean environment — `A → B` means `A` is used in the proof of `B`, directly or through unlabelled lemmas, with arrows implied by longer paths removed. Assumptions occupy the left column; each further column is one step from them. A box with no incoming arrow rests only on definitions and unlabelled lemmas — L4 is the notable case, taking its quorum as a hypothesis rather than from the fault model. §12 describes the extraction; a version carrying each result's Lean name is in `docs/depgraph/`.](depgraph/support-core-compact.svg)

No theorem above `SynchronisedOn` mentions time, and no theorem below it mentions
certificates. The diagram also locates the trust boundary: the leftmost column is
the whole of what is assumed, and it divides into assumptions about an adversarial
network (N1, N2) and clauses of the algorithm (P1–P10) — the derivations of
coverage are visible as the only results drawing on the network column.

**Three separations, and they are different in kind.** The development
draws three lines, and it is worth being explicit about which does what,
since only the first is the one usually meant by "confining the time
model".

*Time from graph structure* — the interface is `SynchronisedOn`.
Everything above it is finite combinatorics over a DAG; everything that
mentions an instant lies below. The interface is a `Prop` about
references, so the layers meet at a statement rather than at a module
boundary, and any of the three routes of §§6.7–6.9 may supply it. This is
the separation the report's title claims, and the diagram shows it as a
single column that every liveness result passes through.

*Network from protocol* — the interface is the pair
`converges` / `references` of §6.9. This line is invisible in the delivery
and timing routes: `EventuallyDelivers` is indexed at build time, and
`Timing.covers` concludes about `refs`, so each silently carries some
protocol content. Only the view-convergence route states the network's
contribution in a form containing nothing the protocol does, which is why
§4.3 can now claim that the network's whole contribution is one sentence
about views.

*Assumed from derived* — the interface is `Populated`. Production may be
assumed (the timing structures carry `blk`, a block per validator per
round), or derived (N1 with P8, through L1, or view convergence with
`HoldsOwn`, through `populated_of_viewsConverge`). Which side of this line
a development stands on is a modelling choice rather than a theorem, and
§4.3 keeps N1 precisely because deriving production from a *conditional
quorum* hypothesis is the weaker and the implementable option.

The routes may therefore be summarised by what each assumes and what it
still owes:

| Route | Network assumption | Also needs | Yields |
|:---|:---|:---|:---|
| Delivery (§6.7) | `EventuallyDelivers` — build-time indexed | P7 | `Synchronised` |
| Timing (§6.8) | `Timing.covers` — Δ after GST, concludes on `refs` | P9, drift | `SynchronisedOn` |
| View convergence (§6.9) | `converges` — Δ after GST, over views | P7, P9, drift | `SynchronisedOn`, and the other two |
| Untimed views (§6.9) | `ViewsConverge` — no bound, index-aligned | `HoldsOwn` | `Populated`, without N1 |

Read downward, the first three are increasingly primitive statements of
the same assumption; read across, the fourth is the only one that buys
production rather than coverage.

### 6.11 Quantitative results

The results of this section are collected in a separate module which nothing else
imports. Each strengthens a result above and is purchased with a strengthened
clause (§4.5); a reader declining those clauses retains §6.1–§6.10 intact.

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

`BoundedSpacing` has no counterpart among the weak hypotheses. Eligibility
bounds an anchor's round from *below*, which is what safety requires, the
anchor of M4 being obliged to clear the decision round. A latency claim requires the opposite
bound, and the class provides none, no safety result having occasion to ask for
one. Supplying the mirror image is what converts a bound on the slot index into a
bound on its round.

**The wait bound.**
```lean
theorem directCommit_of_wait (tm : Timing U T N) (hT : T ⊆ Correct)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
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

## 7. Chain quality: coverage and inclusion

*(design record: `chain-quality.md`; modules `LeanDag/Quality/`)*

Every protocol of this family claims that leader rotation prevents
censorship; this section proves what the ledger actually contains. A
commit does not append one block — it flushes the entire causal cone of
the committed leader (§3.6) — and two families of theorems, split
exactly along the trust boundary, say whose blocks the flush carries:
**coverage**, an aggregate guarantee that holds with no synchrony
assumption anywhere; and **inclusion**, an individual guarantee that
genuinely costs the synchrony round `R`, with a witness model proving
the cost is real.

The metric is **distinct correct authors per round**, not a block-count
fraction: an equivocator can inflate a cone with any number of blocks
per round, so the conventional fraction is adversary-deflatable, while
the author count is what the quorum structure bounds.

```lean
def coveredAt (U) (b : BlockId) (δ : ℕ) : Finset Validator :=
  (Correct : Finset Validator).filter fun v =>
    ∃ i ∈ history U b, (U.block i).creator = v ∧ (U.block i).round = δ
```

**Coverage (CQ1–CQ3), asynchronous.** Density (D25, §8) forces every
layer of every valid cone to carry all but at most `f` correct
authors, and a committed leader's block is in particular valid — any
commit route, any view:

```lean
theorem card_coveredAt_ge_of_decided (h : Decided U V k (some L))
    (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card - F.f ≤ (coveredAt U L δ).card

theorem card_correct_le_two_mul_coveredAt_of_decided …
    (Correct : Finset Validator).card ≤ 2 * (coveredAt U L δ).card
```

— **every commit carries, at every round below it, blocks from at
least half of the correct validators** (`|Correct| ≥ 2f+1` makes
`|Correct| − f` at least half), and the cumulative ledger form
(`ledger_coverage`) exhibits, for any verdict assignment covering a
committed slot, a set of at least `|Correct| − f` correct validators
each with a round-`δ` block in `ledgerSet`. No synchrony, no delivery
model, no populated rounds appear in any hypothesis.

**The boundary, witnessed.** Aggregate coverage is *not* individual
inclusion. The witness model `Ucens` (§11) runs six rounds in which
three validators reference only each other and commit with the full
certificate pattern, while a fourth — correct, building validly, never
referenced — is the missing author of **every** layer of **every**
flush: `missingAt = {3}` throughout, so CQ1's `≤ f` is exactly tight,
and `Synchronised` fails at every round while the commit stands. The
same correct validator can be censored for ever under asynchrony; no
validity, delivery or liveness clause objects.

**Inclusion (CQ5–CQ7), post-`R`.** After the DAG synchronises, the
backbone (§8.2) puts every correct block in the cone of every
correct-led commit at any later round
(`mem_history_of_decided_commit`), and fairness supplies such a commit:

```lean
theorem committed_of_correct_block (hT : T ⊆ Correct)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (fair : FairScheduleOn T) (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      ∀ U D N, Live U D N → DeliversQuorum D → Synchronised U R →
        S.slotRound k' + 2 ≤ N →
        ∃ L, Decided U (View.full U) k' (some L) ∧
          ∀ b ∈ U.ids, (U.block b).creator ∈ Correct →
            (U.block b).round = m →
            b ∈ history U L ∧
            ∀ g n, g k' = some L → k' < n → b ∈ ledgerSet U g n
```

— for every round `m ≥ R` the schedule fixes, *before the universe is
quantified*, a committed slot whose flush contains every correct
round-`m` block. (One composition note: `commits_recur_on` does not
expose the committed leader's membership in `T`, which the backbone
needs, so the proof composes from the fair schedule, L4 and `no_stall`
directly, mirroring L6's own proof.) The quantitative forms pin the
slot to a window: under `FairWithin T w` the committing slot lies
within `w` slots of the first slot above round `m`
(`committed_of_correct_block_within`), and under `BoundedSpacing s` its
round within `s·w` rounds (`committed_of_correct_block_by_round`) — *a
correct block is committed within a schedule-window of its creation,
once the DAG is synchronous*. The capstone `chain_quality` packages
both halves under enforceable or standard conditions only.

A block-count purity variant was assessed against a recorded gate and
dropped: under `DoSValid` alone the per-author block count carries the
exponential constant of §8.3, and under the budget the cone-level
Byzantine count is a whole-store bound — neither yields a ratio worth
quoting, and the author-coverage metric is the honest one.

---

## 8. Denial of service: equivocation, growth, and the novelty budget

*(design record: `dos-equivocation-and-growth.md`; modules `LeanDag/DoS/`)*

Safety needs no protection from equivocation: every result of §5 holds with no
anti-equivocation condition anywhere in its hypotheses, and the independence is
itself recorded — a witness model satisfies safety while violating every
storage condition of this section (`LeanDagTest/DoS/SafetyUnderDoS.lean`).
*Storage* is another matter. An uncertified DAG admits Byzantine blocks into
correct views by design, an equivocator may produce arbitrarily many blocks
per round, and a correct validator that retains the cones of what it accepts
can be made to retain the attacker's freight. This section bounds that
freight twice over: first under a *reference-validity* condition (exposure),
whose bound is shown essentially optimal yet exponential in `f`; then under a
*rate-limiting* condition (the novelty budget), which is enforceable,
author-blind, and yields the linear headline `dos_resistance`. The two
compose: the budget paces what an equivocator can inject, exposure ends it.

### 8.1 The store, and what growth means

A validator's store is the accumulation of the cones of everything it
accepted (§6.2 introduced acceptance):

```lean
def viewUpto (D : Delivery U) (v : Validator) : ℕ → Finset BlockId
  | 0 => (D.accepted v 0).biUnion (history U)
  | n + 1 => viewUpto D v n ∪ (D.accepted v (n + 1)).biUnion (history U)
```

`viewUpto D v n` is everything `v` has retained by round `n`: accepting a
block means holding its entire causal history — that is what downward
closure of views (§2.3) demands. Growth questions are questions about
`(viewUpto D v n).card`, and since correct production alone contributes
`|Correct|` blocks per round, *linear in `n`* is the best possible shape;
the question is the constant, and whether the Byzantine share can exceed it.

The *novelty* of an arriving block is what its cone adds over the store:

```lean
def novelty (U) (V : Finset BlockId) (b : BlockId) : Finset BlockId :=
  history U b \ V
```

Novelty is antitone in the store — the more a validator already holds, the
cheaper any block is — which is the monotonicity every argument below leans
on.

### 8.2 Exposure, and the DoS-validity condition

An author is *exposed* in a cone that holds two of its blocks from one
round; the DoS condition forbids building on the exposed:

```lean
def EquivPair (U) (X : Validator) (i j : BlockId) : Prop :=
  i ≠ j ∧ (U.block i).creator = X ∧ (U.block j).creator = X ∧
    (U.block i).round = (U.block j).round

def ExposedIn (U) (b : BlockId) (X : Validator) : Prop :=
  ∃ i ∈ history U b, ∃ j ∈ history U b, EquivPair U X i j

def DoSValid (U) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator
```

Exposure is objective — a property of the cone, checkable by any holder —
and *monotone up the DAG*: a cone containing an exposing cone is exposing.
Only the guilty are ever exposed (a correct author has one block per round,
by non-equivocation), and at most `f` authors are exposed in any one cone:

```lean
theorem card_exposedTo_le (hb : b ∈ U.ids) : (exposedTo U b).card ≤ F.f
```

Exclusion costs quorum *margin*, not liveness. At the extreme — every
Byzantine validator caught — the condition pins references exactly:

```lean
theorem creators_refs_eq_correct (hdos : DoSValid U) (hb : b ∈ U.ids)
    (hround : 0 < (U.block b).round) (hk : F.f ≤ (exposedTo U b).card) :
    creatorsOf U.block (U.block b).refs = (Correct : Finset Validator)
```

— the references of every later block are precisely the correct validators,
and the commit chain still runs on them: the witness model `Uexcl` carries a
direct commit whose three rounds all lie after the exclusion of its
equivocator (§11). Exclusion also does not depend on luck: *density* says a
cone can be selectively blind to at most `f` correct authors per round, even
below Byzantine blocks, because the quorum clause forces every layer of
every valid cone to carry `n − f` distinct authors:

```lean
theorem card_missingAt_le (hb : b ∈ U.ids) (hδ : δ < (U.block b).round) :
    (missingAt U b δ).card ≤ F.f
```

where `missingAt U b δ` is the set of correct authors with no round-`δ`
block in `H(b)`.

### 8.3 Growth under the condition alone: the exponential wall

How large can one cone be under `DoSValid` alone? Byzantine authors are
excluded only *after* both halves of an equivocation meet in one cone; until
then, distinct branches may carry distinct halves, and `e` cooperating
equivocators can chain reveals so that each unexposed author doubles the
mass a branch may adopt. The general upper bound is proved through
*pedigrees* — for each exposed author, the chain of adoption events by which
its blocks entered the cone — and is linear in the round with a constant
exponential in `f`:

```lean
theorem card_history_le' (hdos : DoSValid U) (hb : b ∈ U.ids) :
    (history U b).card
      ≤ (Fintype.card Validator + (Fintype.card Validator - 1) * F.f ^ F.f) *
          ((U.block b).round + 1)
```

The exponential constant is not slack in the proof: a matching family of
witnesses (`Udouble`, §11) realises `2^(e−2)` growth from `e` equivocators,
so any bound obtainable from reference-validity conditions alone carries a
constant exponential in `f`. That is the honest verdict on the exposure
mechanism as a *storage* defence: it is the right accountability layer — it
identifies and permanently retires equivocators at the cost of quorum
margin — but no practical storage bound can rest on it. Rate limiting is
needed, and it is orthogonal.

### 8.4 The novelty budget

The budget is a rule about acceptance, and deliberately about nothing else.
Two formulations are related. The analysis-side form guards on the author
being Byzantine; the mechanism-side form is the rule a validator can
actually run — **author-blind**, since correct validators cannot in general
tell who is Byzantine:

```lean
def ByzBudget (D : Delivery U) (κ : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (U.block b).creator ∉ (Correct : Finset Validator) →
    (novelty U (viewUpto D v n) b).card ≤ κ

def UniformBudget (D : Delivery U) (T : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (novelty U (viewUpto D v n) b).card ≤ T

def RefsAccepted (D : Delivery U) : Prop :=
  ∀ w ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = w → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted w n
```

`RefsAccepted` is the converse of `includes` (§6.2): together they say a
correct block's references are *exactly* its author's acceptances — local,
observable conduct. The blind and guarded budgets sandwich each other within
one factor of `f`:

* `UniformBudget.byzBudget : UniformBudget D T → ByzBudget D T` — dropping
  a guard weakens nothing; and conversely
* `uniform_of_byzBudget` — post-`R`, under `ByzBudget κ`, *every*
  acceptance (correct authors included) adds at most `f·κ + 1`.

The converse direction is the interesting one, and its engine deserves
stating. Why would a *correct* author's block have small novelty? Because a
correct block's cone is a complete record of everything its author ever
accepted — `includes` puts each round's acceptances among the next block's
references, and the self-parent chain (P3′) carries every earlier round
forward:

```lean
theorem viewUpto_subset_history (hw : w ∈ Correct) (hb : b ∈ U.ids)
    (hbc : (U.block b).creator = w) (hbr : (U.block b).round = n + 1) :
    viewUpto D w n ⊆ history U b
```

One delivered block therefore erases the entire standing gap between two
correct stores — the DAG is its own repair channel, and no cone-exchange
protocol needs modelling. Quantitatively, the gap between correct stores is
a *constant*, not a drift (`card_viewGap_succ_le`): post-`R` it is at most
`f·κ`, one round of Byzantine budget, however long the system has run.

The same self-parent mechanism yields a pure-DAG form worth isolating: if
every correct block adds at most `κ'` over its self-parent (`StepNovelty`),
then correct cones are linear outright,
`|H(b)| ≤ κ'·round(b) + 1` (`card_history_le_of_stepNovelty`) — a telescope
along the self-parent chain, with no delivery model at all.

### 8.5 The headline, and the composition

Under the guarded budget the Byzantine share of a correct store is priced
through a global object, the *pool* — the Byzantine-authored blocks any
correct validator retains:

```lean
def byzPool (D : Delivery U) (n : ℕ) : Finset BlockId :=
  (Correct : Finset Validator).biUnion fun w =>
    (viewUpto D w n).filter fun i => (U.block i).creator ∉ Correct
```

A Byzantine block enters the pool only as a direct budgeted acceptance — if
it arrived inside a correct block's cone, `RefsAccepted` places it in that
author's *earlier* store — so the pool grows by at most `|Correct|·f·κ` per
round (`card_byzPool_le`), and the store bound follows:

```lean
theorem card_viewUpto_le (hbyz : ByzBudget D κ) (hra : RefsAccepted D)
    (hv : v ∈ Correct) (n : ℕ) :
    (viewUpto D v n).card ≤
      (Correct : Finset Validator).card * (n + 1) +
        ((Correct : Finset Validator).card * F.f +
          n * ((Correct : Finset Validator).card * (F.f * κ)))
```

— correct production, a Byzantine genesis allowance, and a Byzantine rate.
The capstone quotes **enforceable conduct only** — the author-blind budget,
the reference rule, and the liveness hypotheses of §6 — and delivers
liveness and storage from one set of premises:

```lean
theorem dos_resistance {T N : ℕ} (H : Live U D N) (hd : DeliversQuorum D)
    (hu : UniformBudget D T) (hra : RefsAccepted D) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto D v n).card ≤
          (Correct : Finset Validator).card * (n + 1) +
            ((Correct : Finset Validator).card * F.f +
              n * ((Correct : Finset Validator).card * (F.f * T)))
```

with a post-`R` incremental form (`dos_resistance'`) in which the slope is
per-round and the pre-`R` prefix is a single opaque constant. Note what the
hypotheses do *not* contain: no `DoSValid`, no exposure, no appeal to
identifying the Byzantine — the budget alone suffices for the linear bound.

The two conditions then compose. Once every equivocator stands exposed to
every correct validator (`AllExposed U m`), `DoSValid` blocks all further
Byzantine acceptances, the pool freezes at its round-`m` value, and the
store's slope decays to the correct-production rate:

```lean
theorem card_viewUpto_le_of_allExposed' (hdos : DoSValid U)
    (hbyz : ByzBudget D κ) (hra : RefsAccepted D) (hexp : AllExposed U m) …
    (viewUpto D v n).card ≤
      (Correct : Finset Validator).card * (n + 1) +
        ((Correct : Finset Validator).card * F.f +
          (m + 1) * ((Correct : Finset Validator).card * (F.f * κ)))
```

— the budget paces what an author can inject; exclusion ends it. On data,
the budget is satisfiable at its sharp constant: the witness schedule
`Dtwin` satisfies `UniformBudget 3` with its costliest acceptance costing
exactly `3`, and `ByzBudget 0` — nothing Byzantine accepted after the
genesis round (§11).

How should the parameter `T` be set? Any `T ≥ 1` admits every correct block
post-`R` (the sandwich's `f·κ + 1` with `κ = 0` would be the correct-only
floor); smaller `T` tightens the Byzantine rate and defers — never refuses —
expensive correct blocks, deferral being a rate limiter rather than a
verdict, since novelty is antitone in the growing store.

---

## 9. Garbage collection: the horizon

*(design record: `garbage.md`; modules `LeanDag/GC/`)*

The DoS results end at linear-forever storage, and linear still diverges: a
validator that runs for years retains years of history, and a joining
validator must fetch it. The remedy is a **horizon** — a round `G`, chosen
per validator, below which nothing is retained, requested, or served — with
theorems that commit safety, commit liveness, bounded storage, and bootstrap
all survive above it, and that **no consensus on the horizon is ever
needed**. Throughout, `G` denotes a horizon round and `Λ` (the *lag*) how far
a horizon trails the current round; both are per-validator quantities.

One scoping fact first: garbage collection bounds *stores*, not the
universe. `U` — every block any correct validator ever held — keeps growing
as an analysis object; the theorems live at the level of what a validator
retains (`viewUpto`, §8.1) and what a joiner must fetch.

### 9.1 Truncation as rebasing

The model-side operator keeps the blocks at rounds `≥ G`, rebases rounds by
`−G`, and empties the reference sets of the new base layer — the round-`G`
layer becomes the new genesis layer:

```lean
def chopBlock (U) (G : ℕ) (i : BlockId) : Block Validator BlockId Payload :=
  if (U.block i).round ≤ G then
    { U.block i with round := (U.block i).round - G, refs := ∅ }
  else
    { U.block i with round := (U.block i).round - G }

def chop (U) (G : ℕ) : BlockUniverse Validator BlockId Payload where
  ids := U.ids.filter fun i => G ≤ (U.block i).round
  block := chopBlock U G
  …
```

Every validity clause of §2.2 constrains only rounds `> 0`, and the old
genesis special case applies verbatim to the new base — so `chop U G` is a
bona-fide `BlockUniverse`, and **every theorem of this report applies to it
unchanged**. That is the entire design: the work is never re-proving the
theory above the cut, only relating verdicts *across* the cut and choosing
the cut. (In an implementation, block identity is a hash over references, so
emptying the base layer's references is not a re-hash of history: it is the
checkpoint reinterpreting those identifiers as opaque geneses — a rule about
what the sync layer serves.)

The DoS condition crosses the cut one way (`dosValid_chop`): cones shrink
under truncation, so exposure shrinks, so the per-block condition weakens.
The converse fails *by design*, and the failure is the **statute of
limitations**: an equivocation whose witnessing pair falls strictly below
the cut is forgiven — in `chop U G` its author is no longer exposed — while
a pair *at* the cut survives into the base layer. §9.5 prices the
forgiveness; the witness file exhibits it on data, an exposure present in
the full universe and absent from its truncation (§11).

### 9.2 Verdicts survive the cut

Every commit-rule notion of §3 for a slot above the cut is invariant — the
rules read a window of rounds that truncation does not touch:

```lean
theorem certificates_chop (s : ℕ) :
    certificates (chop U G) L s = certificates U L (G + s)
```

and likewise `supporters_chop`, `blames_chop`, `directCommit_chop`,
`directSkip_chop`, and the indirect test `certifiedIn_chop`. The full
decision relation follows under an *induced schedule*: slots re-indexed
from a base slot `d` whose round clears the horizon, with
`Slots.chop S G d hd` given by `slotRound' k = slotRound (d + k) − G` (the
condition `hd : G ≤ S.slotRound d` is what keeps the re-based rounds above
zero, where subtraction is faithful and the schedule's keying survives).
Views truncate by the same filter (`View.chop`), and:

```lean
theorem decided_chop (hd : G ≤ S.slotRound d) :
    Decided (S := S.chop G d hd) (chop U G) (V.chop G) k v ↔
      Decided U V (d + k) v
```

— a validator re-running the protocol on the truncation decides slot `k`
exactly as it decided slot `d + k` on the full universe, by structural
induction through anchors and intermediate skips, in both directions. The
**only hypothesis is the base-slot condition**: no synchrony, no liveness,
no lag bound, no DoS condition. Cross-cut agreement is deliberately
asymmetric:

```lean
theorem decided_agree_chop (hd : G ≤ S.slotRound d)
    (hW : Decided (S := S.chop G d hd) (chop U G) W k w)
    (hV : Decided U V (d + k) v) : w = v
```

Here `W` is an **arbitrary** view of the truncation — not a truncated
full-history view. The asymmetry matters because a joiner's view is never of
the form `V.chop`: lifted to `U` it would not be downward closed, its base
layer having lost its references. The proof plays the agreement theorem of
§5.5 *inside* the truncation against a truncated view, and carries the
verdict across the cut through `decided_chop`. So a validator that joined
from the truncation and never saw the pruned prefix agrees with every
full-history validator, slot for slot.

### 9.3 Windowed storage: constant at a lag

Liveness transfers with the offset: a delivery layer for `U` induces one
for the truncation (`chopD D G`, with `held v m := D.held v (G + m)`), and
`Live U D N` yields `Live (chop U G) (chopD D G) (N − G)` (`live_chopD`).
Stores correspond exactly —

```lean
theorem viewUpto_chopD (m : ℕ) :
    viewUpto (chopD D G) v m =
      (viewUpto D v (G + m)).filter fun i => G ≤ (U.block i).round
```

— pruning a store below `G` yields precisely the store of the induced
delivery, which is what lets §8's bound `card_viewUpto_le` be read on the
truncated universe. Two prerequisites make this legitimate over a *sequence*
of cuts. The budget must be measured on the truncated universe — otherwise
pruning would make every arriving block's novelty explode with the
discarded prefix — and windowed novelty is *antitone under cut-advance*
(`novelty_chop_anti`): as the window slides, pruning only cheapens blocks,
so an affordable block never becomes unaffordable. The budget conditions
themselves descend to the window (`byzBudget_chopD`, `refsAccepted_chopD`).

The storage headline is stated per time, because a validator's life is a
sequence of cuts:

```lean
theorem card_retained_le {κ Λ t : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hv : v ∈ Correct) (hG : G ≤ t) (hΛ : t ≤ G + Λ) :
    ((viewUpto D v t).filter fun i => G ≤ (U.block i).round).card ≤
      (Correct : Finset Validator).card * (Λ + 1) +
        ((Correct : Finset Validator).card * F.f +
          Λ * ((Correct : Finset Validator).card * (F.f * κ)))
```

— **constant in `t`**: at lag `Λ`, the retained store is bounded
independently of how long the system has run. The same constant bounds a
joiner's entire fetch — the attested base plus the window is a *subset of
one correct peer's retained store* (`card_joinIds_le`) — and, plus one, a
correct author's serving obligation: everything it can be asked to serve
for its block is its own retained store above its own horizon, plus the
block itself (`card_serve_le`, via `RefsAccepted` one step down and the
self-parent chain the rest of the way). Garbage collection bounds sync
cost, not just storage, and the honest relay obligation is bounded too.

### 9.4 Bootstrap: the attested base

A validator so far behind that its needs predate every peer's horizon
cannot fetch the prefix; it must adopt a genesis layer from others. Requiring
`f+1` *identical* checkpoints would be wrong — correct validators' layers
share the correct core exactly but differ in Byzantine fringe — so the
primitive is an **inexact certificate**, filtered per block: attest the
layer, keep what `f+1` distinct authors attest. In this model an
attestation *is* a block — its cone is its objective, unforgeable statement
of what the layer contains — so the certificate is DAG-internal, decidable,
and needs no signatures:

```lean
def attesters (U) (t : ℕ) (y : BlockId) : Finset Validator :=
  creatorsOf U.block ((blocksAt U t).filter fun a => y ∈ history U a)

def Base (U) (t G : ℕ) : Finset BlockId :=
  (blocksAt U G).filter fun y => F.f + 1 ≤ (attesters U t y).card
```

The base is **sandwiched** between the shared correct layer and the union of
correct cones: everything in it has a correct attester, so the adversary
cannot smuggle fabrications in (`exists_correct_attester_of_mem_base`);
post-`R`, every correct round-`G` block is in every correct attestation, so
nothing of the correct layer can be filtered out, by anyone
(`correct_mem_base`). Completeness in fact extends to everything
*obtainable* — Byzantine-authored included:

```lean
theorem accepted_mem_base (hs : Synchronised U R) (hv : v ∈ Correct)
    (hy : y ∈ viewUpto D v m) (hyr : (U.block y).round = G)
    (hcar : Populated U (m + 1)) (hpop : Populated U t)
    (hR : R ≤ m + 1) (hmt : m + 2 ≤ t) :
    y ∈ Base U t G
```

— every round-`G` block a correct validator accepted into its window by `m`
is in the base attested at any `t ≥ m + 2`: acceptance puts the block in a
correct store, the store rides into its keeper's next block
(`viewUpto_subset_history`, §8.4), and the backbone carries that block into
every correct round-`t` cone — a cone *is* an attestation. The lag is tight
on data: at `t = m + 1` the witness exhibits an accepted equivocation half
missing from the base (§11). Consequently the joiner's assembly — base as
genesis layer plus a correct peer's window strictly above the cut — is a
bona-fide view of the truncation (`joinView`; downward closure is the
content: window references above the cut stay in the window, references *at*
the cut are exactly the blocks `accepted_mem_base` puts in the base), and:

```lean
theorem bootstrap_agree … (hJ : Decided … (joinView …) k jv)
    (hV : Decided U V (d + k) fv) : jv = fv
```

— any decision reached from base-plus-window equals any full-history
validator's. Inexact certificates, exact decisions; bases sampled from
different peers need never agree, exactly as horizons need not.

### 9.5 Horizons without consensus, and the lag envelope

Each validator sets its own horizon by a local rule — trail the decided
frontier by `Λ`, or trail the current round by `Λ` — and three theorems make
the heterogeneity safe. Verdicts at different horizons are equal outright
(`decided_agree_horizons`, matching slots through their absolute index). A
deeper cut is just another cut:

```lean
theorem chop_chop (hG : G₁ ≤ G₂) :
    chop (chop U G₁) (G₂ - G₁) = chop U G₂
```

so validators at different horizons sit on one tower of truncations, never
in incomparable worlds. And post-`R` possession universalises in **one**
round (`viewUpto_subset_viewUpto_succ`): everything any correct validator
retains by round `m` is in every correct store by `m + 1` — the keeper's
next block carries its whole store, and that block is delivered and
accepted — so pruning at depth `≥ 1` below a correct frontier discards
nothing any correct peer still lacks (`pruned_subset_peer_store`).

What constrains the lag is worth pinning theorem by theorem, because
*safety constrains it not at all*:

| bound | source | what breaks below it |
|:---|:---|:---|
| — (any `G` is safe) | `decided_chop`, `decided_agree_chop`, `bootstrap_agree` | nothing — commit safety carries no lag hypothesis; its only premise is `G ≤ slotRound d` |
| `Λ ≥ 0` vs the *decided* frontier | ledger totality | a slot reads rounds `slotRound k … +2`; cutting above an undecided slot discards its certificates and the slot is undecidable forever — output stalls, safety unharmed |
| `Λ ≥ 1` | `viewUpto_subset_viewUpto_succ` | peer no-desync: possession universalises in exactly one round |
| `Λ ≥ 2` | `accepted_mem_base` (tight) | base completeness for joiners |
| upper bound: none | the §9.3 constants | nothing breaks; storage, join and relay grow linearly in `Λ` |

Finally, the statute of limitations is a bounded-rate, priced phenomenon
rather than a cliff. Within an epoch the entire exposure economy of §8.2
applies to the truncation verbatim — it is just another universe. Across a
cut, a forgiven author must equivocate *again, inside the new window*, to
be debarred again — one reveal per author per epoch — and the re-entry runs
under the windowed budget: `Λ·f·κ` of freight per correct store per epoch,
a term the `card_retained_le` constant already carries. Commit safety never
depended on any of it: the cross-cut results above carry no exclusion,
budget, or exposure hypothesis. A world that forgives every equivocation
still commits the same blocks; it just stores more junk.

---

## 10. Odontoceti: two-round commitment

*(design record: `odontoceti.md`; modules `LeanDag/Odontoceti/`)*

Odontoceti [Van25] commits in **two** communication rounds: a leader block
at round `r` is decided by the supports and blames of round `r+1` alone,
with no certificate round anywhere. The price is a larger committee,
`n = 5f+1`. This section proves safety and liveness of the two-round rule at
the *generalization* `n ≥ 5f+1` — direct thresholds `n − f`, indirect
threshold `n − 3f`, specializing to the published `4f+1` and `2f+1` at the
boundary — and reports four findings about the published safety argument,
one of which is a genuine gap that the formalized rule must repair (§10.4).

### 10.1 The reuse boundary

At `n = 5f+1` Odontoceti's quorums *are* `n − f`: the DAG quorum `4f+1`,
and both direct thresholds. Its validity rules coincide with `ValidWrt`
clause for clause — including the mandatory self-parent (P3′) — and its
support/blame primitives are the `supporters`/`blames` of §3. The entire
DAG layer of this report therefore applies verbatim, and only the rule
layer is new; the fault bound is an *extension*,

```lean
class Faults5 (Validator) extends Faults Validator where
  card_validators5 : 5 * f + 1 ≤ Fintype.card Validator
```

so a `Faults5` instance is a `Faults` instance and every existing theorem
continues to apply to the same types. The stronger bound is consumed in
exactly two proofs (O2 and O4′ below) — the two-round rule's *direct* safety
already holds at `3f+1`. The witness file proves the reuse claim as a
computation: a quorum-5 universe over six validators satisfies the untouched
`BlockUniverse` by `decide` (§11). Nothing outside `LeanDag/Odontoceti/`
was modified.

### 10.2 The rule layer, and the arithmetic core

```lean
def DirectCommit (U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (supporters U L (r + 1)).card

def DirectSkip (U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (blames U L (r + 1)).card

def coneSupports (U) (A L : BlockId) (r : ℕ) : Finset Validator :=
  creatorsOf U.block
    ((blocksAt U (r + 1)).filter
      (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A))

def ThickLink (U) (A L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - 3 * F.f) ≤ (coneSupports U A L r).card
```

`ThickLink` is the indirect test: enough supports for `L` visible in an
anchor's cone. It counts **distinct authors** of in-cone support blocks,
not raw blocks — the published rule says "`2f+1` supports in the history of
the anchor" without disambiguating, and the block count is
adversary-inflatable (an equivocating supporter can plant any number of
support-twins in one cone), while the author count is the one the
arithmetic on both sides actually bounds. Four counting theorems carry
safety, and they locate exactly where the five-`f` committee is spent:

**O1 (commit versus skip; needs only `n ≥ 3f+1`).**
`not_directSkip_of_directCommit`: no block is both directly committed and
directly skipped. Two `(n−f)`-quorums over `n` authors share
`n − 2f ≥ f+1`; an author both supporting and blaming has two distinct
decision-round blocks, so every member of the intersection is an
equivocator — one more than exist.

**O1′ (twin uniqueness; `n ≥ 3f+1`).** `eq_of_directCommit`: two directly
committed same-author blocks are equal. Same intersection; an author
supporting two distinct twins is an equivocator, because one block cannot
cite an author twice (`distinct_creators`) and two supporting blocks are an
equivocation.

**O2 (a skipped leader fails the test everywhere; spends the fifth `f`).**
`card_supporters_le_of_directSkip`: a directly skipped leader's supporters —
anywhere in the universe, hence in any cone — number at most `2f`; and
`2f < n − 3f` exactly when `n ≥ 5f+1`
(`not_thickLink_of_directSkip`). The proof requires the **exact complement
identity** `|Correct| = n − |byzantine|`: correct supporters and correct
blamers are disjoint, correct blamers number at least
`(n−f) − |byzantine|`, and the `|byzantine|` cancels, leaving correct
supporters at most `f`. Bounding `|Correct| ≤ n` instead degrades the
estimate to `3f`, which does *not* clear the threshold at the boundary —
the natural loose count fails, and only the exact one proves the published
lemma.

**O3 (propagation — every anchor's cone is the certificate).**
`thickLink_of_directCommit`: if `L` is directly committed, then *every*
block from two rounds above it onward — Byzantine-authored included,
validity being structural — carries at least `n − 3f` distinct authors of
support blocks in its cone. One hop: a round-`(r+2)` block's `n − f`
distinct-author parents meet the `n − f` supporters in `n − 2f` authors, of
whom up to `f` are Byzantine equivocators whose *referenced* parent may be
a non-supporting twin; the remaining `≥ n − 3f` are correct, and a correct
author's unique decision-round block is both supporting and in the cone.
Depth: cones are monotone through any single parent, so the bound never
decays. This is the two-round replacement for M2/M4: there is no
certificate object, so its rôle is played by the support pattern that every
later cone is forced to contain.

**O4′ (a direct commit excludes every rival; spends the fifth `f`
again).** `eq_of_directCommit_of_thickLink`: a directly committed block is
the *only* same-author block that can pass the indirect test, at any
anchor — `n − f` supporters of `L₁` and `n − 3f` in-cone supporters of a
twin `L₂` would overlap in `n − 5f ≥ 1` correct authors, each supporting
two twins. This lemma has no counterpart in the published argument, and
§10.4 explains why it had to exist.

### 10.3 The decision relation, and agreement

Eligibility contracts by one round —
`decisionRound k = slotRound k + 1` and
`Eligible k j ↔ slotRound k + 2 ≤ slotRound j` — and the view-relative
direct rules lift to universe level exactly as in §3.2. The decision
relation mirrors §3.5 constructor for constructor, with one new premise:

```lean
| indirectCommit :
    k < j → Eligible Validator k j → Decided U V j (some A) →
    (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
    IsLeaderBlock U k L → ThickLink U A L (S.slotRound k) →
    (∀ L', IsLeaderBlock U k L' → ThickLink U A L' (S.slotRound k) → ¬ L' < L) →
    Decided U V k (some L)
```

The final premise — the committed candidate is the `≤`-least one passing
the test at the anchor, under `[LinearOrder BlockId]` — is the *canonicity*
of §10.4. With it, agreement and safety follow the §5.5 shape:

```lean
theorem decided_unique (h₁ : Decided U V₁ k v₁) :
    ∀ V₂ v₂, Decided U V₂ k v₂ → v₁ = v₂

theorem safety (h₁ : Decided U V₁ k (some L₁))
    (h₂ : Decided U V₂ k (some L₂)) : L₁ = L₂
```

The induction closes case by case: the direct/direct diagonal by O1 and
O1′; every direct/indirect crossing by O2, O3 and O4′; and the
indirect/indirect case by the anchor trichotomy of §5.5, with a shared
anchor yielding a shared verdict — skip-versus-commit by the skip
constructor's universal premise, commit-versus-commit by canonicity.

### 10.4 The finding: agreement needs a canonical candidate

The published agreement proof (its Lemma 5) handles the indirect/indirect
case by arguing that both validators use the same anchor and that "the
indirect decision rule solely depends on the causal history of the anchor".
That is true of the *test* — but the rule must also **choose a candidate**,
and nothing in the quorum arithmetic prevents two equivocating candidates
from both passing the test at one anchor. The counting that would be needed
— two `(n−3f)`-sized in-cone supporter sets overlapping in more than the
`f` equivocators — requires `2(n−3f) − f > n`, that is `n > 7f`, which
**fails** at `n = 5f+1`. The configuration is moreover realisable: on a
valid six-validator universe, a Byzantine leader's two round-0 twins each
gather exactly three supporters (disjoint correct pairs plus the
equivocator's own split), and a round-3 block sees all of round 1 — **both
twins pass `ThickLink` against it**, by `decide` (`utwin6_both_pass`, §11).
An indirect rule that commits "some passing candidate" therefore admits
derivations committing either twin: agreement is *refutable*.

What arbitrates in practice is the iteration order of the implementation's
candidate loop — every honest node examines candidates in the same,
unspecified but deterministic, order. The formalized rule states that
determinism as mathematics: commit the least passing candidate in a fixed
linear order on block identifiers (block hash, in an implementation). Under
that premise agreement is a theorem; without it, false. The premise is
consumed *exactly* where the published argument is silent — O4′ shows a
directly committed block is the unique candidate passing the test anywhere,
so every other pairing closes by counting, and canonicity arbitrates only
the indirect-versus-indirect, shared-anchor, equivocating-leader corner.

For implementers: **the candidate-iteration order of the indirect rule is
consensus-critical**. Two honest nodes iterating in different orders (for
instance, arrival order) can commit different blocks for one slot at
`n = 5f+1`; any fixed shared order restores agreement, and "first seen"
does not. The remaining findings are recorded in the design document: a
missing lemma (O4′, assumed silently by the published case analysis), the
blocks-versus-authors ambiguity in the indirect test (only the author count
is provable), and the exact-complement subtlety in the published Lemma 2
(§10.2, O2).

### 10.5 Liveness, one round shorter

Liveness follows the §6 development with every hypothesis one round
shorter — the protocol's latency advantage made visible as proof
structure:

* **O7.** Post-`R`, a correct-led slot commits *directly* from **two**
  populated rounds and one synchronised step
  (`Odontoceti.decided_of_leader_mem`): coverage makes every correct
  decision-round block reference the leader's block, and `Correct` carries
  a quorum. The §6.6 analogue needed three populated rounds.
* **O8.** Under a pipelined identity-round schedule, a run of **two**
  consecutive committed slots spans eligibility for everything below
  (`spansEligible_two`): a slot cannot anchor on the round immediately
  above it, but the second slot of the run clears `slotRound + 2`. Two
  consecutive correct leaders is the published Lemma 10, now visible as
  arithmetic.
* **O9.** A committed run of eligible span clears every slot below it
  (`Odontoceti.decided_below_of_committed_run`), by the
  nearest-eligible-committed-anchor induction of §6.6, with the indirect
  commit taking the minimum of the passing candidates — the constructive
  face of the canonicity premise.
* **O10.** The composition, under enforceable hypotheses only:

```lean
theorem all_decided_below_of_fairRun (hc : 0 < c) (hT : T ⊆ Correct)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hspan : SpansEligible Validator c) (fair : FairRunOn T c) (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ U D N, Live U D N → DeliversQuorum D → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v
```

Note the horizon: the run's last slot needs rounds up to `slotRound + 1` —
one round of certificates fewer than the §6 analogue, again the two-round
structure showing through.

---

## 11. Satisfiability

Every structure carrying conditions is exhibited satisfiable by a concrete model
over four validators at `f = 1`. This is a substantive component of the
development rather than a testing exercise: an unsatisfiable hypothesis renders
every theorem above it vacuous, and vacuity is not otherwise detectable.

| Model | Satisfies |
|:---|:---|
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
at `f = 1`, since `|Correct| = 3 = n−f` exactly, so that every correct validator
is required for a quorum and none may lag. Such a model requires `f ≥ 2`. This is
the combined fault budget of §4.2 appearing as a concrete obstruction rather than
as an inequality.

The conditions of §§7–10 are witnessed in the same style, at their own
boundary instances: chain quality on `Ucens` — the one model that is
simultaneously CQ1's tightness witness (`missingAt = {3}` at every layer
of the committed cone, exactly `f`) and the censorship exhibit
(`Synchronised` fails at every round while the commit stands); `DoSValid` satisfiable and biting (`Uexcl`, with the exclusion
chain and a commit after it), the budget satisfiable at its sharp constant
(`UniformBudget Dtwin 3` with `ByzBudget Dtwin 0`), the horizon computed and
its statute of limitations exhibited (`chop Uexcl 2`, `chop Umerge 1`), the
attested base sandwich tight at the bottom (`Base Utwin 1 0 = {1,2,3}`), and
every Odontoceti rule and all four `Decided` constructors at `n = 6, f = 1`
(`Uodo`, `Uskip`, `Utwin6`), including the two-twin configuration that
motivates the canonicity premise (`utwin6_both_pass`).

---

## 12. Mechanisation

The development comprises approximately 15,700 lines of Lean 4 (v4.32.2)
against Mathlib, of which some 10,900 constitute the library and 4,800 the
models of §11 and the witness files of the arcs. A full build reports no
errors.

**Axiom audit.** Every principal result — among them
`reaches_of_quorum_support`, `exists_common_correct_ancestor`,
`decided_agree`, `commitSeq_agree`, `outputAt_agree`, `no_stall`,
`commits_recur_on`, `exists_synchronisedOn_of_backoff`,
`all_decided_below_of_fairRun`, `card_history_le'`, `dos_resistance`,
`decided_chop`, `decided_agree_chop`, `card_retained_le`, `bootstrap_agree`,
`chop_chop`, `Odontoceti.decided_unique`, `Odontoceti.safety` and
`Odontoceti.all_decided_below_of_fairRun`, `chain_quality` and
`committed_of_correct_block` — depends on exactly `propext`,
`Classical.choice` and `Quot.sound`, which constitute the whole axiom set of
Lean 4. No result depends on `sorryAx`, on any bespoke axiom, or on
`native_decide` and the extended trusted base it entails.

**The core.**

| Module | Contents |
|:---|:---|
| `Validators.lean` | the fault model (`n ≥ 3f+1`); T0 |
| `Block.lean` | `Block`, `ValidWrt`; T0′ |
| `BlockDag.lean` | `BlockUniverse`, `View`; T1 |
| `CausalHistory.lean` | `Reaches`; T2, T6a |
| `Support.lean` | counting vocabulary; the hitting, propagation and coverage lemmas |
| `History.lean` | causal history as a `Finset` |
| `Persistence.lean` | T3 |
| `CommonCore.lean` | T3a, T3c |
| `Mysticeti.lean` | the commit rule; eligibility; M1–M6; the ledger |
| `Schedule.lean` | concrete schedules (`uniform`, `uniformSingle`); conservativity |
| `Liveness.lean` | L0–L6, L7a; the committed-run results |
| `Timing.lean` | L7b |
| `ViewSync.lean` | L7c: view convergence, the reduction to `Timing`, the factoring of the bound, and the untimed variant |
| `Quantitative.lean` | L8, L9 |

**The arcs** (§§8–10), each consuming the core read-only:

| Module | Contents |
|:---|:---|
| `DoS/Exposure.lean` | `ExposedIn`, `DoSValid`; exposure ≤ `f` per cone |
| `DoS/Acceptance.lean`, `DoS/Counting.lean` | the acceptance rule; view size from history size |
| `DoS/SelfParent.lean`, `DoS/Adoption.lean`, `DoS/Pedigree.lean` | the adoption collapse; pedigrees; the general per-cone bound |
| `DoS/Density.lean` | histories are almost all of the correct past |
| `DoS/Novelty.lean` | the novelty budget; the budget sandwich; `dos_resistance` |
| `DoS/Composition.lean` | the two conditions composed; the pool freezes |
| `DoS/Exclusion.lean` | liveness survives exclusion; the correct backbone |
| `GC/Chop.lean` | the horizon operator; per-slot verdict invariance |
| `GC/ChopDecided.lean` | the induced schedule; `decided_chop`, `decided_agree_chop` |
| `GC/Window.lean` | windowed novelty and stores; `card_retained_le` |
| `GC/AttestedBase.lean` | the inexact certificate, sandwiched |
| `GC/Bootstrap.lean` | window completeness; the joiner's view; `bootstrap_agree` |
| `GC/Horizon.lean` | `chop_chop`; heterogeneous-horizon agreement; the depth rule |
| `Odontoceti/Rules.lean` | the two-round rules; the arithmetic core O1–O4′ |
| `Odontoceti/Decision.lean` | the decision relation with canonicity; agreement |
| `Odontoceti/Liveness.lean` | O7–O10 |
| `Quality/Coverage.lean` | `coveredAt`; per-commit and ledger coverage (CQ1–CQ3) |
| `Quality/Inclusion.lean` | post-`R` inclusion (CQ5, CQ6) |
| `Quality/Capstone.lean` | the windowed bounds and `chain_quality` (CQ7) |
| `LeanDagTest/` | the models of §11 and the witness files of every arc |

**The support graph, extracted.** The dependency structure of the
development is not documented by hand: `scripts/DepGraph.lean` walks
`Environment.constants` and records, for every declaration, the constants
appearing in its type **and in its body** — for a theorem, that body is
the proof term, so the edges are the real proof structure rather than the
statement's signature. `scripts/depgraph.py` then takes its node set from
Appendix A of this report, contracts paths running through unlabelled
lemmas, takes the transitive reduction, and renders the result. The full
graph is ≈900 declarations and ≈7,700 edges; the two views drawn here are
the §6.10 figure and the one below.

Two extraction details are worth recording for anyone repeating the
exercise. `ConstantInfo.value?` returns `none` for *imported* theorems in
this Lean version — proofs are loaded lazily — so the proof term must be
reached by matching `.thmInfo` explicitly; without that, only
statement-level dependencies appear and the graph looks almost empty.
And private declarations and compiler-generated auxiliaries must be kept
as pass-through nodes, since a labelled result frequently reaches another
only through one of them. Mathlib and core constants *are* dropped, and
safely: they never mention a constant of this development, so no path
between two of its results can run through them.

![**The whole development.** The same extraction over every principal result, including the four arcs. Reading the columns: the core account occupies the left half, and each arc attaches to it at the results it consumes rather than at the top — the garbage-collection operator (G1) sits beside the structural theorems it re-uses, and Odontoceti's counting core (O1–O4′) is independent of Mysticeti's, converging only at its own agreement theorem. Lean names are omitted for legibility; the full-detail rendering is in `docs/depgraph/`.](depgraph/support-full-compact.svg)

The extracted edges are also an independent check on this report's prose,
and three of its claims come out exactly as written. `P3′`, the
self-parent clause, has no outgoing edge in the core view and in the full
view feeds only C1′, C3′, G1, G9 and G11 — which is §2.2's assertion that
safety and liveness never consume it and that it is load-bearing for the
denial-of-service and garbage-collection arcs. `L7a ← N2a, P7` and
`L7b ← N2b, P9, T1` reproduce the §4.4 table row for row, the extra `T1`
on the timing route being the non-equivocation step that identifies a
validator's block with the one the timing structure names. And
`O5 ← O1, O1′, O2, O3, O4′` confirms that Odontoceti's agreement rests on
exactly the four counting theorems plus twin uniqueness (§10.3), with
`O4′` — the lemma the published argument lacks — visibly load-bearing.

Seven design records accompany the development: `spec.md` (safety),
`liveness.md` (liveness), `pipelining-and-multi-leader.md` (the schedule
generalisation), `chain-quality.md` (§7), `dos-equivocation-and-growth.md`
(§8), `garbage.md`
(§9) and `odontoceti.md` (§10), with `related.md` surveying the
surrounding literature. These carry the design rationale and the log of
settled and open questions. The report draws its statements from the source.

---

## 13. Discussion

The first four subsections concern the core account's central design
choice — where the synchrony assumption lives; §13.5 draws the lessons of
the three extensions; §13.6 records what remains open.

### 13.1 Locating the synchrony assumption

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
it holds `n−f = 3` blocks of the round below, and suppose `A`, `B` and `C` are
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

The example is often read as showing that a view-shaped assumption is
*inadequate*. That reading is too strong, and §6.9 corrects it: view
convergence is adequate but **incomplete** — it is the network half of a
two-part derivation whose other half is a protocol clause, and both
halves are now proved. What the counterexample really shows is that the
missing half cannot be supplied by strengthening the network, since the
network is already as strong as it can be (delivery is instantaneous
there). The gap is a *race* between arrival and building, and only the
builder's own schedule can win it.

**The threshold the specification must meet is `D₀ + Δ`, not Δ.** This is the
one point at which a network parameter enters the protocol's constant, and it is
the substantive quantitative result (§6.11). Validators enter a round at
different times, so a wait must accommodate the propagation bound *and* the
spread between validators; taking the spread at round `0`, where it records how
nearly simultaneously the validators started, and propagating it forward by
`driftFrom_of_prompt`, gives the bound. Under a common start, `D₀ ≤ Δ` and the
threshold is `2Δ`.

Because Δ is not known to an implementation, no constant can be fixed in
advance. A backoff is the specification's response — a search for a sufficient
constant, written into the algorithm — and its only relevant property is that
the search terminates (§13.2).

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

### 13.2 Why coverage is derived rather than specified

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
onwards — with no condition on shape, rate, or driving signal. §6.11 carries this
to its conclusion: with Δ known, a constant timeout of `D₀ + Δ` suffices and the
loop disappears.

### 13.3 Consequences of the abstraction

1. The consensus argument is purely combinatorial, involving round indices and
   finite-set cardinalities. Under a message-level assumption every statement
   would carry instants.
2. The temporal content is confined to a single module and consumed through a
   single definition.
3. The condition admits two independent derivations (§6.7, §6.8) and a third,
   quantitative route (§6.11), against an unchanged statement.
4. The condition composes with the safety development, mentioning only `U.ids`,
   `U.block` and `refs` — the vocabulary that development already employs.

### 13.4 Costs

Δ does not appear above the interface. Introducing it would require views indexed
by an instant and every statement quantified over instants, for no proof content.
The quantitative statements recover what is needed *below* the interface without
propagating time upward.

Coverage being derived rather than assumed does not make it unconditional. The
derivation rests on N2, and in the absence of a time model the chain must
terminate at a delivery assumption; what the reformulation achieves is to place
that assumption where it belongs — on the network — and to keep it out of every
statement above.

### 13.5 Lessons from the extensions

Three lessons generalise beyond the particular arcs.

**Additivity is a measurement of abstraction.** Each extension was carried
out without modifying a line of the core: the DoS arc consumed the delivery
layer and the self-parent clause as found; garbage collection consumed every
theorem verbatim because `chop U G` was arranged to *be* a `BlockUniverse`;
Odontoceti consumed the whole DAG layer because its quorums are the `n − f`
the development is parameterised by. When an abstraction is placed
correctly, new developments read like instantiations; when it is misplaced,
they read like refactors. The one refactor resisted — a rule-parameterised
decision relation shared between §3.5 and §10.3 — is the price of the
discipline, and it was paid twice in mirrored proofs rather than once in
core churn.

**Enforceability is a specification discipline.** The DoS headline
(`dos_resistance`) quotes only conduct a validator can execute — an
author-blind budget, a reference rule — and no condition that consults an
identity oracle; the cost of author-blindness is a factor of `f` in a
constant, never a theorem. The same discipline shapes §9: horizons are set
by local rules, the attested base replaces agreement with `f+1` sampling,
and every hypothesis of the bootstrap theorems is checkable by the party it
binds. Conditions of this shape survive contact with implementations;
conditions that quantify over `Correct` do not.

**Mechanisation earns its keep at the equivocation corners.** All four §10
findings — the canonicity gap, the missing uniqueness lemma, the
blocks-versus-authors ambiguity, the exact-complement subtlety — live where
an equivocating author interacts with a counting argument, precisely the
territory that uncertified DAGs annexed when they discarded certificates,
and precisely where hand proofs compress the most. The counterexample
behind the canonicity gap fits in six validators and twenty-five blocks;
what was needed to find it was not scale but the obligation to state the
indirect rule precisely enough to fail to prove it.

### 13.6 Limitations

The quantitative bounds are established (§6.11). The following remain open.

**The backoff loop.** `Rated` and the threshold of R4 are stipulated as clauses
of the specification; no realistic adaptive scheme is shown to satisfy them, and
the feedback mechanism of §13.2 is not modelled. Moreover
`Timing.timeout : ℕ → ℕ` is indexed by round and common to the reliable set, so
that a per-validator backoff — in which validators increase their timeouts at
different moments — cannot be expressed, let alone shown to converge. This
requires a refinement of `Timing`.

**Wall-clock latency.** `Delay(Δ)` is a duration, but the total elapsed time to a
commit is not derived: converting a bound of the form "`3k + 8` rounds, each of
at least `2Δ`" into elapsed time requires a lemma accumulating `prompt` across
rounds, which is not present. `Timing.le_built` relates rounds to time in one
direction only.

**Byzantine leaders.** §6.11 bounds the wait until the next reliable leader,
which sidesteps rather than answers the question of how distant an indirect
anchor may be when the leader is Byzantine.

**Leader predictability.** `Slots.leader` is an arbitrary function, so nothing
distinguishes a schedule an adversary can predict from one it cannot, and
targeted denial of service against a known future leader — the network sense,
distinct from the storage-exhaustion sense §8 bounds — is invisible to the
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
is identifiable. Density (L0) yields `n−f` distinct authors at round `r+1`
whenever the DAG reaches above it, hence `f+1` *correct* authors, and coverage
makes each of their blocks reference the leader — so `f+1` correct **supporters**
is within reach from L0 and `SynchronisedOn` alone, with neither `Populated` nor
P8. A certificate, however, requires `n−f` distinct supporters, and
`SynchronisedOn` is honest-to-honest (§6.6), so the remaining `f` cannot be
obtained; reaching `n−f` supporters requires `n−f` correct authors at `r+1`,
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

## 14. Related work

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

**Chain quality and fairness.** The chain-quality property originates
with the Bitcoin backbone analysis of Garay, Kiayias and Leonardos
[GKL15] — the fraction of honest blocks in any window of the chain —
and fairness claims for DAG protocols go back to Hashgraph [Bai16],
whose "fair ordering" was informal. The order-fairness line (Kelkar,
Zhang, Goldfeder, Juels [KZGJ20]) concerns transaction *ordering*
rather than inclusion and is orthogonal to §7's guarantees. The §7
statements differ from the backbone form in the direction the DAG makes
natural: coverage is per-flush and unconditional (a commit carries a
quorum-forced sample of every round below it), and inclusion is
individual and quantitative once synchrony holds — with a
counterexample separating the two, which the author has not seen stated
for this protocol family.

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
bounded time" not being expressible in this vocabulary (§13.6).

---

## 15. Conclusion

This report has given a machine-checked account of uncertified DAG consensus
organised around one idea: state the liveness condition on the object the
protocol actually builds. Eventual DAG synchrony — beyond some round, every
correct block references every correct block of the round below — is a
sentence about a graph, and above it the entire consensus argument is finite
combinatorics: safety with no network assumption at all, liveness with no
mention of time, and the temporal content of partial synchrony confined to a
single module that *derives* the structural condition twice over.

The same foundation then carried three developments it was not designed for,
essentially unchanged — which is the strongest evidence the abstraction is
placed correctly. The denial-of-service account reused the delivery layer and
the self-parent clause; garbage collection reused every theorem verbatim on
the truncated universe, because truncation was arranged to be a universe; and
Odontoceti reused the entire DAG layer because its quorums turned out to be
the `n − f` the development was already parameterised by. Each arc also
returned something to the trust story: enforceable storage bounds, horizons
without consensus, and — in the one place the formalization diverged from a
published argument by necessity — the observation that Odontoceti's
agreement rests on a canonical candidate order that its paper never states.

What remains open is catalogued in §13.6: the backoff dynamics, wall-clock
latency, block-level total order, and liveness below the growth clause.
Beyond those, two directions suggest themselves. The commit-free,
evidence-based horizon rule sketched in the garbage-collection design record
would extend pruning into asynchrony; and the decision relation, now
instantiated twice at different wavelengths with near-identical agreement
proofs, invites a rule-parameterised treatment — resisted here to keep each
development additive, but natural the third time a commit rule arrives.

---

## References

- [Aru+25] B. Arun, Z. Li, F. Suri-Payer, S. Das, A. Spiegelman. *Shoal++: High Throughput DAG BFT Can Be Fast and Robust!* NSDI 2025. arXiv:2405.20488.
- [Bab+25] K. Babel, A. Chursin, G. Danezis, A. Kichidis, L. Kokoris-Kogias, A. Koshy, A. Sonnino, M. Tian. *Mysticeti: Reaching the Limits of Latency with Uncertified DAGs.* NDSS 2025. arXiv:2310.14821.
- [Bai16] L. Baird. *The Swirlds Hashgraph Consensus Algorithm.* Swirlds Tech Report SWIRLDS-TR-2016-01, 2016.
- [Ber+24] N. Bertrand, P. Ghorpade, S. Rubin, B. Scholz, P. Subotic. *Reusable Formal Verification of DAG-based Consensus Protocols.* arXiv:2407.02167.
- [DH18] G. Danezis, D. Hrycyszyn. *Blockmania: from Block DAGs to Consensus.* arXiv:1809.01620.
- [DKSS22] G. Danezis, L. Kokoris-Kogias, A. Sonnino, A. Spiegelman. *Narwhal and Tusk: a DAG-based Mempool and Efficient BFT Consensus.* EuroSys 2022.
- [DLS88] C. Dwork, N. Lynch, L. Stockmeyer. *Consensus in the Presence of Partial Synchrony.* JACM 35(2), 1988.
- [GKL15] J. Garay, A. Kiayias, N. Leonardos. *The Bitcoin Backbone Protocol: Analysis and Applications.* EUROCRYPT 2015.
- [Jov+24] P. Jovanovic, L. Kokoris-Kogias, B. Kumara, A. Sonnino, P. Tennage, I. Zablotchi. *Mahi-Mahi: Low-Latency Asynchronous BFT DAG-Based Consensus.* arXiv:2410.08670.
- [KZGJ20] M. Kelkar, F. Zhang, S. Goldfeder, A. Juels. *Order-Fairness for Byzantine Consensus.* CRYPTO 2020.
- [KNPS23] I. Keidar, O. Naor, O. Poupko, E. Shapiro. *Cordial Miners: Fast and Efficient Consensus for Every Eventuality.* DISC 2023, LIPIcs 281.
- [PMV25] N. Polyanskii, S. Mueller, I. Vorobyev. *Making Uncertified DAG BFT Provably Live with Linear Payload and Quadratic Metadata Communication* (Starfish). IACR ePrint 2025/567.
- [PVM26] N. Polyanskii, I. Vorobyev, S. Mueller. *Bluestreak: Scaling DAG BFT by Sparsifying Metadata.* IACR ePrint 2026/898.
- [QXS25] L. Qiu, J. Xiao, J.-Y. Shin, Z. Shao. *LiDO-DAG: A Framework for Verifying Safety and Liveness of DAG-Based Consensus Protocols.* PACMPL 9(PLDI), Article 203, 2025. doi:10.1145/3729306.
- [QXS26] L. Qiu, J. Xiao, Z. Shao. *Mechanized Safety and Liveness Proofs for the Mysticeti Consensus Protocol under the LiDO-DAG Framework.* IEEE S&P 2026, 149–168.
- [SGSK22] A. Spiegelman, N. Giridharan, A. Sonnino, L. Kokoris-Kogias. *Bullshark: DAG BFT Protocols Made Practical.* CCS 2022.
- [SSKN25] N. Shrestha, R. Shrothrium, A. Kate, K. Nayak. *Sailfish: Towards Improving the Latency of DAG-based BFT.* IEEE S&P 2025. ePrint 2024/472.
- [Van25] P. Vander Vos. *Odontoceti: Ultra-Fast DAG Consensus with Two Round Commitment.* MSc thesis, arXiv:2510.01216.

---

## Appendix A. Statement index

Principal results only; supporting lemmas are omitted.

### Safety

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| T0 | two quorums share a correct validator | `exists_correct_mem_inter` *(Validators)* |
| T0′ | two quorum-backed identifier sets share a correct author | `exists_correct_mem_creators_inter` *(Block)* |
| T1 | non-equivocation, in usable form | `BlockUniverse.eq_of_creator_eq` *(BlockDag)* |
| — | two quorum-backed sets of round-`n` blocks share a block | `BlockUniverse.exists_common_mem_of_quorums` *(BlockDag)* |
| T2 | causal history is non-increasing in round | `round_le_of_reaches` *(CausalHistory)* |
| T6a | causal history does not escape a view | `View.mem_of_reaches`, `View.exists_reaches_iff` *(CausalHistory)* |
| T3 | persistence | `reaches_of_quorum_support` *(Persistence)* |
| T3a | correct-support counting | `exists_correct_common_support` *(CommonCore)* |
| T3c | a common correct ancestor | `exists_common_correct_ancestor` *(CommonCore)* |
| M1 | no block is both committed and skipped | `not_directCommit_of_directSkip` *(Mysticeti)* |
| M2 | a committed block's certificate is unavoidable from `r+3` | `exists_certificate_reaches_of_directCommit` *(Mysticeti)* |
| M3 | a skipped block has no certificate anywhere | `certificates_eq_empty_of_directSkip` *(Mysticeti)* |
| M4 | the indirect rule agrees with the direct | `indirect_agrees_with_direct`, `certifiedIn_iff_of_view` *(Mysticeti)* |
| M5′ | certificate uniqueness | `eq_of_certificates_nonempty` *(Mysticeti)* |
| M5 | at most one block per slot is directly committed | `eq_of_directCommit_of_creator_eq` *(Mysticeti)* |
| M6 | agreement | `decided_unique`, `decided_agree` *(Mysticeti)* |
| — | corollaries of agreement | `eq_of_decided_commit`, `not_decided_skip_of_decided_commit` *(Mysticeti)* |
| — | the committed-leader sequence is agreed | `commitSeq_agree` *(Mysticeti)* |
| — | the ledger is monotone and agreed | `ledgerSet_mono`, `ledgerSet_agree` *(Mysticeti)* |
| — | a block enters at one slot, agreed | `outputAt_unique`, `outputAt_agree` *(Mysticeti)* |

### Liveness

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| L0 | the DAG is dense below its frontier | `card_authorsAt_of_lt` *(Liveness)* |
| L1 | no stall | `no_stall` *(Liveness)* |
| L2 | decisions are monotone in the view | `decided_mono` *(Liveness)* |
| L3 | decisions propagate to the full view | `decided_full` *(Liveness)* |
| L4 | a correct leader is committed | `directCommit_of_leader_mem`, `decided_of_leader_mem` *(Liveness)* |
| — | at `T := Correct` | `directCommit_of_correct_leader`, `decided_of_correct_leader` *(Liveness)* |
| L5 | an absent leader is skipped | `decided_none_of_leader_absent` *(Liveness)* |
| L6 | commits recur | `commits_recur_on`, `commits_recur` *(Liveness)* |
| — | a slot resolves through its first eligible commit | `decided_of_first_eligible_commit` *(Liveness)* |
| — | a committed slot above decides everything below (spaced schedules) | `decided_of_committed_above`, `all_decided_below_of_spacing` *(Liveness)* |
| — | a committed run of eligible span clears everything below | `decided_below_of_committed_run` *(Liveness)* |
| — | every slot below a fair run is decided (pipelined) | `all_decided_below_of_fairRun` *(Liveness)* |
| L7a | coverage from delivery | `synchronised_of_delivery` *(Liveness)* |
| L7b | coverage from GST | `Timing.synchronisedOn_of_timing`, `exists_synchronisedOn_of_backoff` *(Timing)* |
| L7c | coverage from view convergence | `ViewSync.synchronisedOn_of_converges` *(ViewSync)* |
| — | the referencing clause, unfused from the network's | `ViewSync.covers_of_converges` *(ViewSync)* |
| — | the timing route derived from the view-level one | `ViewSync.toTiming` *(ViewSync)* |
| — | build-time views agree | `ViewSync.ViewsAgree`, `ViewSync.viewsAgree_of_converges` *(ViewSync)* |
| — | the bound factored out of convergence | `convergesWithin_iff_bounded` *(ViewSync)* |
| — | production from untimed view convergence, without N1 | `ViewsConverge`, `populated_of_viewsConverge` *(ViewSync)* |
| — | liveness on the view-convergence foundation | `ViewSync.commits_recur_of_converges`, `ViewSync.all_decided_below_of_converges` *(ViewSync)* |
| — | drift is derived | `Timing.driftFrom_of_prompt` *(Timing)* |
| L8a | the round of coverage, explicitly | `synchronisedOn_of_rate` *(Quantitative)* |
| L8b | the committing slot, and its round | `commits_recur_within`, `commits_recur_by_round` *(Quantitative)* |
| L9 | the wait bound | `directCommit_of_wait`, `decided_of_wait`, `directCommit_of_wait_two_delay` *(Quantitative)* |

### Chain quality (§7)

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| CQ1 | a commit covers all but at most `f` correct authors, per round | `card_coveredAt_ge_of_decided` *(Quality/Coverage)* |
| CQ2 | at least half of the correct validators, per round | `card_correct_le_two_mul_coveredAt_of_decided` *(Quality/Coverage)* |
| CQ3 | ledger coverage, cumulative | `ledger_coverage` *(Quality/Coverage)* |
| CQ5 | post-`R`, every correct block is in every later correct-led commit | `mem_history_of_decided_commit` *(Quality/Inclusion)* |
| CQ6 | every correct block enters the agreed ledger | `committed_of_correct_block` *(Quality/Inclusion)* |
| CQ7 | within a schedule window; the capstone | `committed_of_correct_block_within`, `committed_of_correct_block_by_round`, `chain_quality` *(Quality/Capstone)* |
| — | the censorship boundary, on data | `Ucens` witnesses *(LeanDagTest/Quality/Model)* |

### Denial of service (§8)

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| D11–D13 | exposure, and the DoS condition | `ExposedIn`, `DoSValid` *(DoS/Exposure)* |
| C2 | at most `f` authors exposed per cone | `card_exposedTo_le` *(DoS/Exposure)* |
| D14 | safety and the DoS condition do not interact | witness file *(LeanDagTest/DoS/SafetyUnderDoS)* |
| D15a | at zero margin, references are exactly the correct validators | `creators_refs_eq_correct` *(DoS/Exclusion)* |
| — | the correct backbone | `mem_history_of_correct` *(DoS/Exclusion)* |
| C1′ | the general per-cone bound | `card_history_le'` *(DoS/Pedigree)* |
| D25 | density: cones miss at most `f` per layer | `card_missingAt_le` *(DoS/Density)* |
| — | the doubling construction (`2^(e−2)`) | `Udouble` witnesses *(LeanDagTest/DoS/Doubling)* |
| — | the telescope | `card_history_le_of_stepNovelty` *(DoS/Novelty)* |
| C3′ | the view gap is a constant, not a drift | `card_viewGap_succ_le` *(DoS/Novelty)* |
| — | the budget sandwich | `UniformBudget.byzBudget`, `uniform_of_byzBudget` *(DoS/Novelty)* |
| B4 | linear storage under the budget | `card_viewUpto_le` *(DoS/Novelty)* |
| B | the capstone, enforceable conditions only | `dos_resistance`, `dos_resistance'` *(DoS/Novelty)* |
| B5 | after exposure completes, the pool freezes | `card_viewUpto_le_of_allExposed'` *(DoS/Composition)* |

### Garbage collection (§9)

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| G1 | truncation is a universe; the DoS condition crosses one way | `chop`, `dosValid_chop` *(GC/Chop)* |
| G2 | per-slot verdict invariance | `certificates_chop`, `directCommit_chop`, `certifiedIn_chop`, … *(GC/Chop)* |
| G3 | the decision relation survives the cut | `decided_chop` *(GC/ChopDecided)* |
| G4 | cross-cut agreement, arbitrary joiner views | `decided_agree_chop` *(GC/ChopDecided)* |
| G5 | liveness transfers | `live_chopD`, `populated_chop` *(GC/Window)* |
| G13, G14 | windowed novelty; store correspondence | `novelty_chop_anti`, `viewUpto_chopD` *(GC/Window)* |
| G6 | storage constant at lag `Λ` | `card_retained_le` *(GC/Window)* |
| G6b, G7 | join and relay at the same constant | `card_joinIds_le`, `card_serve_le` *(GC/Bootstrap)* |
| G10 | the attested-base sandwich | `correct_mem_base`, `exists_correct_attester_of_mem_base` *(GC/AttestedBase)* |
| G11 | window completeness, tight at lag two | `accepted_mem_base` *(GC/Bootstrap)* |
| G12 | bootstrap safety | `joinView`, `bootstrap_agree` *(GC/Bootstrap)* |
| G8 | horizons compose; heterogeneous horizons agree | `chop_chop`, `decided_agree_horizons` *(GC/Horizon)* |
| G9 | possession universalises in one round | `viewUpto_subset_viewUpto_succ`, `pruned_subset_peer_store` *(GC/Horizon)* |

### Odontoceti (§10)

| Label | Statement | Lean *(module)* |
|:---|:---|:---|
| O1 | commit versus skip | `not_directSkip_of_directCommit` *(Odontoceti/Rules)* |
| O1′ | twin uniqueness for direct commits | `eq_of_directCommit` *(Odontoceti/Rules)* |
| O2 | a skipped leader fails the indirect test everywhere | `card_supporters_le_of_directSkip`, `not_thickLink_of_directSkip` *(Odontoceti/Rules)* |
| O3 | support propagation: every anchor's cone is the certificate | `thickLink_of_directCommit` *(Odontoceti/Rules)* |
| O4′ | a direct commit excludes every rival candidate | `eq_of_directCommit_of_thickLink` *(Odontoceti/Rules)* |
| O5 | agreement, under canonicity | `Odontoceti.decided_unique` *(Odontoceti/Decision)* |
| O6 | safety | `Odontoceti.safety` *(Odontoceti/Decision)* |
| O7 | a correct leader commits in one step | `Odontoceti.decided_of_leader_mem` *(Odontoceti/Liveness)* |
| O8 | a run of two spans eligibility | `Odontoceti.spansEligible_two` *(Odontoceti/Liveness)* |
| O9 | a committed run clears everything below | `Odontoceti.decided_below_of_committed_run` *(Odontoceti/Liveness)* |
| O10 | liveness | `Odontoceti.all_decided_below_of_fairRun` *(Odontoceti/Liveness)* |
| — | the thesis gap, on data | `utwin6_both_pass` *(LeanDagTest/Odontoceti/Model)* |
