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
rather than assumed, and the whole of what the network must supply reduces to
a single clause of **view convergence** — after stabilisation, whatever one
correct validator holds reaches every correct validator within Δ — from which
both coverage and block production follow by the protocol's own build rules.
The quantitative form states that a correct leader is committed once correct
validators wait `2Δ`.

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

The development comprises roughly 17,400 lines of Lean 4 over Mathlib. Every
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
   rather than a set of alternatives: the third derives the second, and states the
   network's contribution in a form containing no clause about what
   validators do. On the same foundation, production is derived too —
   untimed from round `0` (`populated_of_viewsConverge`), and timed from
   the GST crossing (`ViewGrowth.populatedOn`) — so the entire liveness
   account rests on one view-shaped assumption. The quorum-based
   alternative N1 is retained in a module nothing else imports
   (`Network/Quorum.lean`).

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
  companion document. A Cordial-Miners-like three-round spacing is the
  special case in which every later slot is eligible
  (`eligible_of_lt_of_spacing`).
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
ledger) and §6 liveness, grounded on view convergence (culminating in
recurring commits, `commits_recur_on`, the three derivations of eventual
DAG synchrony, and the quantitative wait bound). §7 proves the chain-quality account — coverage
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
records that the correct validators themselves form a quorum. The liveness
development consumes it wherever a `T`-relative result is specialised to
`T := Correct`, and in the production inductions of §6.3 and §6.9.

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

Four aspects of the formulation are consequential.

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
consume it; it is indispensable to §8, where the self-parent
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
the companion documents and the source comments; Appendix A maps each to its Lean
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
`Slots.uniformSingle`), though a backlog of undecided slots is
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
P3′ by neither — it is indispensable to §8.

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
`|Correct| = 3 = n−f` exactly, so no margin exists and every correct validator
must be timely; margin appears only when fewer than `f` validators are in fact
faulty, and the `T`-parameterised statements make it available automatically.
The specialisations at `T := Correct` (`directCommit_of_correct_leader`,
`decided_of_correct_leader`, `commits_recur`) recover the conventional
statements.

### 4.3 The network

The development asks the environment for two *things*, and each admits
several *formulations*. Keeping those apart is what this section is for:
the roles are fixed, the formulations are a modelling choice, and two of
the formulations are not as pure as their names suggest.

| Role | What is wanted | Formulations |
|:---|:---|:---|
| **Production** | what exists is eventually obtained, so the DAG keeps growing | N1 (`DeliversQuorum`); or view convergence, untimed (`ViewsConverge`) or timed (`converges`, from GST on) |
| **Coverage** | after stabilisation, delivery is prompt enough that blocks reference one another | N2, in three forms: `converges` (views), `Timing.covers` (references), `EventuallyDelivers` (holdings) |

Safety (§5) uses **none** of them: it holds under arbitrary asynchrony,
arbitrary loss and arbitrarily divergent views.

#### The vehicles

The formulations do not all range over the same object, and the
differences matter more than they appear to.

| Field | Indexed by | Structure |
|:---|:---|:---|
| `held v n` | the **round** `v` is building over | `Delivery` (§6.2) |
| `holds v t` | the **instant** `t` | `Timing`, `ViewSync` (§6.8–§6.9) |

`held v n` is what `v` had in hand *at the moment it built its
round-`(n+1)` block* — not what it eventually receives. That build-time
index is the essential modelling device (§13.1): a block's references are
frozen at construction, so what bears on the DAG's shape is what was held
when the builder acted. `View.ids` is a finite set of identifiers with no
index of either kind, which is why no formulation is stated over it.

#### Production

In the main line production is derived, not assumed. The liveness results
consume it as a `Populated` hypothesis, and view convergence discharges
that hypothesis twice over: `ViewGrowth.populatedOn` derives it from the
GST crossing on, and `populated_of_viewsConverge` from round `0` under
the untimed form (§6.9). The network contributes nothing to production
beyond the one convergence clause it already supplies for coverage.

There remains a third route, the development's original one, kept in
`LeanDag/Network/Quorum.lean` outside the main line: a quorum-conditional
delivery assumption from which production follows with no temporal input
at all. It is documented here because it is the weakest of the three and
the natural one to implement against, and because its shape repays study
even where it is not used.

```lean
def DeliversQuorum (D : Delivery U) : Prop :=
  ∀ n, (Fintype.card Validator - F.f) ≤ (authorsAt U n).card →
    ∀ v ∈ (Correct : Finset Validator),
      (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (D.accepted v n)).card
```

*If* a quorum of validators have produced round-`n` blocks, *then* every
correct validator accepts round-`n` blocks from a quorum of distinct
authors. Four features of the shape are deliberate.

- **Conditional: existence first, holding second.** Stated
  unconditionally it would assert that round-`n` blocks exist, which is
  what the liveness argument sets out to prove (§6.3); the assumption
  would presuppose what it is invoked to establish.
- **No clock and no round bound.** No Δ, no GST, no index past which it
  begins to hold, so it constrains the network before stabilisation
  exactly as after. This is what carries the results that do not need
  synchrony: `N1 + P8 → Populated`, through L1, with no temporal input.
- **Stated on `accepted`, not `held`.** The quorum must survive the
  acceptance filter — where a validator takes at most one block per
  author, and where the novelty budget of §8 imposes a rate limit.
- **Counting authors, not blocks** (`creatorsOf`), so an equivocator
  flooding a validator with twins contributes one (§2.5).

Two qualifications weaken the sense in which N1 is a network
assumption.

*It is not purely environmental.* Nothing obliges a validator to accept a
**Byzantine**-authored block — `accepts_correct` covers correct authors
only. With `f` Byzantine validators and `f` slow correct ones, a
validator may hold a quorum yet accept only `f+1` creators. So N1
constrains the network **and the acceptance policy** jointly, which is
the formal link to §8: `dos_resistance` takes N1 *and* the novelty
budget, and that pairing is the statement that the budget must be set
loose enough to keep N1 true.

*From `R` on it is a theorem, not an assumption.*
`card_creators_accepted_of_eventuallyDelivers` derives the accepted
quorum from N2 with `Populated`: coverage puts every correct round-`n`
block in hand, `accepts_correct` obliges acceptance, and
`|Correct| ≥ n−f`. N1's real content is therefore the pre-GST prefix —
which is precisely what it is for.

#### Coverage: N2, in three forms

The three formulations are a hierarchy, ordered here from the most
primitive; §6.9 proves the reductions.

```lean
-- over views, at instants
converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)

-- over references, at instants
covers : ∀ v ∈ T, ∀ w ∈ T, ∀ n < N, gst ≤ built w n →
  built w n + delay ≤ built v (n + 1) →
  blk w n ∈ (U.block (blk v (n + 1))).refs

-- over holdings, at the build index
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ (Correct : Finset Validator), ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ (Correct : Finset Validator) →
    a ∈ D.held v n
```

`converges` is partial synchrony as one would state it in words — *after
GST, whatever a correct validator holds reaches every correct validator
within Δ* — and mentions no block, no round and no reference. Each of the
others is obtained from it by applying a clause of the protocol:
`covers` is `converges` composed with P7 (`ViewSync.covers_of_converges`),
and `ViewSync.toTiming` exhibits a view-convergent execution as a timed
one, so the timing route is a special case rather than an alternative.

**Two of the three are impure.** `Timing.covers` concludes about `refs`,
fusing the network guarantee with the referencing clause;
`EventuallyDelivers` concludes about `held v n` — the *build-time*
index — and so presupposes that the builder waited. Only `converges`
states the network's contribution in a form containing nothing the
protocol does, and it is accordingly the primitive of the three
(§6.9).

Two further relations, both proved in §6.9. The bound factors out:
convergence within Δ is exactly eventual convergence whose lag is
uniformly bounded after GST (`convergesWithin_iff_bounded`), so *view
convergence under synchrony = view convergence + a bound*. And eventual
convergence **alone** yields nothing: an unbounded lag cannot be compared
with a timeout, so no argument places the block in the builder's hands
before it builds. The missing ingredient is not a stronger network but
the protocol's waiting rule — which is why P9 stands beside N2 in §4.1
rather than inside it.

#### What none of them says

- **Nothing about Byzantine senders.** A Byzantine validator may deliver
  to some correct validators and not others, may send equivocating blocks
  to two of them, or may publish nothing. Every formulation quantifies
  over *correct* authors only, and safety tolerates the rest
  unconditionally — a Byzantine block reaching one view and not another is
  exactly what the cross-view theorems of §5 are stated to survive.
- **Nothing about which blocks arrive**, beyond correct ones after `R`:
  N1 promises a quorum, not a particular sender's block.
- **Nothing before GST**, for N2: arbitrary delay, reordering and loss are
  permitted there, and every safety result and L1 continue to hold.

#### Where they are consumed

Neither role is discharged where its name suggests, and the extracted
support graph (§12) makes the pattern checkable rather than asserted.

**N1 lives outside the main line.** It, L1, and the four results that
exist only to serve them are collected in `LeanDag/Network/Quorum.lean`,
which nothing else in the development imports. The main line therefore
presents one network assumption — view convergence — and obtains
production from it; N1 remains available as an alternative way to
discharge the same `Populated` hypothesis, and is still the weakest of
the three, since it promises a quorum only when one already exists.

**N1 has exactly one primitive consumer: L1 (`no_stall`).** Its job is
production, not synchrony, and the results that need production take it
as a `Populated` hypothesis rather than reaching for the assumption that
supplies it. L6, the committed-run results, the quantitative results and
the capstones of
§§7–10 therefore do not mention N1 at all: any of the three production
routes may discharge them — `no_stall` from N1, `ViewGrowth.populatedOn`
from timed view convergence, or `populated_of_viewsConverge` from the
untimed form.

Of the 67 results in Appendix A, three still reach N1, and each is
*about* the combinatorial route rather than a consumer of it: L1, which
derives production from it; G5, which re-establishes it on a truncated
universe; and B, whose statement bundles growth with the storage bound
and so asserts both under the same hypotheses. The storage half of B is
independent of N1.

**N2a is derivable from view convergence.** The delivery a `ViewGrowth`
induces satisfies it — `ViewGrowth.eventuallyDelivers_toDelivery` — so the
store facts below rest on the same single network assumption as coverage
does, rather than on a second one. The derivation needs `waits` at every
round rather than only below the horizon, which is the one clause
`ViewGrowth` states more strongly than `Timing`: at round `N` the
assumption speaks of a block being in hand when its holder builds for
round `N+1`, and only a schedule that keeps honouring timeouts past `N`
orders those two events. The horizon bounds the DAG, not the clock. L7a
then follows for the induced delivery (`synchronised_toDelivery`), so all
three routes of §§6.7–6.9 are available from view convergence alone.

**N2's abstract form is used for five distinct things**, only the first
of which is coverage: L7a (§6.7); the view-gap constant C3′ and hence the
budget sandwich of §8.4; the accepted-quorum lemma above; the bound
placing the attested base inside a correct peer's retained store (G6b,
§9.3); and the one-round universalisation of possession (G9, §9.5). The
last four are facts about **stores**, where coverage is a fact about
**references**; one assumption serves both because it is stated on
`held`, upstream of the split. `Timing.covers` is consumed exactly once,
in L7b.

#### What is actually trusted

Collecting the qualifications, what the environment is trusted with is
narrower than the two-assumption summary suggests.

*For coverage*, one condition on the environment: view convergence,
bounded after GST. The other two formulations are that condition with a
protocol clause incorporated, and §6.9 derives them from it.

*For production*, one condition — but the choice of formulation is a
genuine choice. N1 is the weakest and the implementable one, though it
also constrains the acceptance policy. Untimed view convergence
(`ViewsConverge`) is stronger — every correct block, always, rather than
a quorum when one exists — and discharges N1 entirely
(`populated_of_viewsConverge`), though it is unimplementable as stated, since a validator cannot wait for "all correct blocks" without
distinguishing correct validators from crashed ones. The timed structures
take a third option and assume production outright, carrying a block per
validator per round as data (§6.10).

*And nothing else.* No condition on the environment appears in the
development beyond these two roles, in one of the formulations above; the
remaining hypotheses of §4.1 are clauses of the algorithm, which a
designer controls. Reference coverage itself — the condition all of
liveness rests on — is not a further assumption but a consequence, which
is the subject of §4.4.

### 4.4 Derived, not assumed

Eventual DAG synchrony is not an assumption of the development. It is a
property of executions, obtained from the network assumption of §4.3
together with clauses of the protocol, by any of three routes:

| Route | From | Result |
|:---|:---|:---|
| Delivery | N2 (`EventuallyDelivers`) with P7 | `synchronised_of_delivery` (L7a) |
| Timing | N2 (`Timing.covers`) with P9 | `Timing.synchronisedOn_of_timing` (L7b) |
| View convergence | N2 (`converges`) with P7 and P9 | `ViewSync.synchronisedOn_of_converges` (L7c) |

The third derives the second (`ViewSync.toTiming`, §6.9), so the routes
are a hierarchy rather than a set of alternatives; and a fourth result on the same
foundation derives *production* rather than coverage, discharging N1
(`populated_of_viewsConverge`).

It is stated as a hypothesis of L4 and L6 in order to keep those arguments free
of temporal notions (§6.10), and supplied to them by the results above. §13
discusses the formulation.

**What "derived" does and does not mean here.** Each route derives
coverage from a network assumption *together with clauses of the
protocol* — P7 on the delivery route, P9 on the timing route, both on the
view-convergence route — and each is consumed by L4 alongside
`Populated`, which comes from P8. The claim is therefore not that eventual DAG synchrony holds
in any execution of any DAG protocol; it is that it need not be *postulated*
separately, because the network assumption already standard in this literature,
combined with build rules a designer controls, entails it.

The distinction matters because the corresponding claims in the source literature
have not survived scrutiny. Mysticeti's Lemma 8 and Cordial Miners' Proposition
38 both assert that honest validators are synchronised after GST; [PMV25] reports
that both leave gaps, and [QXS26] shows the gap is not merely expositional — with
round-jumping unrestricted the conclusion is false. The present development is
not exposed to that counterexample, but the reason is P8, which excludes
round-jumping outright (§4.1). Properly read, this is the stronger position: it
identifies precisely which protocol clause the structural condition depends
on, rather than asserting the condition and leaving the price implicit.

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

### 4.6 What the adversary may do

The clauses above say what correct validators do and what the network
provides. This section states the complement: the behaviour a Byzantine
validator is permitted, which is everything not excluded above. An
implementation that defends against less than this is defending against
the wrong adversary.

**Equivocate.** P5 (`BlockUniverse.no_equivocation`) quantifies over
`Correct` alone, so a Byzantine author may publish any number of distinct
blocks for one round. Nothing in the safety development limits how many:
§8.1 shows the equivocation degree enters no safety statement, and the
`Utwin6` model exhibits two blocks by one author each passing
Odontoceti's indirect test against a third (§10.5).

**Withhold entirely.** No clause obliges a Byzantine validator to publish
anything. A Byzantine *leader* may therefore leave its slot undecided,
which is why P10 asks only that reliable leaders recur, and why L5
(skipping) exists.

**Send selectively.** A Byzantine author may deliver a block to some
correct validators and not others, at any time. Every network assumption
in §4.3 is restricted to correct-authored blocks for exactly this reason:
`ViewsConverge` carries the restriction in its statement, and a
formulation that dropped it would be assuming Byzantine validators
behave, which is not an assumption anyone can implement against.

**Reveal late.** Delivery bounds apply from GST and to correct authors. A
Byzantine validator may release a block long after building it, and the
commit rules must — and do — treat a late block as a block.

**Lead any slot.** `Slots.leader` is an arbitrary function; the schedule
is not assumed to favour correct validators. P10 asks only that reliable
leaders appear arbitrarily far out, which a round-robin schedule
discharges whenever the reliable set is of quorum size.

**What the adversary may not do** is exactly three things, and each is
either cryptographic or a counting bound. It may not forge a block under
another validator's name — authorship is taken as authenticated, the one
cryptographic assumption in the development and the only clause of §4
with no Lean counterpart. It may not exceed `f` in number (`Faults`,
§4.2). And under the DoS conditions of §4.7 it may not force a correct
validator to store more than the stated bound.

**The limits are witnessed, not merely stated.** Three models show that
weakening a network hypothesis does not merely block a proof but makes
the conclusion false: `bound_is_necessary` (the delivery bound cannot be
dropped for coverage), `ugap_not_viewsConvergeOn` (the starting round
cannot be dropped), and `reliable_set_is_forced` (coverage over the
reliable set does not extend to `Correct`). §6.9 gives them in full.

### 4.7 The denial-of-service conditions

§8 assumes four further conditions, none of them about the network. Two
are enforceable by a correct validator acting alone, which is the
property that makes them deployable; the other two are structural.

```lean
def DoSValid (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator
```

**D (`DoSValid`) — do not build on an exposed author.** A block never
references a block whose author is already exposed as an equivocator
within the referencing block's own history. Checkable locally, since
exposure is a fact about the cone a validator already holds.

```lean
def UniformBudget (D : Delivery U) (T : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (novelty U (viewUpto D v n) b).card ≤ T
```

**The novelty budget — accept nothing that costs more than `T` new
blocks.** `UniformBudget` is the author-blind form and the one an
implementation should use: it consults no identity, so a validator can
enforce it without knowing who is correct. `ByzBudget κ` is the same
bound imposed only on Byzantine-authored blocks; it is what the theory
needs, and `uniform_of_byzBudget` shows the enforceable form implies it.

```lean
def RefsAccepted (D : Delivery U) : Prop :=
  ∀ w ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = w → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted w n
```

**The reference discipline — reference only what you accepted.** The
converse of P7, and equally a clause an implementation executes.

The distinction matters for deployment: `DoSValid`, `UniformBudget` and
`RefsAccepted` are conduct a validator can follow unilaterally, so the
storage bound of §8.5 rests on nothing an operator must trust others to
do. `ByzBudget` is not, and appears only as the weaker hypothesis the
enforceable one discharges.

### 4.8 Where each assumption is consumed

Extracted from the compiled development rather than compiled by hand: a
result appears against a clause when its proof reaches that clause, by
any path. Read down a column to see what an implementation puts at risk
by violating a clause; read across to see what a result depends on.

| | Clause | Consumed by |
|:---|:---|:---|
| P1 | `ValidWrt.predecessor` | T2, T3, T3a, T3c, M1, M2, M3, M4, M5′, M5, M6, L0, CQ3, CQ5, CQ6, CQ7, C2, D15a, C1′, C3′, B4, B, B5, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G10, G11, G12, G8, G9 |
| P2 | `ValidWrt.distinct_creators` | M5′, M5, M6, C1′, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G12, G8, O1′, O4′, O5, O6 |
| P3 | `ValidWrt.quorum` | T3, T3a, T3c, M2, M4, M6, L0, CQ5, CQ6, CQ7, D15a, B5, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G10, G11, G12, G8 |
| P3′ | `ValidWrt.self_parent` | C1′, C3′, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G11, G12, G8, G9 |
| P4 | `BlockUniverse.complete` | T2, T3, T3a, T3c, M1, M2, M3, M4, M5′, M5, M6, L0, L3, L6, L8b, CQ3, CQ5, CQ6, CQ7, C2, D15a, C1′, C3′, B4, B, B5, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G10, G11, G12, G8, G9, O7, O10 |
| P5 | `BlockUniverse.no_equivocation` | T1, T3, T3a, T3c, M1, M2, M3, M4, M5′, M5, M6, L7b, L7c, L8a, L9, C2, D15a, C1′, B4, B, B5, G1, G2, G3, G4, G5, G13, G14, G6, G6b, G7, G12, G8, O1, O1′, O2, O4′, O5, O6 |
| P7 | `Delivery.includes` | L7a, C3′, B5, G6, G6b, G7, G11, G12, G9 |
| P8 | `Live.builds` | L1 |
| P9a | `Timing.waits` | L7b, L7c, L8a, L9 |
| P9b | `Timing.prompt` | L8a, L9 |
| P10 | `FairScheduleOn` | L6, CQ6 |
| N1 | `DeliversQuorum` | L1 |
| N2a | `EventuallyDelivers` | L7a, C3′, G6b, G7, G9 |
| N2b | `Timing.covers` | L7b, L7c, L8a, L9 |
| N2v | `ViewSync.converges` | L7c |

Three readings are worth drawing out. **P8 and N1 now reach only L1**:
since the liveness results take production as a `Populated` hypothesis
rather than deriving it inline, the quorum route is one way to discharge
that hypothesis and no result is committed to it (§4.4). **P3′ is absent
from safety and liveness entirely**, feeding only the DoS and
garbage-collection arcs — the report's claim to that effect is this table
row. And **P4 and P5 appear almost everywhere**, which is the honest
shape of the development: causal closure and non-equivocation are what
the DAG is, not conditions imposed on it.

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

The chapter is organised around two interface predicates, and every
result above them consumes them as hypotheses rather than reaching for a
network assumption: **production** (`Populated`, §6.3) and **coverage**
(`SynchronisedOn`, §6.4). The main line discharges both from a single
network clause, view convergence, in §6.7–§6.9; the quorum route that
discharges production instead from N1 lives in `Network/Quorum.lean` and
is noted where it is relevant (§4.3).

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

No network assumption is stated over this structure in the main line.
The view-convergence layer *produces* a delivery —
`ViewGrowth.toDelivery`, §6.9 — and the DoS arc's novelty budget is a
rule about `accepted`. The quorum assumption N1 (`DeliversQuorum`), the
delivery-level alternative kept in `Network/Quorum.lean`, is documented
in §4.3; nothing below depends on it.

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

`Populated` is the production half of the liveness interface (§6.10):
every result above this section takes `∀ r ≤ N, Populated U r` as a
hypothesis, and which route discharges it is decided at the point of
application. The main line derives it from view convergence — the
induction of `ViewGrowth.populatedOn` in the timed setting, and of
`populated_of_viewsConverge` in the untimed one (§6.9), both running
`builds` against blocks that convergence places in the builder's hands.

The quorum route derives the same conclusion in `Network/Quorum.lean`:

**L1.**
```lean
theorem no_stall {D : Delivery U} (H : Live U D N) (hd : DeliversQuorum D) :
    ∀ r ≤ N, Populated U r
```

with the quorum obtained from N1 rather than from convergence — the
inductive hypothesis makes a quorum *exist*, `DeliversQuorum` converts
existence into each correct validator *holding* one, and `builds`
applies. It is the weakest hypothesis of the three and needs no clock,
which is why the module survives; nothing else in the development
consumes it.

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

The horizon is consumed exactly where production is derived — L1 and
the two view-convergence derivations alike; L4 itself never mentions
`N`.

### 6.4 Eventual DAG synchrony

```lean
def SynchronisedOn (U) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ T →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ T → a ∈ (U.block b).refs
```

The condition is restricted to correct authors on both sides, and both
restrictions are consequential.

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

def CommitsAt (BlockId) (Payload) (T : Finset Validator) (R k : ℕ) : Prop :=
  ∀ U N, (∀ r ≤ N, Populated U r) → SynchronisedOn U T R →
    S.slotRound k + 2 ≤ N →
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)

theorem commits_recur_on (hT : T ⊆ Correct)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧ CommitsAt BlockId Payload T R k'
```

The order of quantification carries the content. The alternative reading — that
given a universe populated to `N`, for every `k` there exists a committing
`k' ≥ k` with `slotRound k' + 2 ≤ N` — is false: fairness promises a correct
leader somewhere beyond `k`, and that slot may lie beyond the horizon, with
nothing to license requesting a nearer one. As stated, `k'` depends only upon
the schedule, which is a property of the `Slots` instance and not of any DAG;
the universe is then required to have grown far enough. This is also the
correct reading of the claim that the ledger grows without bound (§6.3).

The unboundedness of slot rounds required by the proof is `Slots.unbounded`,
with `Slots.mono` carrying it past the fair slot; three-round spacing, which
once supplied both, is not assumed (§3.4).

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
of `D.held v n`. That indexing is what carries the argument, and it is exactly
what a
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
  blk_mem : ∀ v ∈ T, ∀ n ≤ N, …
  blk_creator : …
  blk_round : …
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

The routes of §6.7 and §6.8 state the network's contribution over objects
the protocol builds — `held` in one case, `refs` in the other. A third states
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

**`covers` is two clauses, not one.** It concludes about `refs`, fusing a
network guarantee with the protocol's referencing rule (§4.3). Stated
over views the two are apart: `converges` is the network's, `references` is P7 in the timed
setting, and the composite field becomes a *theorem*:

```lean
theorem covers_of_converges : … vs.blk w n ∈ (U.block (vs.blk v (n + 1))).refs
```

The block is in its author's hands when built (`holds_own`), reaches the
builder within `delay` (`converges`), is still there when the builder
acts (`holds_mono` — which is where the hypothesis
`built w n + delay ≤ built v (n+1)` is used), and is therefore
referenced (`references`).

**L7c.**
```lean
theorem ViewSync.synchronisedOn_of_converges (hT : T ⊆ Correct)
    (hD : vs.DriftFrom R D) (hgst : vs.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vs.delay ≤ vs.timeout n) :
    SynchronisedOn U T R
```

with `ViewSync.exists_synchronisedOn_of_converges` giving the backoff
form, as in §6.8.

**The routes form a hierarchy, not a pair.** `ViewSync.toTiming`
exhibits a `ViewSync` as a `Timing`, so every result of §6.8 applies
unchanged — drift still derived from `prompt`, the backoff still
terminating, the quantitative bounds of §6.11 unaffected. The timing
route is what the view-convergence route becomes once P7 is applied,
which is the hierarchy of §4.3.

**The bound, factored out.** `converges` is partial synchrony in its
familiar two-part form, and the parts separate:

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
the first following without further hypotheses
(`ViewSync.convergesEventually`).

**The bound is indispensable.** Eventual convergence alone yields
nothing: the derivation above needs the block in
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

theorem viewsAgree_of_converges (hT) (hD : vs.toTiming.DriftFrom R D) (hgst)
    (hbackoff : ∀ n, R ≤ n → D + vs.delay ≤ vs.timeout n) : vs.ViewsAgree R
```

the bound (to compare a lag with a timeout at all), the drift (to compare
one validator's clock with another's) and the wait (to push the build
past both).

**The untimed variant.** The same condition may be written with no clock
at all, over `Delivery`:

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

N1 is not thereby obtained without cost. Index-aligned sharing of every
correct block is **stronger** than N1, which promises only a quorum and
only when one exists; what is obtained is uniformity of formulation, not a
weaker hypothesis. And **the untimed condition is not a delivery assumption but
a delivery assumption combined with a waiting clause.** In the untimed model
that fusion cannot be undone, for a structural reason:
`Delivery.held v n` is indexed by the *round*, and `held_spec` confines
it to round-`n` blocks, so a round-`n` block can appear only at index
`n`. "It arrived, but after `v` had already built" is inexpressible —
the model has nowhere to place the arrival event relative to the build
event. Separating them requires an ordering of those events, which is to
say a clock; with one, the split is exactly `converges` against `waits`,
and `viewsAgree_of_converges` carries the unfused pair to what the
untimed model must postulate.

**Production, derived in the timed route as well.** The two routes appear
to treat block production differently: the untimed one derives it, while
the timed structures carry `blk`, a total function giving every
`T`-validator a block at every round below the horizon. The difference is
one of presentation. The three `blk` fields say exactly that every
`v ∈ T` has a round-`n` block, which is `PopulatedOn U T n`; and a choice
function extracted from `PopulatedOn` satisfies them, the choice being
canonical because non-equivocation makes a correct validator's round-`n`
block unique:

```lean
theorem exists_blk_of_populatedOn [Nonempty BlockId]
    (hpop : ∀ n ≤ N, PopulatedOn U T n) :
    ∃ blk : Validator → ℕ → BlockId,
      (∀ v ∈ T, ∀ n ≤ N, blk v n ∈ U.ids) ∧
      (∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).creator = v) ∧
      (∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).round = n)
```

So `blk` is `PopulatedOn`, Skolemised, and the timed route may derive it
instead. `ViewGrowth` is `ViewSync` with `blk` removed and the build rule
put in its place:

```lean
structure ViewGrowth (U) (T : Finset Validator) (R N : ℕ) where
  …                                        -- the schedule, as in `ViewSync`
  holds_own : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n → b ∈ holds v (built v n)
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  references : ∀ v ∈ T, ∀ n < N, ∀ c ∈ U.ids,
    (U.block c).creator = v → (U.block c).round = n + 1 →
    ∀ a ∈ holds v (built v (n + 1)), (U.block a).round = n →
    a ∈ (U.block c).refs
  base : PopulatedOn U T R
  builds : ∀ v ∈ T, ∀ n, R ≤ n → n < N →
    (Fintype.card Validator - F.f) ≤
      (creatorsOf U.block
        ((holds v (built v (n + 1))).filter fun b => (U.block b).round = n)).card →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n + 1
```

Two clauses had to be generalised, and they are exactly the two that
mentioned `blk`: `holds_own` becomes a statement about any block a
validator authored, and `references` about any block it authors at round
`n+1`. Both are what one would state in any case, since non-equivocation
makes the block unique; with them neither clause mentions the function
being constructed, and the circularity is gone. `builds` is `Live.builds`
with `D.accepted v n` replaced by the round-`n` part of the build-time
view — the same rule, over the object this layer has.

Production is then a theorem:

```lean
theorem ViewGrowth.populatedOn (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn vg.built T R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n) :
    ∀ n ≤ N, PopulatedOn U T n
```

by the induction of `populated_of_viewsConverge` run over the timed data:
each `w ∈ T` authored a round-`n` block and holds it at `built w n`,
which is past GST since rounds advance time; convergence puts it in `v`'s
hands by `built w n + delay`, and drift, the wait and the backoff put that
before `built v (n+1)`. So `v`'s build-time view carries a round-`n` block
from every member of `T`, and `builds` applies. `ViewGrowth.toViewSync`
then Skolemises the result, so every theorem of §§6.8–6.9 applies to a
structure that assumed no blocks exist.

**What remains asymmetric, and should.** `converges` says nothing below
`gst`, so production is derivable only from a round `R` at or after the
GST crossing. `ViewGrowth` therefore carries `base`, and it is a *single*
seed round: the step consumes only its predecessor, so nothing is assumed
about the rounds beneath `R`. `ViewsConverge` is unconditional and drives
production from round `0`.

The natural objection is that convergence *is* available before GST, in
its unbounded form — `convergesEventually_of_within` establishes
`ConvergesEventually` at every instant, GST or not. It cannot serve here,
for the reason `covers_of_converges` exhibits: the block must be in the
builder's hands before it builds, and a lag that merely exists cannot be
ordered against a build time. That comparison is what `hbackoff`
performs, and it requires a bound. What lets the untimed route begin at
round `0` is therefore not the absence of a GST but the index alignment
of `ViewsConverge`, which supplies the ordering by fiat and is, for that
reason, the stronger assumption.

The residue is thus the content of partial synchrony rather than a defect:
before GST the network may deliver nothing, and no round need be
populated. The two routes run the same induction and differ only in where
it starts — `R = 0` untimed, `R` past GST timed.

**The untimed condition, induced.** `ViewsConverge` is stated over a
`Delivery`, whose `held v n` is documented as *what `v` held from round
`n` when it built its round-`n+1` block*. A `ViewGrowth` has exactly
that, as `holds v (built v (n+1))`, so it induces a delivery and the
untimed condition becomes a theorem about it:

```lean
def toDelivery : Delivery U where
  held v n := (vg.holds v (vg.built v (n + 1))).filter
    fun b => (U.block b).round = n ∧ v ∈ T
  accepted v n := … fun b => … ∧ (U.block b).creator ∈ (Correct : Finset Validator)
  …

theorem viewsConvergeOn_toDelivery (hD : DriftOn vg.built T R D N)
    (hgst : vg.gst ≤ R) (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n) :
    ViewsConvergeOn vg.toDelivery T R
```

Accepting conservatively is what makes `accepted_inj` a theorem rather
than a further assumption: two accepted blocks share an author only if
that author is correct, and non-equivocation identifies them. `includes`
is `references`, and needs no side condition on the horizon because no
block exists above `N`.

Two relativisations survive the passage. The induced delivery holds
nothing outside `T` or above the horizon, because `converges` and
`holds_own` say nothing there; and the derived condition runs from `R`
on, because `converges` is silent below `gst`. So `ViewsConvergeOn T R`
is what is obtained, of which `ViewsConverge` is the case `T = Correct`,
`R = 0` — `viewsConverge_toDelivery`, with both parameters carried in the
type since they are parameters of the structure.

Whether these are artefacts of the derivation or properties of the
setting matters, since only in the second case is the hierarchy real.
Both are settled, by models in which everything else holds and the
conclusion fails.

For the starting round, `ugap_not_viewsConvergeOn` exhibits a
`ViewGrowth` whose `gst` lies beyond the run and on which the untimed
condition fails outright, so `gst ≤ R` cannot be dropped.

For the reliable set, `reliable_set_is_forced` takes `T = {1,2}`, a
proper subset of `Correct`, over a DAG withholding validator `3`'s blocks
from everyone's references. The network assumption is met properly there
— `gst = 0`, a real bound of `1` — so coverage over `T` is *derived*,
while coverage over `Correct` is *false*. That second statement is about
the DAG alone, independent of any delivery, which forestalls the
objection that the relativisation is an artefact of how `toDelivery`
treats validators outside `T`. `ViewsConverge` fails a fortiori, and for
the same reason: a correct validator outside `T` builds on nothing anyone
else can see.

The relation between the timed and untimed formulations is therefore a
hierarchy, in the same shape as the one between `converges` and
`Timing.covers`, rather than an equivalence.

**The bound is necessary.** `convergesWithin_iff_bounded` factors the
network assumption into a qualitative half and a quantitative one, and it
is fair to ask whether the second is doing any work. It is, and the claim
is now checked rather than argued. `Ugap` is `Ugrow` with one block per
round withheld — validator `2`'s, from everyone but validator `2`. The
withheld blocks arrive after every build in the run, so holdings converge;
they converge too late to be referenced. `ugapGrowth` certifies every
protocol clause field by field, and

```lean
theorem bound_is_necessary (hN : 0 < N) :
    ConvergesEventually (ugapGrowth N).holds Correct ∧
      ¬ SynchronisedOn (Ugap N) Correct 0
```

Convergence without a bound holds from time `0`; coverage fails at every
round the horizon leaves room for. The structure carries `gst = 4N + 5`,
after every build in the run, so `converges` is true of it but says
nothing — which is precisely the situation the qualitative half describes.
Nothing is contradicted: `synchronisedOn_of_converges` requires
`gst ≤ R`, and at such an `R` coverage holds vacuously for want of blocks
above it. What the model shows is that the qualitative half alone carries
none of the weight.

The reduction is more demanding than the derivation. `ViewGrowth.toViewSync`
requires population at *every* round below the horizon, since `blk` is
total, and so takes the pre-`R` rounds as an explicit hypothesis. That is a
constraint of `Timing`'s shape, not of the argument: deriving production
needs one seed round, whereas presenting the result as a `ViewSync` needs
blocks everywhere.

### 6.10 The layering

![**The core account: what supports what.** Every arrow is extracted from the compiled Lean environment — `A → B` means `A` is used in the proof of `B`, directly or through unlabelled lemmas, with arrows implied by longer paths removed. Assumptions occupy the left column; each further column is one step from them. A box with no incoming arrow depends only on definitions and unlabelled lemmas; L4 is the notable case, taking its quorum as a hypothesis rather than from the fault model. §12 describes the extraction; a version carrying each result's Lean name is in `docs/depgraph/`.](depgraph/support-core-compact.svg)

No theorem above `SynchronisedOn` mentions time, and no theorem below it mentions
certificates. The diagram also locates the trust boundary: the leftmost column is
the whole of what is assumed, and it divides into assumptions about an adversarial
network (N1, N2) and clauses of the algorithm (P1–P10) — the derivations of
coverage are visible as the only results drawing on the network column.

**Three separations, different in kind.** The development draws three
lines; only the first is the one usually meant by "confining the time
model".

*Time from graph structure* — the interface is the pair
`SynchronisedOn` and `PopulatedOn`, coverage and production. Everything
above it is finite combinatorics over a DAG; everything that mentions an
instant lies below. Both halves are `Prop`s about a block universe, so
the layers meet at a statement rather than at a module boundary, and any
of the routes of §§6.7–6.9 may supply them. Extraction confirms the
division: of the 67 labelled results, four mention a clock — L7b, L7c,
L8a and L9, which are the derivations themselves — and every theorem of
`Timing.lean`, `Quantitative.lean` and `ViewSync.lean` that concludes
anything used above the line does so by first establishing
`SynchronisedOn` or `PopulatedOn`. This is the separation the report's
title claims, and the diagram shows it as a column that every liveness
result passes through.

*Network from protocol* — the interface is the pair
`converges` / `references` of §6.9. This line is invisible in the delivery
and timing routes: `EventuallyDelivers` is indexed at build time, and
`Timing.covers` concludes about `refs`, so each tacitly carries some
protocol content. Only the view-convergence route states the network's
contribution in a form containing nothing the protocol does, which is why
§4.3 can now claim that the network's whole contribution is one sentence
about views.

*Assumed from derived* — the interface is `Populated`. Production may be
assumed, as `Timing` and `ViewSync` do in carrying `blk`, or derived:
from N1 with P8 through L1; from untimed view convergence with `HoldsOwn`
through `populated_of_viewsConverge`; or, in the timed setting, from
`converges` with the build rule through `ViewGrowth.populatedOn`. The
assumed form is not a different hypothesis but the derived one
Skolemised, and `exists_blk_of_populatedOn` is the identification. What
the three derivations differ in is where the induction may start: at
round `0` for the two untimed ones, and only past GST for the timed one,
since `converges` says nothing before it. N1 is retained — in
`Network/Quorum.lean`, outside the main line — because deriving
production from a *conditional quorum* hypothesis is the weaker and the
implementable option.

The routes may therefore be summarised by what each assumes and what it
still owes:

| Route | Network assumption | Also needs | Yields |
|:---|:---|:---|:---|
| Delivery (§6.7) | `EventuallyDelivers` — build-time indexed | P7 | `Synchronised` |
| Timing (§6.8) | `Timing.covers` — Δ after GST, concludes on `refs` | P9, drift | `SynchronisedOn` |
| View convergence (§6.9) | `converges` — Δ after GST, over views | P7, P9, drift | `SynchronisedOn`, and the other two |
| View growth (§6.9) | `converges`, with `blk` removed | P7, P8, P9, drift, one seed round at `R` | `PopulatedOn` from `R` on, and `SynchronisedOn` |
| Untimed views (§6.9) | `ViewsConverge` — no bound, index-aligned | `HoldsOwn`, P8 | `Populated`, from round `0`, without N1 |

The three routes are interchangeable at the interface. Results above it
take `PopulatedOn` and `SynchronisedOn` as hypotheses, so which route
supplies them is a choice made at the point of application rather than a
commitment baked into the statements.

Read downward, the first three are increasingly primitive statements of
the same assumption; the last two yield production as well as coverage,
and differ only in the round at which their common induction may start.

### 6.11 Quantitative results

The results of this section are collected in `Quantitative.lean`, which the
view-convergence layer and the chain-quality capstone build on. Each
strengthens a result above under a strengthened clause (§4.5); a reader
declining those clauses retains §6.1–§6.10 intact.

**The weak hypotheses admit no bound.** Two of the results above conclude with
an existential statement that supplies no bound on its witness —
`∃ R, SynchronisedOn U T R`, and `∃ k', k ≤ k' ∧ …`. This is not a
deficiency of the proofs. Each governing hypothesis has the same form, and under such hypotheses
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

`Timing.populatedOn` supplies L4's population hypotheses from the `Timing`
structure directly, because `Timing.blk` is total below the horizon — P8 in
its strongest form, a block at every round with no exception (§6.9 identifies
it as `PopulatedOn` Skolemised). These statements consequently require
neither `Live`, nor N1, nor L1: their only temporal hypotheses are the start
spread, the wait, and the position of the slot relative to GST.

---

## 7. Chain quality: coverage and inclusion

*(companion document: `chain-quality.md`; modules `LeanDag/Quality/`)*

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
def IncludesAt (BlockId) (Payload) (R m k : ℕ) : Prop :=
  ∀ U N, (∀ r ≤ N, Populated U r) → Synchronised U R →
    S.slotRound k + 2 ≤ N →
    ∃ L, Decided U (View.full U) k (some L) ∧
      ∀ b ∈ U.ids, (U.block b).creator ∈ Correct →
        (U.block b).round = m →
        b ∈ history U L ∧
        ∀ g n, g k = some L → k < n → b ∈ ledgerSet U g n

theorem committed_of_correct_block (hT : T ⊆ Correct)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (fair : FairScheduleOn T) (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt BlockId Payload R m k'
```

— for every round `m ≥ R` the schedule fixes, *before the universe is
quantified*, a committed slot whose flush contains every correct
round-`m` block. (`commits_recur_on` does not
expose the committed leader's membership in `T`, which the backbone
needs, so the proof composes from the fair schedule and L4 against the
production hypothesis directly, mirroring L6's own proof.) The quantitative forms pin the
slot to a window: under `FairWithin T w` the committing slot lies
within `w` slots of the first slot above round `m`
(`committed_of_correct_block_within`), and under `BoundedSpacing s` its
round within `s·w` rounds (`committed_of_correct_block_by_round`) — *a
correct block is committed within a schedule-window of its creation,
once the DAG is synchronous*. The capstone `chain_quality` packages
both halves under enforceable or standard conditions only.

A block-count purity variant was considered and rejected: under `DoSValid`
alone the per-author block count carries the exponential constant of §8.3,
and under the budget the cone-level Byzantine count is a whole-store
bound. Neither yields an informative ratio, and the author-coverage
metric is the appropriate one.

---

## 8. Denial of service: equivocation, growth, and the novelty budget

*(companion document: `dos-equivocation-and-growth.md`; modules `LeanDag/DoS/`)*

Safety needs no protection from equivocation: every result of §5 holds with no
anti-equivocation condition anywhere in its hypotheses, and the independence is
itself recorded — a witness model satisfies safety while violating every
storage condition of this section (`LeanDagTest/DoS/SafetyUnderDoS.lean`).
*Storage* is another matter. An uncertified DAG admits Byzantine blocks into
correct views by design, an equivocator may produce arbitrarily many blocks
per round, and a correct validator that retains the cones of what it accepts
can be made to retain material injected by an adversary. This
section bounds that growth in two ways: first under a *reference-validity* condition (exposure),
whose bound is shown essentially optimal yet exponential in `f`; then under a
*rate-limiting* condition (the novelty budget), which is enforceable,
author-blind, and yields the linear result `dos_resistance`. The two
compose: the budget limits the rate at which an equivocator can inject
material, and exposure terminates it.

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
`|Correct|` blocks per round, *linear in `n`* is the best attainable;
the question is the constant, and whether the Byzantine share can exceed it.

The *novelty* of an arriving block is what its cone adds over the store:

```lean
def novelty (U) (V : Finset BlockId) (b : BlockId) : Finset BlockId :=
  history U b \ V
```

Novelty is antitone in the store — the more a validator already holds, the
smaller the novelty of any arriving block — the monotonicity on which every
argument below depends.

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
and the commit chain still operates over
them: the witness model `Uexcl` carries a
direct commit whose three rounds all lie after the exclusion of its
equivocator (§11). Nor does exclusion depend on favourable circumstances:
*density* establishes that a
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

The exponential constant is not an artefact of the proof: a matching family of
witnesses (`Udouble`, §11) realises `2^(e−2)` growth from `e` equivocators,
so any bound obtainable from reference-validity conditions alone carries a
constant exponential in `f`. This is the assessment of the exposure
mechanism as a *storage* defence: it is the right accountability layer — it
identifies and permanently retires equivocators at the cost of quorum
margin — but no practical storage bound can rest upon it. Rate limiting is
required, and is orthogonal to it.

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
observable conduct. The blind and guarded formulations bound each other to
within a factor of `f`:

* `UniformBudget.byzBudget : UniformBudget D T → ByzBudget D T` — dropping
  a guard weakens nothing; and conversely
* `uniform_of_byzBudget` — post-`R`, under `ByzBudget κ`, *every*
  acceptance (correct authors included) adds at most `f·κ + 1`.

The converse direction is the substantive one, and the mechanism behind it
should be stated. Why would a *correct* author's block have small novelty? Because a
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

The same self-parent mechanism yields a purely structural form: if
every correct block adds at most `κ'` over its self-parent (`StepNovelty`),
then correct cones are linear outright,
`|H(b)| ≤ κ'·round(b) + 1` (`card_history_le_of_stepNovelty`) — a telescope
along the self-parent chain, with no delivery model at all.

### 8.5 The principal result, and the composition

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
The capstone quotes **enforceable conduct only** — the author-blind budget
and the reference rule — and carries production through alongside the
storage bound, so both hold of the same execution. Production itself is a
hypothesis rather than a premise of the DoS argument: any of the routes of
§§6.7–6.9 discharges it (§4.3):

```lean
theorem dos_resistance {T N : ℕ} (hpop : ∀ r ≤ N, Populated U r)
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

— the budget limits the rate at which an author can inject material;
exclusion terminates it. On data,
the budget is satisfiable at its exact constant: the witness schedule
`Dtwin` satisfies `UniformBudget 3` with its costliest acceptance costing
exactly `3`, and `ByzBudget 0` — nothing Byzantine accepted after the
genesis round (§11).

How should the parameter `T` be set? Any `T ≥ 1` admits every correct block
post-`R` (the sandwich's `f·κ + 1` with `κ = 0` would be the correct-only
floor); smaller `T` tightens the Byzantine rate and defers — never refuses —
correct blocks of high novelty, deferral being a rate limit rather than a
refusal, since novelty is antitone in the growing store.

---

## 9. Garbage collection: the horizon

*(companion document: `garbage.md`; modules `LeanDag/GC/`)*

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
unchanged**. This is the design in its entirety: the task is never to re-prove the
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

Liveness transfers with the offset. Production on the truncation is
production upstream with the round index shifted — a round-`r` block of
`chop U G` is a round-`(G+r)` block of `U` — so `populated_chop` (G5)
takes the `Populated` hypothesis every liveness result consumes and
re-establishes it above the cut, consuming no network assumption of its
own. (A delivery layer also transports: `chopD D G` sets
`held v m := D.held v (G + m)`, and the quorum route's assumptions carry
across with it, `live_chopD` and `deliversQuorum_chopD` in
`Network/Quorum.lean`.) Stores correspond exactly —

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
(`novelty_chop_anti`): as the window slides, pruning only decreases novelty,
so an affordable block never becomes unaffordable. The budget conditions
themselves descend to the window (`byzBudget_chopD`, `refsAccepted_chopD`).

The principal storage result is stated per time, because a validator's life
is a
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
cost as well as storage, and the obligation on correct validators is bounded
likewise.

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
a deeper cut is again a cut:

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

The constraints on the lag are best set out theorem by theorem, since
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
applies to the truncation verbatim, the truncation being simply another
universe. Across a
cut, a forgiven author must equivocate *again, inside the new window*, to
be debarred again — one reveal per author per epoch — and the re-entry runs
under the windowed budget: `Λ·f·κ` of injected material per correct store per
epoch,
a term the `card_retained_le` constant already carries. Commit safety never
depended on any of it: the cross-cut results above carry no exclusion,
budget, or exposure hypothesis. A world that forgives every equivocation
still commits the same blocks; it merely retains more.

---

## 10. Odontoceti: two-round commitment

*(companion document: `odontoceti.md`; modules `LeanDag/Odontoceti/`)*

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
safety, and they identify precisely where the committee of size `5f+1` is
required:

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
of §10.4. With it, agreement and safety follow the pattern of §5.5:

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
the indirect-versus-indirect case with a shared anchor and an equivocating
leader.

For implementers: **the candidate-iteration order of the indirect rule is
consensus-critical**. Two honest nodes iterating in different orders (for
instance, arrival order) can commit different blocks for one slot at
`n = 5f+1`; any fixed shared order restores agreement, and "first seen"
does not. The remaining findings are recorded in the design document: a
missing lemma (O4′, assumed tacitly by the published case analysis), the
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
      ∀ U N, (∀ r ≤ N, Populated U r) → SynchronisedOn U T R →
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

One negative observation should be recorded. A model exhibiting *round spread* —
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
chain and a commit after it), the budget satisfiable at its exact constant
(`UniformBudget Dtwin 3` with `ByzBudget Dtwin 0`), the horizon computed and
its statute of limitations exhibited (`chop Uexcl 2`, `chop Umerge 1`), the
attested base sandwich tight at the bottom (`Base Utwin 1 0 = {1,2,3}`), and
every Odontoceti rule and all four `Decided` constructors at `n = 6, f = 1`
(`Uodo`, `Uskip`, `Utwin6`), including the two-twin configuration that
motivates the canonicity premise (`utwin6_both_pass`).

---

## 12. Mechanisation

The development comprises approximately 17,400 lines of Lean 4 (v4.32.2)
against Mathlib, of which some 11,800 constitute the library and 5,600 the
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
| `Liveness.lean` | L0, L2–L6, L7a; the committed-run results |
| `Network/Quorum.lean` | the quorum route: N1, L1, and the results that exist to serve them |
| `Timing.lean` | L7b |
| `ViewSync.lean` | L7c: view convergence, the reduction to `Timing`, the factoring of the bound, the untimed variant, production derived rather than assumed, and the delivery a timed structure induces |
| `Quantitative.lean` | L8a, L8b, L9 |

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

Two details govern the extraction. `ConstantInfo.value?` returns `none`
for *imported* theorems in this Lean version, proofs being loaded
lazily, so the proof term is reached by matching `.thmInfo` explicitly;
otherwise only statement-level dependencies appear. Private declarations
and compiler-generated auxiliaries are kept as pass-through nodes, since
a labelled result frequently reaches another only through one of them.
Mathlib and core constants are dropped, and safely: they never mention a
constant of this development, so no path between two of its results can
run through them.

![**The whole development.** The same extraction over every principal result, including the four arcs. Reading the columns: the core account occupies the left half, and each arc attaches to it at the results it consumes rather than at the top — the garbage-collection operator (G1) sits beside the structural theorems it re-uses, and Odontoceti's counting core (O1–O4′) is independent of Mysticeti's, converging only at its own agreement theorem. Lean names are omitted for legibility; the full-detail rendering is in `docs/depgraph/`.](depgraph/support-full-compact.svg)

The extracted edges are also an independent check on this report's prose,
and three of its claims come out exactly as written. `P3′`, the
self-parent clause, has no outgoing edge in the core view and in the full
view feeds only C1′, C3′, G1, G9 and G11 — which is §2.2's assertion that
safety and liveness never consume it and that it is indispensable to the
denial-of-service and garbage-collection arcs. `L7a ← N2a, P7` and
`L7b ← N2b, P9, T1` reproduce the §4.4 table row for row — `N2a` and
`N2b` being the diagram's labels for N2's `EventuallyDelivers` and
`Timing.covers` forms (§4.3) — the extra `T1`
on the timing route being the non-equivocation step that identifies a
validator's block with the one the timing structure names. And
`O5 ← O1, O1′, O2, O3, O4′` confirms that Odontoceti's agreement rests on
exactly the four counting theorems plus twin uniqueness (§10.3), with
`O4′` — the lemma the published argument lacks — evidently indispensable.

Seven companion documents accompany the development and carry the design
rationale in more detail than a report admits: `spec.md` (safety),
`liveness.md` (liveness), `pipelining-and-multi-leader.md` (the schedule
generalisation), `chain-quality.md` (§7),
`dos-equivocation-and-growth.md` (§8), `garbage.md` (§9) and
`odontoceti.md` (§10), with `related.md` surveying the surrounding
literature. Every statement in this report is drawn from the source.

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

The example does not show a view-shaped assumption to be *inadequate*.
View convergence is adequate but **incomplete**: it is the network half
of a two-part derivation whose other half is a protocol clause, and §6.9
proves both. What the counterexample shows is that the missing half
cannot be supplied by strengthening the network, which is already as
strong as it can be — delivery there is instantaneous. The gap is a
*race* between arrival and building, which only the builder's own schedule
can resolve.

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

The signal driving the backoff is the difficulty. Before GST no period is
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
derivation rests on view convergence, and in the absence of a time model the
chain must terminate at a network assumption; what the reformulation achieves
is to place that assumption where it belongs — on the network, as one clause
over views — and to keep it out of every statement above.

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
decision relation shared between §3.5 and §10.3 — is the cost of that
discipline, incurred twice in mirrored proofs rather than once in
modifications to the core.

**Enforceability is a specification discipline.** The principal result of §8
(`dos_resistance`) quotes only conduct a validator can execute — an
author-blind budget, a reference rule — and no condition that consults an
identity oracle; the cost of author-blindness is a factor of `f` in a
constant, never a theorem. The same discipline shapes §9: horizons are set
by local rules, the attested base replaces agreement with `f+1` sampling,
and every hypothesis of the bootstrap theorems is checkable by the party it
binds. Conditions of this kind survive contact with implementations;
conditions that quantify over `Correct` do not.

**The value of mechanisation is concentrated where equivocation meets
counting.** All four §10
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
differences of method should be recorded. Theirs is an operational model: a
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
mention of time, and the temporal content of partial synchrony confined to
two files beneath a `Prop`-valued interface, where the whole of the
network's contribution reduces to one clause of view convergence and the
structural condition is *derived* — three ways over (§6.7–§6.9).

The same foundation then carried three developments it was not designed for,
essentially unchanged — which is the strongest evidence the abstraction is
placed correctly. The denial-of-service account reused the delivery layer and
the self-parent clause; garbage collection reused every theorem verbatim on
the truncated universe, because truncation was arranged to be a universe; and
Odontoceti reused the entire DAG layer because its quorums are
the `n − f` the development was already parameterised by. Each arc also
returned something to the account of the trust boundary: enforceable storage
bounds, horizons
without consensus, and — in the one place the formalization diverged from a
published argument by necessity — the observation that Odontoceti's
agreement rests on a canonical candidate order that its paper never states.

What remains open is catalogued in §13.6: the backoff dynamics, wall-clock
latency, block-level total order, and liveness below the growth clause.
Beyond those, two directions suggest themselves. The commit-free,
evidence-based horizon rule sketched in the garbage-collection document
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
| L1 | no stall | `no_stall` *(Network/Quorum)* |
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
| — | production from timed view convergence, from the GST crossing | `ViewGrowth`, `ViewGrowth.populatedOn` *(ViewSync)* |
| — | the assumed production clause is the derived one, Skolemised | `exists_blk_of_populatedOn`, `ViewGrowth.toViewSync` *(ViewSync)* |
| — | the untimed condition induced by the timed structure | `ViewGrowth.toDelivery`, `ViewsConvergeOn`, `viewsConvergeOn_toDelivery` *(ViewSync)* |
| — | N2a and L7a derived from view convergence | `ViewGrowth.eventuallyDelivers_toDelivery`, `ViewGrowth.synchronised_toDelivery` *(ViewSync)* |
| — | the bound in `converges` is necessary for coverage | `bound_is_necessary` *(LeanDagTest.Unbounded)* |
| — | and its starting round is forced, not chosen | `ugap_not_viewsConvergeOn` *(LeanDagTest.Unbounded)* |
| — | as is its reliable set: coverage over `T` derived, over `Correct` false | `reliable_set_is_forced` *(LeanDagTest.Unbounded)* |
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
| G5 | liveness transfers | `populated_chop` *(GC/Window)*; the assumption transfer `live_chopD`, `deliversQuorum_chopD` *(Network/Quorum)* |
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

---

<!-- BEGIN GENERATED REFERENCE -->

## Appendix B. The definition reference

Every definition and structure of the development, in the order
a reader meets them. Each entry is the source text, unabridged,
with the explanation the source carries. This appendix is
generated from the compiled development by
`scripts/gen-reference.py`; the statements are therefore the
declarations themselves rather than transcriptions of them.

Nine entries carry proofs, which can look like a
misclassification. They are not. A structure in Lean may have
fields that are propositions — `BlockUniverse` requires causal
closure, validity and non-equivocation — so *constructing* one
means discharging those obligations, and the proof is part of
the definition rather than a theorem about it. `chop`, `chopD`
and `toDelivery` are of this kind: each builds an object whose
type demands the proofs shown. A theorem, by contrast, asserts
a proposition about objects already built, and those are
Appendix C.

### The validator set and the fault model

#### `Faults`

*class, `Validators.lean`*

```lean
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  /-- The fault bound. -/
  f : ℕ
  /-- The Byzantine validators. Everything else is correct. -/
  byzantine : Finset Validator
  /-- There are at least `3f+1` validators. -/
  card_validators : 3 * f + 1 ≤ Fintype.card Validator
  /-- At most `f` validators are Byzantine. -/
  card_byzantine : byzantine.card ≤ f
```

The fault model: `n ≥ 3f+1` validators, at most `f` of them Byzantine.

#### `Correct`

*def, `Validators.lean`*

```lean
def Correct : Finset Validator := (F.byzantine)ᶜ
```

The correct (non-Byzantine) validators.

### Blocks, validity, and the universe

#### `Block`

*structure, `Block.lean`*

```lean
structure Block (Validator BlockId Payload : Type*) where
  /-- The round this block was produced in. -/
  round : ℕ
  /-- The validator that authored the block. -/
  creator : Validator
  /-- Ids of the blocks this one references, all from round `round - 1`. -/
  refs : Finset BlockId
  /-- Opaque application data. Inert throughout Phase 1. -/
  payload : Payload
```

A block: its round, its author, the ids it references from the preceding round, and an opaque payload.

#### `creatorsOf`

*def, `Block.lean`*

```lean
def creatorsOf (blk : BlockId → Block Validator BlockId Payload)
    (s : Finset BlockId) : Finset Validator :=
  s.image (fun i => (blk i).creator)
```

The validators that authored a set of ids. Defined on an arbitrary `Finset BlockId`, not just on a block's refs: T3's hypothesis, T4's commit rule, and T0' all quantify over id-sets that are nobody's refs.

#### `creators`

*def, `Block.lean`*

```lean
def creators (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Finset Validator :=
  creatorsOf blk b.refs
```

The validators behind a block's references.

#### `ValidWrt`

*structure, `Block.lean`*

```lean
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- Every reference sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- A block never cites the same author twice. -/
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  /-- Non-genesis blocks reference a quorum of distinct validators. -/
  quorum : 0 < b.round → (Fintype.card Validator - F.f) ≤ (creators blk b).card
  /-- Non-genesis blocks reference a block by their own creator — *some* such
  block, not a unique one: an equivocator's blocks form a forest of
  predecessor chains, one edge per block, and the condition does not (and
  need not) collapse the forest. Combined with `predecessor` the parent sits
  at the round immediately below, and with `distinct_creators` it is the
  *only* reference sharing the block's author. -/
  self_parent : 0 < b.round → ∃ i ∈ b.refs, (blk i).creator = b.creator
```

Block validity, relative to a lookup function.

The predecessor condition is stated additively rather than as `(blk i).round = b.round - 1`. That avoids `ℕ`-subtraction, and it makes the genesis case *derivable* rather than a separate branch: at round `0` the equation `(blk i).round + 1 = 0` is unsatisfiable, so `refs = ∅` follows (`refs_empty_of_round_zero`). Only the quorum condition needs a round guard.

The quorum is stated on the *creator set*, not on `refs.card`. That is the form every downstream proof wants, and it is the faithful reading of "2f+1 blocks from the previous round" — the protocol means 2f+1 *validators*.

#### `BlockUniverse`

*structure, `BlockDag.lean`*

```lean
structure BlockUniverse (Validator BlockId Payload : Type*)
    [Fintype Validator] [DecidableEq Validator] [Faults Validator] where
  /-- Which blocks exist. -/
  ids : Finset BlockId
  /-- What each id denotes. Total, with junk outside `ids`; every statement
  below quantifies over `i ∈ ids`, so the junk is never observed. -/
  block : BlockId → Block Validator BlockId Payload
  /-- Every referenced block is itself present. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  /-- Every block present is valid. -/
  valid : ∀ i ∈ ids, ValidWrt block (block i)
  /-- Correct validators do not equivocate: at most one block per correct
  author per round. Byzantine validators are unconstrained. -/
  no_equivocation : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator ∈ (Correct : Finset Validator) →
    (block i).creator = (block j).creator →
    (block i).round = (block j).round → i = j
```

Every block that exists, together with the well-formedness conditions the protocol guarantees.

#### `View`

*structure, `BlockDag.lean`*

```lean
structure View (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator]
    (U : BlockUniverse Validator BlockId Payload) where
  /-- The ids this validator holds. -/
  ids : Finset BlockId
  /-- A view holds only blocks that exist. -/
  subset_ids : ids ⊆ U.ids
  /-- A view is closed downward: it holds everything its blocks reference. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids
```

A **view**: one validator's local DAG. A subset of the universe that is itself closed under references.

Views share `U.block`, so they disagree about *which* blocks they hold, never about what an id denotes, and they inherit validity and non-equivocation from `U` unchanged. Different correct validators may hold different views — that asymmetry is the entire point of the cross-view results.

### Causal structure

#### `RefStep`

*def, `CausalHistory.lean`*

```lean
def RefStep (U : BlockUniverse Validator BlockId Payload) (i j : BlockId) : Prop :=
  j ∈ (U.block i).refs
```

One step of causal history: `j` is directly referenced by `i`.

#### `Reaches`

*def, `CausalHistory.lean`*

```lean
def Reaches (U : BlockUniverse Validator BlockId Payload) : BlockId → BlockId → Prop :=
  Relation.ReflTransGen (RefStep U)
```

`Reaches U c b` — `b` lies in the causal history of `c`.

#### `historyUpto`

*def, `History.lean`*

```lean
def historyUpto (U : BlockUniverse Validator BlockId Payload) :
    ℕ → BlockId → Finset BlockId
  | 0, b => {b}
  | n + 1, b => insert b ((U.block b).refs.biUnion (historyUpto U n))
```

Everything reachable from `b` in at most `n` reference steps.

Structural in the fuel `n`, so it is computable and needs no decidability hypothesis. Outside `U.ids` it still evaluates — to junk, like `U.block` itself — and every statement below quantifies over ids of the universe.

#### `history`

*def, `History.lean`*

```lean
def history (U : BlockUniverse Validator BlockId Payload) (b : BlockId) : Finset BlockId :=
  historyUpto U ((U.block b).round + 1) b
```

The causal history of `b`, as a `Finset`.

#### `blocksAt`

*def, `Support.lean`*

```lean
def blocksAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  U.ids.filter (fun i => (U.block i).round = n)
```

The ids present at a given round.

#### `authorsAt`

*def, `Support.lean`*

```lean
def authorsAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset Validator :=
  creatorsOf U.block (blocksAt U n)
```

The validators holding a block at a given round — the pool `p`.

#### `supporters`

*def, `Support.lean`*

```lean
def supporters (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((blocksAt U n).filter (fun q => b ∈ (U.block q).refs))
```

The validators whose round-`n` block references `b`.

#### `correctSupporters`

*def, `Support.lean`*

```lean
def correctSupporters (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  supporters U b n ∩ (Correct : Finset Validator)
```

Validators that are both correct and back `b` with their round-`n` block. This is exactly what the coverage lemmas consume.

#### `blames`

*def, `Support.lean`*

```lean
def blames (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((blocksAt U n).filter (fun q => L ∉ (U.block q).refs))
```

The validators whose round-`n` block declines to reference `L`.

The complement of `supporters U L n` *within the round-`n` author pool* — but only for correct validators. A Byzantine author can appear in both, by publishing one round-`n` block that votes and another that does not; ruling that out for correct validators is exactly what `blames_inter_supporters_subset_byzantine` does, and is the whole content of M3.

#### `correctBlocksAt`

*def, `CommonCore.lean`*

```lean
def correctBlocksAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  (blocksAt U n).filter (fun q => (U.block q).creator ∈ (Correct : Finset Validator))
```

The round-`n` blocks authored by *correct* validators. The counting argument ranges over these: a correct author has exactly one block per round (T1), so `creator` is injective here and blocks and authors can be counted interchangeably.

### Slots and the schedule

#### `uniform`

*def, `Schedule.lean`*

```lean
def uniform (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (elect : ℕ → Validator)
    (hblock : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂) :
    Slots Validator where
  slotRound k := p * (k / m)
  leader k := elect k
  mono := fun _ _ hab => Nat.mul_le_mul_left p (Nat.div_le_div_right hab)
  unbounded := fun n => ⟨m * n, by
    rw [Nat.mul_div_cancel_left n hm]
    exact Nat.le_mul_of_pos_left n hp⟩
  keyed := by
    intro k₁ k₂ h
    simp only [Prod.mk.injEq] at h
    exact hblock k₁ k₂ (Nat.eq_of_mul_eq_mul_left hp h.1) h.2
```

**The uniform schedule**: `m` leaders in every `p`-th round, slot `k` proposed by `elect k`.

`hblock` is the one real condition — the `m` proposers sharing a round are distinct validators. Round-robin `elect k = k % n` satisfies it whenever `m ≤ n`. Without it a single block would be the candidate for two slots and the ledger would deliver it twice.

#### `uniformSingle`

*def, `Schedule.lean`*

```lean
def uniformSingle (p : ℕ) (hp : 0 < p) (elect : ℕ → Validator) : Slots Validator :=
  uniform p 1 hp Nat.one_pos elect (one_hblock elect)
```

**One leader every `p` rounds.** `p = 3` is the schedule the development had before pipelining; `p = 1` is pipelined single-leader.

### The commit rule, and the ledger

#### `votesIn`

*def, `Mysticeti.lean`*

```lean
def votesIn (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Finset BlockId :=
  (U.block C).refs.filter (fun q => L ∈ (U.block q).refs)
```

The references of `C` that vote for `L`.

#### `Certifies`

*def, `Mysticeti.lean`*

```lean
def Certifies (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Prop :=
  (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (votesIn U C L)).card
```

A round-`(r+2)` block certifies `L` when its votes for `L` come from a quorum of distinct validators.

#### `certificates`

*def, `Mysticeti.lean`*

```lean
def certificates (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (r + 2)).filter (fun C => Certifies U C L)
```

The certificates for a round-`r` block `L`: the round-`(r+2)` blocks that certify it.

#### `DirectCommit`

*def, `Mysticeti.lean`*

```lean
def DirectCommit (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (certificates U L r)).card
```

`L` is directly committed when its certificates come from a quorum of distinct validators.

#### `DirectSkip`

*def, `Mysticeti.lean`*

```lean
def DirectSkip (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (blames U L (r + 1)).card
```

`L` is directly skipped when a quorum of distinct validators declined to vote for it.

#### `CertifiedIn`

*def, `Mysticeti.lean`*

```lean
def CertifiedIn (U : BlockUniverse Validator BlockId Payload) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ C ∈ certificates U L r, Reaches U A C
```

The indirect rule's test: does a certificate for `L` lie in the causal history of the anchor block `A`?

#### `Slots`

*class, `Mysticeti.lean`*

```lean
class Slots (Validator : Type*) where
  /-- The round at which slot `k` is proposed. -/
  slotRound : ℕ → ℕ
  /-- The validator whose block is the slot-`k` candidate. -/
  leader : ℕ → Validator
  /-- Slots are enumerated in round order. -/
  mono : Monotone slotRound
  /-- Slot rounds are unbounded. -/
  unbounded : ∀ n, ∃ k, n ≤ slotRound k
  /-- Distinct slots differ in round or in leader. -/
  keyed : Function.Injective (fun k => (slotRound k, leader k))
```

The leader schedule: which validator proposes at which round, as a sequence of slots.

Slots need **not** be three rounds apart. Under pipelining consecutive slots are one round apart, and under multiple leaders per round they share a round, so all that is required of `slotRound` is that it be monotone. The three-round separation M4's commit half needs is no longer a property of *consecutive* slots and is therefore not derivable here; it is required instead of the particular pairs that use it, by `Eligible` below.

`unbounded` was a theorem under three-round spacing (`3 * k ≤ slotRound k`) and is underivable from `mono` alone — a schedule parking every slot at one round is monotone. Liveness needs it, so it is assumed.

`keyed` says distinct slots differ in round or in leader. It too held under three-round spacing, which makes `slotRound` injective outright. Under multiple leaders it is a real condition on the schedule: the proposers of a round must be distinct validators. Without it one block would be the candidate for two slots, and the ledger would deliver it twice.

#### `decisionRound`

*def, `Mysticeti.lean`*

```lean
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 2
```

The round at which slot `k`'s direct rules are settled: its certificates live here. Algorithm 2's `DecisionRound`.

`Validator` is explicit because the result is a bare `ℕ`, so nothing else would fix it — the same reason the three-round spacing lemma is written `S.slotRound`.

#### `Eligible`

*def, `Mysticeti.lean`*

```lean
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j
```

**`j` may anchor `k`.** Its proposal lies past `k`'s decision round, so a block at `j`'s round can reach a certificate for `k`'s — which is exactly M4's `r + 3` hypothesis. Algorithm 3's anchor filter `r_decision < s.round`.

Stated through `decisionRound` rather than as a bare `+ 3` so that a later wavelength parameter is a change to one definition.

It is a predicate on the **pair of slots alone** — not on any view. That is what makes agreement go through: two validators deciding the same slot `k` agree on which slots may anchor it, so each one's eligibility premise is the side condition the other's intermediate-skip premise requires.

#### `IsLeaderBlock`

*def, `Mysticeti.lean`*

```lean
def IsLeaderBlock (U : BlockUniverse Validator BlockId Payload) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k
```

`L` is a candidate block for slot `k`: the right round, the right author.

A *correct* leader has at most one such block (T1); a Byzantine one may have several, which is why the definitions below quantify over candidates rather than selecting one. M5 supplies uniqueness where it is needed.

#### `certificatesIn`

*def, `Mysticeti.lean`*

```lean
def certificatesIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Finset BlockId :=
  certificates U L r ∩ V.ids
```

The certificates for `L` that a view actually holds.

#### `DirectCommitIn`

*def, `Mysticeti.lean`*

```lean
def DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (certificatesIn U V L r)).card
```

Direct commit, as judged from a single view.

#### `DirectSkipIn`

*def, `Mysticeti.lean`*

```lean
def DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤
    (creatorsOf U.block
      (((blocksAt U (r + 1)).filter (fun q => L ∉ (U.block q).refs)) ∩ V.ids)).card
```

Direct skip, as judged from a single view.

#### `Decided`

*inductive, `Mysticeti.lean`*

```lean
inductive Decided (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      Decided U V k (some L)
  /-- The direct rule blames every candidate — including vacuously, when the
  leader produced no block at all. -/
  | directSkip {k : ℕ} :
      (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      Decided U V k none
  /-- Anchored on the nearest eligible committed slot, a certificate is in
  reach. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate is in
  reach. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      Decided U V k none
```

**The decision relation.** `Decided U V k v` — a validator holding the view `V` has settled slot `k`, committing the block `v = some L` or skipping it, `v = none`.

Four rules, in two pairs. The *direct* pair reads the slot's own certificates: a candidate carrying `n−f` of them is committed, and a slot whose every candidate is blamed by `n−f` is skipped. The *indirect* pair applies when the direct evidence is inconclusive, and decides `k` by looking up to an **anchor** — the nearest eligible slot above `k` that is itself committed — and asking whether a certificate for a candidate of `k` is reachable from the anchor's block.

"Nearest" is stated positively: every eligible slot strictly between `k` and the anchor is decided `none`. The negative reading — *no eligible slot between is committed* — would be a negative premise, which an inductive definition cannot carry; the positive form is equivalent, since the sweep decides every slot it passes, and it keeps every recursive occurrence strictly positive. The occurrence sits behind `Eligible`, which is a predicate on two naturals and does not mention `Decided`.

The relation is indexed by a view, so two validators may reach different verdicts by the letter of the definition; M6 (`decided_unique`) is the theorem that they cannot.

#### `commitSeq`

*def, `Mysticeti.lean`*

```lean
def commitSeq (g : ℕ → Option BlockId) (n : ℕ) : List BlockId :=
  (List.range n).filterMap g
```

The blocks committed at slots `0, …, n-1`, in slot order, with skipped slots dropped. `g` is a validator's verdict assignment.

#### `ledgerSet`

*def, `Mysticeti.lean`*

```lean
def ledgerSet (U : BlockUniverse Validator BlockId Payload)
    (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ Reaches U L b}
```

The blocks output after settling slots `0, …, n-1`: everything in the causal history of a committed leader.

#### `OutputAt`

*def, `Mysticeti.lean`*

```lean
def OutputAt (U : BlockUniverse Validator BlockId Payload)
    (g : ℕ → Option BlockId) (b : BlockId) (k : ℕ) : Prop :=
  (∃ L, g k = some L ∧ Reaches U L b) ∧
    ∀ j, j < k → ∀ L, g j = some L → ¬ Reaches U L b
```

`b` enters the ledger at slot `k`: the first committed slot whose leader reaches it.

### Delivery, growth, and coverage

#### `PopulatedOn`

*def, `Liveness.lean`*

```lean
def PopulatedOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r
```

What L4 actually needs of a round: every validator in `T` has a block there.

Local and finite — no growth, no horizon. Splitting this out is what keeps the horizon `N` out of L4 entirely, so the only hard proof in the plan is independent of how `Live` is framed.

**Why a set `T` rather than all of `Correct`.** L4 counts to `2f+1` and never higher, so it needs a *quorum* of reliable validators, not every one of them. Demanding all of `Correct` makes the theorem lapse when a single correct validator misses a single round — a GC pause, a restart — although the protocol still commits. See `liveness.md` §8 Q2.

#### `Populated`

*abbrev, `Liveness.lean`*

```lean
abbrev Populated (U : BlockUniverse Validator BlockId Payload) (r : ℕ) : Prop :=
  PopulatedOn U (Correct : Finset Validator) r
```

The all-of-`Correct` case, which is what L1 produces.

#### `Delivery`

*structure, `Liveness.lean`*

```lean
structure Delivery (U : BlockUniverse Validator BlockId Payload) where
  /-- What `v` held from round `n` when it built its round-`(n+1)` block. -/
  held : Validator → ℕ → Finset BlockId
  /-- Held ids are real blocks of the stated round. Not used by
  `synchronised_of_delivery` below — it is what keeps `Delivery` meaningful,
  since without it `held` could be junk and `includes` would demand blocks
  reference it. -/
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  /-- What `v` chose to build on: a subset of what it held. -/
  accepted : Validator → ℕ → Finset BlockId
  /-- You can only accept what arrived. -/
  accepted_sub : ∀ v n, accepted v n ⊆ held v n
  /-- **The acceptance rule**: at most one block per author. Forced by
  `distinct_creators` — a validator holding two blocks by one author must pick
  one, because it cannot reference both. -/
  accepted_inj : ∀ v n, ∀ i ∈ accepted v n, ∀ j ∈ accepted v n,
    (U.block i).creator = (U.block j).creator → i = j
  /-- A correct block is always accepted. It never conflicts with anything —
  its author has only the one block for that round (T1) — so nothing is ever
  given up by taking it, and L7 needs it. -/
  accepts_correct : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ a ∈ held v n,
    (U.block a).creator ∈ (Correct : Finset Validator) → a ∈ accepted v n
  /-- **The protocol rule.** A correct validator references everything it
  accepted. Implementable and observable — unlike `Synchronised` itself. -/
  includes : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    accepted v n ⊆ (U.block b).refs
```

What each validator had in hand, one round at a time — and which of it it chose to build on.

**Two fields, because delivery and policy are two things.** `held` is what the network brought; `accepted` is what the validator will reference. Until equivocation nothing forces them apart, and a structure carrying only `held`, with `includes` demanding that a correct validator reference *everything* it held, would be **unsatisfiable** the moment a correct validator holds both halves of an equivocation: `distinct_creators` forbids referencing two blocks by one author, so no valid block exists and the validator cannot build at all. See `dos-equivocation-and-growth.md` §4.

`held` must *not* be deduplicated: `U` is defined as every block some correct validator held (§4.2), so pruning at the delivery layer would put the second half of an equivocation outside the universe altogether. The choice of which half to accept is left unspecified, exactly as the timeout is — the model says what was in hand and what was built on, never how either was decided.

#### `Live`

*structure, `Liveness.lean`*

```lean
structure Live (U : BlockUniverse Validator BlockId Payload)
    (D : Delivery U) (N : ℕ) : Prop where
  /-- Every correct validator has a genesis block. -/
  genesis : Populated U 0
  /-- Below the horizon, a correct validator that **holds** a quorum of
  round-`r` blocks has one of its own at `r+1`.

  The quorum is measured against `D.accepted v r`, not against `authorsAt U r`:
  a validator cannot build on blocks it has not received, nor on blocks it
  declined to accept. -/
  builds : ∀ r < N, ∀ v ∈ (Correct : Finset Validator),
    (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (D.accepted v r)).card →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r + 1
```

The positive protocol behaviour liveness needs. Not derivable from the DAG structure — `Correct` is a negative condition and these are positive.

**Asynchrony-only.** `builds` asks that a correct validator has a block at round `r+1` once *some* quorum holds round-`r` blocks; it says nothing about timing, delivery, or whose blocks are referenced. That is what lets L1 hold from round 0 with no synchrony at all.

`N` is the **horizon**, and it is not decoration. `U.ids` is a `Finset`, so without the bound `r < N` these two fields force infinitely many distinct blocks into a finite set and *no universe satisfies them* — see `LeanDagTest.Growth`, where the witness is built, and `liveness.md` §4.4, where the vacuous formulation is discussed.

Note `N` is a **demand** on the DAG, not a bound on it: `Live U N` requires blocks to exist all the way to round `N`, so a larger `N` is a *stronger* hypothesis satisfied by *fewer* universes. Coverage of every DAG comes from quantifying over `N`, never from choosing it large.

#### `SynchronisedOn`

*def, `Liveness.lean`*

```lean
def SynchronisedOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ T →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ T → a ∈ (U.block b).refs
```

From round `R` on, a correct block references every correct block of the round below.

`R` is **not** GST: it is the round from which synchrony has fully taken effect — GST plus however long catch-up ran (`liveness.md` §4.2). It is a round index, not a clock; there is no Δ here.

**Both quantifiers are restricted to `Correct`, and deliberately.** A Byzantine validator may publish nothing at all, or publish and reveal to only some validators, so no assumption about referencing its blocks would be sound — and none is needed: L4 counts only correct certificates, and there are `2f+1` correct validators. Getting this wrong in the *strong* direction, by demanding that all blocks be referenced, would assume Byzantine validators behave.

**This does not follow from view convergence.** A block's references are frozen when it is built: a correct validator waits for `2f+1` round-`n` blocks, and the arrival of the `2f+1`st says nothing about the rest having arrived. Views converging later does not retroactively enlarge blocks. So this is an assumption, not a theorem — see `liveness.md` §4.3, and its §8 question 8 for how it is meant to be split and derived.

#### `Synchronised`

*abbrev, `Liveness.lean`*

```lean
abbrev Synchronised (U : BlockUniverse Validator BlockId Payload) (R : ℕ) : Prop :=
  SynchronisedOn U (Correct : Finset Validator) R
```

The all-of-`Correct` case.

#### `EventuallyDelivers`

*def, `Liveness.lean`*

```lean
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ (Correct : Finset Validator), ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ (Correct : Finset Validator) →
    a ∈ D.held v n
```

**The network assumption**: after `R`, correct blocks reach correct validators in time to be built on. This is eventual DAG synchrony proper — pure delivery, no protocol content.

#### `View.full`

*def, `Liveness.lean`*

```lean
def View.full (U : BlockUniverse Validator BlockId Payload) :
    View Validator BlockId Payload U where
  ids := U.ids
  subset_ids := Finset.Subset.rfl
  complete := U.complete
```

Every correct validator's *eventual* view. Downward-closed by `U.complete`.

#### `CommitsAt`

*def, `Liveness.lean`*

```lean
def CommitsAt (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    [S : Slots Validator] (T : Finset Validator) (R k : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
    (∀ r ≤ N, Populated U r) → SynchronisedOn U T R →
    S.slotRound k + 2 ≤ N →
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**A slot every sufficiently grown synchronous execution commits.**

The conclusion the recurrence results share. Naming it keeps their quantifier order visible — the slot is fixed by the schedule alone, before any execution is named — and keeps production and coverage as the two separate hypotheses they are, rather than bundling them.

#### `FairScheduleOn`

*def, `Liveness.lean`*

```lean
def FairScheduleOn (T : Finset Validator) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T
```

The schedule names a correct leader arbitrarily far out. Without it no recurrence statement holds: `Slots.leader` is an arbitrary function and could name Byzantine validators forever, however synchronous the network.

#### `FairSchedule`

*abbrev, `Liveness.lean`*

```lean
abbrev FairSchedule : Prop := FairScheduleOn (Correct : Finset Validator)
```

The all-of-`Correct` case.

#### `FairRunOn`

*def, `Liveness.lean`*

```lean
def FairRunOn (T : Finset Validator) (c : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ ∀ i, i < c → S.leader (k' + i) ∈ T
```

**The schedule puts `c` consecutive `T`-led slots arbitrarily far out.**

Stronger than `FairScheduleOn`, which promises one `T`-led slot and no more, and it is what P7′ needs: `decided_below_of_committed_run` is fed a *run* of commits, and L4 turns a run of `T`-led slots into one.

Round-robin over `3f+1` satisfies it with `c = 3` for every `f ≥ 1`, whatever the `f` Byzantine validators are and wherever they sit in the rotation. The `f` of them cut the cycle into at most `f` arcs holding `2f+1` correct slots between them, so some arc has at least `⌈(2f+1)/f⌉ = 3` — the ceiling being `3` for all `f ≥ 1` since `(2f+1)/f = 2 + 1/f`. Three is exactly what pipelining asks for, which is a pleasant coincidence rather than a designed one.

Like `FairScheduleOn` this is an assumption about the schedule, not a theorem: `Slots.leader` is arbitrary and could name Byzantine validators for ever.

#### `SpansEligible`

*def, `Liveness.lean`*

```lean
def SpansEligible (c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator i (b + c - 1)
```

**A run of `c` slots reaches three rounds past everything below it.**

This is the one place the schedule's *shape* enters P7′, and it is what makes `decided_below_of_committed_run`'s `hspan` available: the last slot of a run starting at `b` is an eligible anchor for every slot below `b`.

It holds with `c = 1` under three-round spacing and with `c = 3` under pipelining — one commit against three consecutive, which is the entire cost pipelining imposes on this property.

#### `slotAt`

*def, `Liveness.lean`*

```lean
def slotAt (n : ℕ) : ℕ := Nat.find (S.unbounded n)
```

The least slot proposed at or after round `n`.

A three-round-spaced schedule needs no such thing: `3 * k ≤ slotRound k` made slot `n` itself sit past round `n`, so `n` could be used as its own slot index. That coincidence is gone — under multiple leaders slot `n` may still be far below round `n` — so the slot has to be named.

#### `DeliversQuorum`

*def, `Network.Quorum.lean`*

```lean
def DeliversQuorum (D : Delivery U) : Prop :=
  ∀ n, (Fintype.card Validator - F.f) ≤ (authorsAt U n).card →
    ∀ v ∈ (Correct : Finset Validator),
      (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (D.accepted v n)).card
```

**Asynchrony.** A quorum that exists is eventually held. Stated conditionally — existence first, holding second — because unconditionally it would assert the very block production L1 sets out to prove.

No round bound: this is what holds *before* GST too, and it is all L1 needs. Contrast `EventuallyDelivers`, which demands the *whole* correct round and only from `R`.

### Time: GST, drift, and the backoff

#### `Timing`

*structure, `Timing.lean`*

```lean
structure Timing (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) where
  /-- `v`'s round-`n` block. -/
  blk : Validator → ℕ → BlockId
  /-- The time at which `v` built it. -/
  built : Validator → ℕ → ℕ
  /-- The timeout in force at round `n`, common to `T`. -/
  timeout : ℕ → ℕ
  /-- Global stabilisation time. -/
  gst : ℕ
  /-- The post-GST delivery bound — Δ. -/
  delay : ℕ
  /-- The universe stops at the horizon. Without this the structure would be
  **unsatisfiable**, exactly as the first `Live` was: `blk` at every round
  would force infinitely many distinct blocks into the `Finset` `U.ids`
  (`liveness.md` §4.4). -/
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  blk_mem : ∀ v ∈ T, ∀ n ≤ N, blk v n ∈ U.ids
  blk_creator : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).creator = v
  blk_round : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).round = n
  /-- **The waiting rule** (protocol). `v` builds round `n+1` a full timeout
  after entering round `n` — not as soon as it holds a quorum. -/
  waits : ∀ v ∈ T, ∀ n < N, built v n + timeout n ≤ built v (n + 1)
  /-- Timeouts are positive, so time advances with rounds. -/
  timeout_pos : ∀ n, 1 ≤ timeout n
  /-- **Delivery** (network). After GST, a `T`-block built at time `t` is in
  every `T`-validator's hands by `t + delay`; and a validator references
  everything it holds. This is GST, and it is where the chain bottoms out. -/
  covers : ∀ v ∈ T, ∀ w ∈ T, ∀ n < N, gst ≤ built w n →
    built w n + delay ≤ built v (n + 1) →
    blk w n ∈ (U.block (blk v (n + 1))).refs
  /-- The last time any `T`-validator built at round `n` — an explicit max,
  so no `Finset.max'` machinery is needed. -/
  latest : ℕ → ℕ
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  /-- `latest` is *attained*, not merely an upper bound. Without this it could
  be arbitrarily large and would carry no information. -/
  latest_mem : ∀ n ≤ N, ∃ w ∈ T, latest n ≤ built w n
  /-- **Validators do not dawdle** (protocol). Once the timeout has elapsed
  *and* the round below has arrived, a validator builds. The counterpart to
  `waits`, which is the lower bound; this is the upper one. -/
  prompt : ∀ v ∈ T, ∀ n < N,
    built v (n + 1) ≤ max (built v n + timeout n) (latest n + delay)
```

When each validator built each of its blocks, and what the network guarantees about delivery.

`gst`, `delay` and `timeout` are fields rather than parameters because they belong to the execution, not to the statement.

#### `DriftFrom`

*def, `Timing.lean`*

```lean
def DriftFrom (n₀ D : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, n₀ ≤ n → n ≤ N → tm.built w n ≤ tm.built v n + D
```

`T`-validators are never more than `D` apart in real time at the same round, from round `n₀` on.

Stated *from* a round `n₀` rather than from 0, because that is all `synchronisedOn_of_timing` consumes and all `driftFrom_of_prompt` can deliver: while the backoff is still below `delay`, drift may grow.

#### `Rated`

*def, `Quantitative.lean`*

```lean
def Rated (timeout : ℕ → ℕ) : Prop := ∀ n, n ≤ timeout n
```

A backoff that grows **at least as fast as the round index**.

Weaker than it may look, and deliberately so: it fixes no shape, and any schedule dominating the identity qualifies — linear, exponential, or a step function that jumps early and then plateaus high. What it rules out is exactly what `hub` permits: growth so slow that clearing a fixed threshold takes unboundedly many rounds.

#### `FairWithin`

*def, `Quantitative.lean`*

```lean
def FairWithin (T : Finset Validator) (w : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ k' < k + w ∧ S.leader k' ∈ T
```

The schedule names a `T`-leader **within every window of `w` slots**.

The rated form of `FairScheduleOn`. Note `w` is a property of the schedule alone — no DAG, no network — which is what keeps L6's quantifier order intact: the slot is still fixed before any universe is mentioned.

#### `BoundedSpacing`

*def, `Quantitative.lean`*

```lean
def BoundedSpacing (s : ℕ) : Prop := ∀ k, S.slotRound (k + 1) ≤ S.slotRound k + s
```

Consecutive slots are at most `s` rounds apart — the upper companion to such a field. Every real schedule has one; the class omits it because no safety result ever asks.

### View convergence

#### `ViewSync`

*structure, `ViewSync.lean`*

```lean
structure ViewSync (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) where
  /-- `v`'s round-`n` block, when it was built, and the timing parameters —
  as in `Timing`. -/
  blk : Validator → ℕ → BlockId
  built : Validator → ℕ → ℕ
  timeout : ℕ → ℕ
  gst : ℕ
  delay : ℕ
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  blk_mem : ∀ v ∈ T, ∀ n ≤ N, blk v n ∈ U.ids
  blk_creator : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).creator = v
  blk_round : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).round = n
  /-- **P9, the waiting rule** (protocol). -/
  waits : ∀ v ∈ T, ∀ n < N, built v n + timeout n ≤ built v (n + 1)
  timeout_pos : ∀ n, 1 ≤ timeout n
  latest : ℕ → ℕ
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  latest_mem : ∀ n ≤ N, ∃ w ∈ T, latest n ≤ built w n
  /-- **P9, the promptness rule** (protocol). -/
  prompt : ∀ v ∈ T, ∀ n < N,
    built v (n + 1) ≤ max (built v n + timeout n) (latest n + delay)
  /-- What `v` holds at *time* `t` — the temporal index a `View` cannot
  supply (§13.1). This is the object the original design notes wanted the
  synchrony assumption stated over. -/
  holds : Validator → ℕ → Finset BlockId
  /-- A validator holds its own block from the moment it builds it. -/
  holds_own : ∀ v ∈ T, ∀ n ≤ N, blk v n ∈ holds v (built v n)
  /-- Holdings only grow: nothing is forgotten. -/
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  /-- **N2, as view convergence** (network). After GST, whatever a correct
  validator holds at time `t` is held by every correct validator by
  `t + delay`. No mention of blocks, rounds or references: this is a
  statement about views, and it is the whole of what is assumed of the
  network here. -/
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  /-- **P7, referencing** (protocol). A validator references every block of
  the round below that it holds when it builds. This is `Delivery.includes`
  in the timed setting, and it is a clause an implementation executes —
  not something the network provides. -/
  references : ∀ v ∈ T, ∀ n < N, ∀ a ∈ holds v (built v (n + 1)),
    (U.block a).round = n → a ∈ (U.block (blk v (n + 1))).refs
```

`Timing` with its one impure field replaced by the two clauses it conflates: a view-level network guarantee (`converges`) and the protocol's referencing rule (`references`).

Everything else is `Timing`'s, unchanged, because the derivation of reference coverage needs the same waiting and drift machinery either way — the point of the separation is *where the premises come from*, not how many there are.

#### `toTiming`

*def, `ViewSync.lean`*

```lean
def toTiming : Timing U T N where
  blk := vs.blk
  built := vs.built
  timeout := vs.timeout
  gst := vs.gst
  delay := vs.delay
  rounds_le := vs.rounds_le
  blk_mem := vs.blk_mem
  blk_creator := vs.blk_creator
  blk_round := vs.blk_round
  waits := vs.waits
  timeout_pos := vs.timeout_pos
  covers := vs.covers_of_converges
  latest := vs.latest
  built_le_latest := vs.built_le_latest
  latest_mem := vs.latest_mem
  prompt := vs.prompt
```

**The reduction.** A `ViewSync` *is* a `Timing`, so every result of `Timing.lean` applies to it unchanged — `driftFrom_of_prompt`, `synchronisedOn_of_timing`, `exists_synchronisedOn_of_backoff`, and the quantitative results built on them. The two formulations of the network assumption are therefore not siblings but a hierarchy: view convergence is the weaker, more primitive statement, and `covers` is what it becomes once the protocol's referencing clause is applied.

#### `DriftFrom`

*abbrev, `ViewSync.lean`*

```lean
abbrev DriftFrom (n₀ D : ℕ) : Prop := vs.toTiming.DriftFrom n₀ D
```

Drift, stated directly over a `ViewSync`.

#### `ViewsAgree`

*def, `ViewSync.lean`*

```lean
def ViewsAgree (R : ℕ) : Prop :=
  ∀ v ∈ T, ∀ u ∈ T, ∀ n, R ≤ n → n < N →
    vs.blk u n ∈ vs.holds v (vs.built v (n + 1))
```

The untimed condition's shape, stated over the timed structure: from `R` on, every `T`-validator's build-time view contains every `T`-authored block of the round it is building over. This is what `ViewsConverge` asserts outright in the untimed model.

#### `ConvergesEventually`

*def, `ViewSync.lean`*

```lean
def ConvergesEventually (holds : Validator → ℕ → Finset BlockId)
    (T : Finset Validator) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ t, ∃ d, holds w t ⊆ holds v (t + d)
```

**The qualitative half.** Holdings converge: whatever `w` holds at `t`, `v` holds at some later time. No bound and no GST.

#### `ConvergesWithin`

*def, `ViewSync.lean`*

```lean
def ConvergesWithin (holds : Validator → ℕ → Finset BlockId)
    (T : Finset Validator) (gst bound : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + bound)
```

**The quantitative half.** From `gst` on, that lag is at most `bound` — and uniformly so, in the validators and in the time. This is exactly the `converges` field of `ViewSync`.

#### `ViewsConverge`

*def, `ViewSync.lean`*

```lean
def ViewsConverge (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ w ∈ (Correct : Finset Validator),
    ∀ n, ∀ b ∈ D.held v n,
      (U.block b).creator ∈ (Correct : Finset Validator) → b ∈ D.held w n
```

**Untimed view convergence.** What a correct validator holds when it builds for round `n` is held by every correct validator when *it* builds for round `n` — no clock, no Δ, no GST.

Restricted to correct-authored blocks, deliberately: a Byzantine author may send to some correct validators and not others, and no network assumption should forbid that (§4.3).

#### `HoldsOwn`

*def, `ViewSync.lean`*

```lean
def HoldsOwn (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n → b ∈ D.held v n
```

A correct validator has its own block in hand when it builds the next one. The untimed counterpart of `ViewSync.holds_own`, and the clause that turns *existence* of a block into somebody *holding* it.

#### `DriftOn`

*def, `ViewSync.lean`*

```lean
def DriftOn (built : Validator → ℕ → ℕ) (T : Finset Validator)
    (R D N : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, R ≤ n → n ≤ N → built w n ≤ built v n + D
```

Drift over a build schedule alone. `Timing.DriftFrom` is this predicate at `tm.built`, which is all that definition mentions; naming it separately lets the production argument state the hypothesis before any `Timing` exists — and none can exist until `blk` is available.

#### `ViewGrowth`

*structure, `ViewSync.lean`*

```lean
structure ViewGrowth (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (R N : ℕ) where
  built : Validator → ℕ → ℕ
  timeout : ℕ → ℕ
  gst : ℕ
  delay : ℕ
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  /-- **P9, the waiting rule** (protocol), at every round rather than only
  below the horizon. `N` bounds the DAG, not the clock: a schedule does
  not stop honouring its timeouts at round `N`, and the extra round is
  what lets the induced delivery below reach the topmost blocks. -/
  waits : ∀ v ∈ T, ∀ n, built v n + timeout n ≤ built v (n + 1)
  timeout_pos : ∀ n, 1 ≤ timeout n
  latest : ℕ → ℕ
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  latest_mem : ∀ n ≤ N, ∃ w ∈ T, latest n ≤ built w n
  /-- **P9, the promptness rule** (protocol). -/
  prompt : ∀ v ∈ T, ∀ n < N,
    built v (n + 1) ≤ max (built v n + timeout n) (latest n + delay)
  holds : Validator → ℕ → Finset BlockId
  /-- Holdings are real blocks. `ViewSync` can leave this implicit because
  `blk_mem` supplies it where it is needed; the induced delivery below
  states it over arbitrary held ids, so it must be assumed. -/
  holds_sub : ∀ v t, holds v t ⊆ U.ids
  /-- A validator holds every block it authored, from the time it builds
  at that round. `ViewSync.holds_own` is this at `blk v n`. -/
  holds_own : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n → b ∈ holds v (built v n)
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  /-- **N2, as view convergence** (network). -/
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  /-- **P7, referencing** (protocol), over any block the validator authors
  at that round. `ViewSync.references` is this at `blk v (n+1)`. -/
  references : ∀ v ∈ T, ∀ n < N, ∀ c ∈ U.ids,
    (U.block c).creator = v → (U.block c).round = n + 1 →
    ∀ a ∈ holds v (built v (n + 1)), (U.block a).round = n →
    a ∈ (U.block c).refs
  /-- The seed: **one** populated round at the GST crossing. The
  induction below steps from `n` to `n+1` using only the previous round,
  so nothing is assumed about the rounds beneath `R` — which is the most
  that can be claimed, since `converges` is silent below `gst` and the
  network may deliver nothing there. The untimed route's counterpart is
  `Live.genesis`, at `R = 0`. -/
  base : PopulatedOn U T R
  /-- **P8, the build rule** (protocol). A validator holding a quorum of
  distinct authors at round `n`, among what it has in hand when it builds
  for round `n+1`, produces a block there. This is `Live.builds` with
  `D.accepted v n` replaced by the round-`n` part of the build-time
  view. -/
  builds : ∀ v ∈ T, ∀ n, R ≤ n → n < N →
    (Fintype.card Validator - F.f) ≤
      (creatorsOf U.block
        ((holds v (built v (n + 1))).filter fun b => (U.block b).round = n)).card →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n + 1
```

`ViewSync` with production removed and the build rule put in its place: the same network and protocol data, but the DAG's growth is a consequence rather than a hypothesis.

Everything except `blk` is `ViewSync`'s, with `holds_own` and `references` generalised off `blk` as described above, plus the two clauses the induction needs: a `base` populating the rounds up to `R`, and `builds`, the timed counterpart of `Live.builds`.

#### `toViewSync`

*def, `ViewSync.lean`*

```lean
noncomputable def toViewSync [Nonempty BlockId]
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn vg.built T R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n)
    (hbelow : ∀ n < R, PopulatedOn U T n) :
    ViewSync U T N :=
  let hb := exists_blk_of_populatedOn (U := U) (T := T) (N := N)
    (fun n hn => if h : R ≤ n then vg.populatedOn hcard hD hgst hbackoff n h hn
      else hbelow n (by omega))
  { blk := hb.choose
    built := vg.built
    timeout := vg.timeout
    gst := vg.gst
    delay := vg.delay
    rounds_le := vg.rounds_le
    blk_mem := hb.choose_spec.1
    blk_creator := hb.choose_spec.2.1
    blk_round := hb.choose_spec.2.2
    waits := fun v hv n _ => vg.waits v hv n
    timeout_pos := vg.timeout_pos
    latest := vg.latest
    built_le_latest := vg.built_le_latest
    latest_mem := vg.latest_mem
    prompt := vg.prompt
    holds := vg.holds
    holds_own := fun v hv n hn =>
      vg.holds_own v hv n hn _ (hb.choose_spec.1 v hv n hn)
        (hb.choose_spec.2.1 v hv n hn) (hb.choose_spec.2.2 v hv n hn)
    holds_mono := vg.holds_mono
    converges := vg.converges
    references := fun v hv n hn a ha har =>
      vg.references v hv n hn _ (hb.choose_spec.1 v hv (n + 1) (by omega))
        (hb.choose_spec.2.1 v hv (n + 1) (by omega))
        (hb.choose_spec.2.2 v hv (n + 1) (by omega)) a ha har }
```

**The unification.** A `ViewGrowth` *is* a `ViewSync`: production is recovered by Skolemising the population it derives, and the two clauses generalised off `blk` specialise back to it.

So the timed route no longer assumes what the untimed route proves. Every result of this file and of `Timing.lean` applies to a `ViewGrowth` through this reduction, with N1 absent from both routes.

#### `ViewsConvergeOn`

*def, `ViewSync.lean`*

```lean
def ViewsConvergeOn (D : Delivery U) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, R ≤ n → ∀ b ∈ D.held v n,
    (U.block b).creator ∈ T → b ∈ D.held w n
```

`ViewsConverge` relative to a set and a starting round: what a `T`-validator holds when it builds for round `n` is held by every `T`-validator when it builds for round `n`, for `T`-authored blocks from round `R` on.

#### `toDelivery`

*def, `ViewSync.lean`*

```lean
def toDelivery : Delivery U where
  held v n := (vg.holds v (vg.built v (n + 1))).filter
    fun b => (U.block b).round = n ∧ v ∈ T
  held_spec v n i hi := by
    simp only [Finset.mem_filter] at hi
    exact ⟨vg.holds_sub _ _ hi.1, hi.2.1⟩
  accepted v n := (vg.holds v (vg.built v (n + 1))).filter
    fun b => ((U.block b).round = n ∧ v ∈ T) ∧
      (U.block b).creator ∈ (Correct : Finset Validator)
  accepted_sub v n i hi := by
    simp only [Finset.mem_filter] at hi ⊢
    exact ⟨hi.1, hi.2.1⟩
  accepted_inj v n i hi j hj hij := by
    simp only [Finset.mem_filter] at hi hj
    exact U.eq_of_creator_eq (vg.holds_sub _ _ hi.1) (vg.holds_sub _ _ hj.1)
      hi.2.2 rfl hij.symm (by rw [hi.2.1.1, hj.2.1.1])
  accepts_correct v _ n a ha hac := by
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2, hac⟩
  includes v _ n b hb hbc hbr a ha := by
    simp only [Finset.mem_filter] at ha
    obtain ⟨hamem, ⟨har, hvT⟩, _⟩ := ha
    -- above the horizon there is no such `b`, so the clause is vacuous
    have hnN : n < N := by have := vg.rounds_le b hb; omega
    exact vg.references v hvT n hnN b hb hbc hbr a hamem har
```

**The delivery a timed structure induces.** `held` is the build-time view, cut to the round it is indexed by; `accepted` keeps the correct-authored part of it.

Accepting conservatively is what makes `accepted_inj` true rather than a further assumption: two accepted blocks share an author only if that author is correct, and non-equivocation then identifies them. Outside `T` and above the horizon the delivery is empty, which is the most that can be claimed — `converges` and `holds_own` quantify over `T`, and no block exists above `N`.

### Chain quality

#### `coveredAt`

*def, `Quality.Coverage.lean`*

```lean
def coveredAt (U : BlockUniverse Validator BlockId Payload)
    (b : BlockId) (δ : ℕ) : Finset Validator :=
  (Correct : Finset Validator).filter fun v =>
    ∃ i ∈ history U b, (U.block i).creator = v ∧ (U.block i).round = δ
```

The correct validators whose round-`δ` block a cone carries — the complement, within `Correct`, of `missingAt`.

#### `IncludesAt`

*def, `Quality.Inclusion.lean`*

```lean
def IncludesAt (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    [S : Slots Validator] (R m k : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
    (∀ r ≤ N, Populated U r) → Synchronised U R →
    S.slotRound k + 2 ≤ N →
    ∃ L, Decided U (View.full U) k (some L) ∧
      ∀ b ∈ U.ids,
        (U.block b).creator ∈ (Correct : Finset Validator) →
        (U.block b).round = m →
        b ∈ history U L ∧
        ∀ (g : ℕ → Option BlockId) (n : ℕ), g k = some L → k < n →
          b ∈ ledgerSet U g n
```

**A slot whose commit carries a whole round into the ledger.**

The conclusion CQ6 and its refinements share: in any sufficiently grown synchronous execution, slot `k` commits a leader whose history contains every correct round-`m` block, and every such block is in the agreed ledger from any later position. Naming it keeps the quantifier order visible — `k` is fixed by the schedule before an execution is named — as `CommitsAt` does for the recurrence results.

### Denial of service

#### `EquivPair`

*def, `DoS.Exposure.lean`*

```lean
def EquivPair (U : BlockUniverse Validator BlockId Payload) (X : Validator) (i j : BlockId) :
    Prop :=
  i ≠ j ∧ (U.block i).creator = X ∧ (U.block j).creator = X ∧
    (U.block i).round = (U.block j).round
```

Two ids witnessing an equivocation by `X`: distinct, both authored by `X`, both at one round.

Split out from `ExposedIn` so that D13 can quantify over the *same* witness condition with and without a view restriction.

#### `ExposedIn`

*def, `DoS.Exposure.lean`*

```lean
def ExposedIn (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (X : Validator) :
    Prop :=
  ∃ i ∈ history U b, ∃ j ∈ history U b, EquivPair U X i j
```

**`X` is exposed in `b`'s history**: two distinct blocks by `X` at one round lie below `b`.

Stated over `history` rather than over `Reaches` so that it is decidable and countable; `exposedIn_iff_reaches` gives the `Reaches` form for a block of the universe.

#### `DoSValid`

*def, `DoS.Exposure.lean`*

```lean
def DoSValid (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator
```

**The DoS-protection condition** (`dos-equivocation-and-growth.md` §3): a block may not reference an author exposed in its own history.

A predicate on the universe, deliberately **not** a field of `ValidWrt`. Every safety and liveness theorem in the development applies verbatim under it, because none of them mention it; results that need it take it as an extra hypothesis.

#### `historyBlocksOf`

*def, `DoS.Exposure.lean`*

```lean
def historyBlocksOf (U : BlockUniverse Validator BlockId Payload) (b : BlockId)
    (X : Validator) (n : ℕ) : Finset BlockId :=
  (history U b).filter (fun i => (U.block i).creator = X ∧ (U.block i).round = n)
```

The blocks of `b`'s history authored by `X` at round `n`. The thing the size results count.

#### `exposedTo`

*def, `DoS.Exposure.lean`*

```lean
def exposedTo (U : BlockUniverse Validator BlockId Payload) (b : BlockId) : Finset Validator :=
  Finset.univ.filter (fun X => ExposedIn U b X)
```

The authors a block's history has caught.

#### `missingAt`

*def, `DoS.Density.lean`*

```lean
def missingAt (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (δ : ℕ) :
    Finset Validator :=
  (Correct : Finset Validator).filter fun v =>
    ∀ i ∈ history U b, ¬ ((U.block i).creator = v ∧ (U.block i).round = δ)
```

The correct validators with no block at round `δ` in `b`'s history.

#### `atRound`

*def, `DoS.Counting.lean`*

```lean
def atRound (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) (n : ℕ) :
    Finset BlockId :=
  s.filter (fun i => (U.block i).round = n)
```

The blocks of `s` at round `n`. Generalises `blocksAt`, which is this at `s := U.ids`.

#### `EquivFree`

*def, `DoS.Counting.lean`*

```lean
def EquivFree (U : BlockUniverse Validator BlockId Payload) (s : Finset BlockId) : Prop :=
  ∀ i ∈ s, ∀ j ∈ s, (U.block i).creator = (U.block j).creator →
    (U.block i).round = (U.block j).round → i = j
```

No two distinct blocks of `s` share an author and a round.

A property of the **set**, not of the universe: `U` may be full of equivocations while a particular `s` is free of them, which is exactly the situation D8a describes.

#### `topsOf`

*def, `DoS.Adoption.lean`*

```lean
def topsOf (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (X : Validator) :
    Finset BlockId :=
  (history U b).filter fun t => (U.block t).creator = X ∧
    ∀ c ∈ history U b, (U.block c).creator = X → t ∉ (U.block c).refs
```

The chain tops of author `X` in `b`'s history: `X`-blocks with no `X`-authored child there. Chains being priced exactly (D22/D23), tops are what remains to count.

#### `AdoptedUnder`

*def, `DoS.Pedigree.lean`*

```lean
def AdoptedUnder (U : BlockUniverse Validator BlockId Payload) (b t T : BlockId) : Prop :=
  ∃ j ∈ history U b, j ∈ history U T ∧
    (U.block j).creator = (U.block T).creator ∧ t ∈ (U.block j).refs
```

`t` is adopted under `T`: some block of `T`'s own author, inside `T`'s history, references `t`. By D21/D22 such a block sits on `T`'s chain, so per (`T`, author-of-`t`) the adopted top is unique (`top_eq_of_mem_namer_history`).

#### `PedigreeTo`

*inductive, `DoS.Pedigree.lean`*

```lean
inductive PedigreeTo (U : BlockUniverse Validator BlockId Payload) (b : BlockId) :
    BlockId → List Validator → Prop
  | base : PedigreeTo U b b []
  | step {t T : BlockId} {l : List Validator} :
      t ∈ topsOf U b (U.block t).creator →
      AdoptedUnder U b t T →
      PedigreeTo U b T l →
      PedigreeTo U b t ((U.block T).creator :: l)
```

An adoption pedigree: the climb from a top to `b`, recording the adopters' authors.

#### `PedigreeVia`

*inductive, `DoS.Pedigree.lean`*

```lean
inductive PedigreeVia (U : BlockUniverse Validator BlockId Payload) (b : BlockId) :
    BlockId → BlockId → List Validator → Prop
  | base {t T : BlockId} :
      t ∈ topsOf U b (U.block t).creator → AdoptedUnder U b t T →
      PedigreeVia U b t T []
  | step {t T₁ T : BlockId} {l : List Validator} :
      t ∈ topsOf U b (U.block t).creator → AdoptedUnder U b t T₁ →
      PedigreeVia U b T₁ T l →
      PedigreeVia U b t T ((U.block T₁).creator :: l)
```

A pedigree anchored at an arbitrary block `T` rather than at `b`, recording only the *intermediate* adopters' authors.

#### `encodeList`

*def, `DoS.Pedigree.lean`*

```lean
def encodeList (E' : Finset Validator) (m : ℕ) (l : List Validator) :
    Fin m → Option {W // W ∈ E'} :=
  fun k => if hk : (k : ℕ) < l.length then
      if hmem : l[(k : ℕ)] ∈ E' then some ⟨l[(k : ℕ)], hmem⟩ else none
    else none
```

The padded encoding of a list of at most `m` members of `E'`: entry `k` is the `k`-th element when there is one, and `none` past the end.

Used to count lists by counting functions — a `Finset` of lists of bounded length has no convenient cardinality, whereas `Fin m → Option _` does.

#### `DoSAccepting`

*def, `DoS.Exclusion.lean`*

```lean
def DoSAccepting (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    ∀ i ∈ D.accepted v n, ¬ ExposedIn U b (U.block i).creator
```

The policy: nothing a correct validator accepts is exposed to the block it goes on to build.

#### `ReferencesAccepted`

*def, `DoS.Exclusion.lean`*

```lean
def ReferencesAccepted (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted v n
```

The tight half of `includes`: a correct validator references *exactly* what it accepted, no more. `Delivery.includes` gives the other inclusion, and D3's sharp bound wants both.

#### `HeldByCorrect`

*def, `DoS.Exclusion.lean`*

```lean
def HeldByCorrect (D : Delivery U) : Prop :=
  ∀ i ∈ U.ids, ∃ v ∈ (Correct : Finset Validator), i ∈ D.held v (U.block i).round
```

**What `U` means, made explicit.** §4.2 of `liveness.md` defines `U` as every block some correct validator held; the model has never said so.

#### `AcceptsSome`

*def, `DoS.Exclusion.lean`*

```lean
def AcceptsSome (D : Delivery U) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ a ∈ D.held v n,
    ∃ i ∈ D.accepted v n, (U.block i).creator = (U.block a).creator
```

**A stronger acceptance policy**: a validator that holds a block by some author accepts *some* block by that author. `Delivery.accepts_correct` demands this only of correct authors.

#### `Accepted`

*structure, `DoS.Acceptance.lean`*

```lean
structure Accepted (U : BlockUniverse Validator BlockId Payload)
    (A : Finset BlockId) (n : ℕ) : Prop where
  /-- Only real blocks are accepted. -/
  subset_ids : A ⊆ U.ids
  /-- One round: the frontier. -/
  round_eq : ∀ i ∈ A, (U.block i).round = n
  /-- At most one block per author — the rule. -/
  inj : ∀ i ∈ A, ∀ j ∈ A, (U.block i).creator = (U.block j).creator → i = j
```

What a validator has accepted at round `n`: real blocks of that round, at most one per author.

The injectivity field is the acceptance rule, and it is the only one D2 uses — the round field is what makes `A` a *frontier* rather than an accumulation, and is used by D3.

#### `View.ofAccepted`

*def, `DoS.Acceptance.lean`*

```lean
def View.ofAccepted (h : Accepted U A n) : View Validator BlockId Payload U where
  ids := A.biUnion (history U)
  subset_ids := by
    intro i hi
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    exact history_subset_ids (h.subset_ids ha) hia
  complete := by
    intro i hi j hj
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    have ha_ids : a ∈ U.ids := h.subset_ids ha
    refine Finset.mem_biUnion.mpr ⟨a, ha, ?_⟩
    exact (mem_history_iff ha_ids).mpr
      (((mem_history_iff ha_ids).mp hia).trans (Reaches.single hj))
```

**D1 — the view an accepted set generates.**

That this typechecks *is* the result: `complete` is discharged by transitivity of `Reaches`, so a union of causal histories is downward closed and no closure obligation has to be met by hand.

#### `novelty`

*def, `DoS.Novelty.lean`*

```lean
def novelty (U : BlockUniverse Validator BlockId Payload) (V : Finset BlockId)
    (b : BlockId) : Finset BlockId :=
  history U b \ V
```

What accepting `b` would newly bring into the view `V`.

#### `StepNovelty`

*def, `DoS.Novelty.lean`*

```lean
def StepNovelty (U : BlockUniverse Validator BlockId Payload) (κ' : ℕ) : Prop :=
  ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ p ∈ (U.block b).refs, (U.block p).creator = (U.block b).creator →
      (novelty U (history U p) b).card ≤ κ'
```

Stepwise novelty: every correct block adds at most `κ'` blocks over the history of its self-parent. For a correct author the self-parent is unique (`no_equivocation`), so the `∀` costs nothing.

#### `viewUpto`

*def, `DoS.Novelty.lean`*

```lean
def viewUpto (D : Delivery U) (v : Validator) : ℕ → Finset BlockId
  | 0 => (D.accepted v 0).biUnion (history U)
  | n + 1 => viewUpto D v n ∪ (D.accepted v (n + 1)).biUnion (history U)
```

Everything `v` has retained by round `n`: the whole histories of everything it accepted at any round up to `n` — the retained view of S1, accumulated. This is what novelty is measured against, and the reason C3 works: accepting a block means holding its entire cone.

#### `ByzBudget`

*def, `DoS.Novelty.lean`*

```lean
def ByzBudget (D : Delivery U) (κ : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (U.block b).creator ∉ (Correct : Finset Validator) →
    (novelty U (viewUpto D v n) b).card ≤ κ
```

The **analysis-side budget**: only the Byzantine clause. This is the weakest thing the theorems need — Byzantine-authored acceptances were affordable — and the correct clause is *derived* from it (`card_novelty_le_of_byzBudget`): a schedule keeping Byzantine acceptances under `κ` never carries a correct block over `f·κ + 1`. The creator guard is bookkeeping, never something a validator evaluates; the enforced form is `UniformBudget` below.

#### `UniformBudget`

*def, `DoS.Novelty.lean`*

```lean
def UniformBudget (D : Delivery U) (T : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (novelty U (viewUpto D v n) b).card ≤ T
```

**The mechanism-side budget** — the rule a validator actually runs: a guard-free cap on every acceptance, author-blind. Enforcing the cap on everyone enforces it on the Byzantine authors (`UniformBudget.byzBudget`), and post-`R` the converse holds at `f·κ + 1` (`uniform_of_byzBudget` below) — the two formulations sandwich within one factor of `f`, the exact price of author-blindness.

#### `viewGap`

*def, `DoS.Novelty.lean`*

```lean
def viewGap (D : Delivery U) (v w : Validator) (n : ℕ) : Finset BlockId :=
  viewUpto D w n \ viewUpto D v n
```

The standing divergence between two correct validators' retained views: what `w` holds that `v` does not.

#### `RefsAccepted`

*def, `DoS.Novelty.lean`*

```lean
def RefsAccepted (D : Delivery U) : Prop :=
  ∀ w ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = w → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted w n
```

D3's ordinary case as a protocol property: a correct validator's block references **only** what it accepted — the converse of `includes`; together they say `refs = accepted`.

#### `byzPool`

*def, `DoS.Novelty.lean`*

```lean
def byzPool (D : Delivery U) (n : ℕ) : Finset BlockId :=
  (Correct : Finset Validator).biUnion fun w =>
    (viewUpto D w n).filter
      fun i => (U.block i).creator ∉ (Correct : Finset Validator)
```

The **global Byzantine pool**: every Byzantine-authored block sitting in any correct validator's retained view.

#### `AllExposed`

*def, `DoS.Composition.lean`*

```lean
def AllExposed (U : BlockUniverse Validator BlockId Payload) (m : ℕ) : Prop :=
  ∀ X : Validator, X ∉ (Correct : Finset Validator) →
    ∀ c ∈ U.ids, (U.block c).round = m + 1 →
      (U.block c).creator ∈ (Correct : Finset Validator) → ExposedIn U c X
```

**Exposure-complete at `m`**: every correct block of round `m+1` is exposed to every Byzantine author — the state D16 manufactures once all `f` authors have equivocated toward the correct population.

### Garbage collection

#### `chopBlock`

*def, `GC.Chop.lean`*

```lean
def chopBlock (U : BlockUniverse Validator BlockId Payload) (G : ℕ)
    (i : BlockId) : Block Validator BlockId Payload :=
  if (U.block i).round ≤ G then
    { U.block i with round := (U.block i).round - G, refs := ∅ }
  else
    { U.block i with round := (U.block i).round - G }
```

One block of the truncation: the round is rebased by `−G`, and blocks at or below the cut — the new base layer, plus junk — lose their references.

#### `chop`

*def, `GC.Chop.lean`*

```lean
def chop (U : BlockUniverse Validator BlockId Payload) (G : ℕ) :
    BlockUniverse Validator BlockId Payload where
  ids := U.ids.filter fun i => G ≤ (U.block i).round
  block := chopBlock U G
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlock_refs_of_lt h] at hj
      have hj_ids := U.complete i hi.1 j hj
      have hj_round := U.round_of_mem_refs hi.1 hj
      exact Finset.mem_filter.mpr ⟨hj_ids, by omega⟩
    · rw [chopBlock_refs_of_le h] at hj
      exact absurd hj (Finset.notMem_empty j)
  valid := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hv := U.valid i hi.1
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    swap
    · -- the new base layer (and junk): no references, nothing to prove
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
          | (intro j hj
             rw [chopBlock_refs_of_le h] at hj
             exact absurd hj (Finset.notMem_empty j))
          | (intro hr
             rw [chopBlock_round] at hr
             omega)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- predecessor, rebased
        intro j hj
        rw [chopBlock_refs_of_lt h] at hj
        have := hv.predecessor j hj
        rw [chopBlock_round, chopBlock_round]
        omega
      · -- distinct creators, untouched
        intro a ha b hb hab
        rw [chopBlock_refs_of_lt h] at ha hb
        rw [chopBlock_creator, chopBlock_creator] at hab
        exact hv.distinct_creators a ha b hb hab
      · -- quorum, untouched
        intro _
        have hcr : creators (chopBlock U G) (chopBlock U G i) =
            creators U.block (U.block i) := by
          unfold creators
          rw [chopBlock_refs_of_lt h, creatorsOf_chopBlock]
        rw [hcr]
        exact hv.quorum (by omega)
      · -- self-parent, untouched
        intro _
        obtain ⟨p, hp, hpc⟩ := hv.self_parent (by omega)
        refine ⟨p, ?_, ?_⟩
        · rw [chopBlock_refs_of_lt h]; exact hp
        · rw [chopBlock_creator, chopBlock_creator]; exact hpc
  no_equivocation := by
    intro i hi j hj hic hcreator hround
    rw [Finset.mem_filter] at hi hj
    rw [chopBlock_creator] at hic hcreator
    rw [chopBlock_creator] at hcreator
    rw [chopBlock_round, chopBlock_round] at hround
    exact U.no_equivocation i hi.1 j hj.1 hic hcreator (by omega)
```

**The horizon** (`garbage.md` §2): the universe above the cut, rounds rebased, the round-`G` layer as the new geneses.

#### `View.chop`

*def, `GC.ChopDecided.lean`*

```lean
def View.chop (V : View Validator BlockId Payload U) (G : ℕ) :
    View Validator BlockId Payload (chop U G) where
  ids := V.ids.filter fun i => G ≤ (U.block i).round
  subset_ids := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact mem_chop_ids.mpr ⟨V.subset_ids hi.1, hi.2⟩
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rw [chop_block_eq] at hj
    rcases Nat.lt_or_ge G (U.block i).round with hlt | hge
    · rw [chopBlock_refs_of_lt hlt] at hj
      have := U.round_of_mem_refs (V.subset_ids hi.1) hj
      exact Finset.mem_filter.mpr ⟨V.complete i hi.1 j hj, by omega⟩
    · rw [chopBlock_refs_of_le hge] at hj
      simp at hj
```

A validator's view, truncated at the horizon: keep what clears the cut. Closure survives: a retained block's references sit one round below it, hence at or above the cut — except at the base layer, where they are gone.

#### `Slots.chop`

*def, `GC.ChopDecided.lean`*

```lean
def Slots.chop (S : Slots Validator) (G d : ℕ) (hd : G ≤ S.slotRound d) :
    Slots Validator where
  slotRound k := S.slotRound (d + k) - G
  leader k := S.leader (d + k)
  mono _ _ h := Nat.sub_le_sub_right (S.mono (Nat.add_le_add_left h d)) G
  unbounded := by
    intro n
    obtain ⟨k, hk⟩ := S.unbounded (G + n)
    rcases Nat.le_total k d with hkd | hdk
    · refine ⟨0, ?_⟩
      have := S.mono hkd
      simp only [Nat.add_zero]
      omega
    · refine ⟨k - d, ?_⟩
      have hcancel : d + (k - d) = k := by omega
      simp only [hcancel]
      omega
  keyed := by
    intro k₁ k₂ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hr, hl⟩ := h
    have h₁ := hd.trans (S.mono (Nat.le_add_right d k₁))
    have h₂ := hd.trans (S.mono (Nat.le_add_right d k₂))
    have hpair : (S.slotRound (d + k₁), S.leader (d + k₁))
        = (S.slotRound (d + k₂), S.leader (d + k₂)) := by
      have : S.slotRound (d + k₁) = S.slotRound (d + k₂) := by omega
      rw [this, hl]
    have := S.keyed hpair
    omega
```

The truncation's slot schedule: slots re-indexed from a base slot `d` whose round clears the horizon, rounds rebased by `−G`. The base-slot condition keeps subtraction faithful, which is what keying needs.

#### `chopD`

*def, `GC.Window.lean`*

```lean
def chopD (D : Delivery U) (G : ℕ) : Delivery (chop U G) where
  held v m := D.held v (G + m)
  held_spec := by
    intro v m i hi
    obtain ⟨h1, h2⟩ := D.held_spec v (G + m) i hi
    refine ⟨mem_chop_ids.mpr ⟨h1, by omega⟩, ?_⟩
    rw [chop_block_eq, chopBlock_round]
    omega
  accepted v m := D.accepted v (G + m)
  accepted_sub v m := D.accepted_sub v (G + m)
  accepted_inj := by
    intro v m i hi j hj hij
    rw [chop_block_eq, chopBlock_creator, chopBlock_creator] at hij
    exact D.accepted_inj v (G + m) i hi j hj hij
  accepts_correct := by
    intro v hv m a ha hac
    rw [chop_block_eq, chopBlock_creator] at hac
    exact D.accepts_correct v hv (G + m) a ha hac
  includes := by
    intro v hv m b hb hbc hbr
    rw [mem_chop_ids] at hb
    rw [chop_block_eq, chopBlock_creator] at hbc
    rw [chop_block_eq, chopBlock_round] at hbr
    have hsub := D.includes v hv (G + m) b hb.1 hbc (by omega)
    intro i hi
    rw [chop_block_eq, chopBlock_refs_of_lt (by omega)]
    exact hsub hi
```

A delivery for the truncation: round `m` of the window is round `G + m` of the original. Nothing below the cut is consulted.

#### `attesters`

*def, `GC.AttestedBase.lean`*

```lean
def attesters (U : BlockUniverse Validator BlockId Payload) (t : ℕ)
    (y : BlockId) : Finset Validator :=
  creatorsOf U.block ((blocksAt U t).filter fun a => y ∈ history U a)
```

The authors attesting `y` at round `t`: those with a round-`t` block whose cone holds `y`. An author's block *is* its attestation.

#### `Base`

*def, `GC.AttestedBase.lean`*

```lean
def Base (U : BlockUniverse Validator BlockId Payload) (t G : ℕ) :
    Finset BlockId :=
  (blocksAt U G).filter fun y => F.f + 1 ≤ (attesters U t y).card
```

**The inexact certificate**: the round-`G` blocks attested by more than `f` distinct authors at round `t`.

#### `joinIds`

*def, `GC.Bootstrap.lean`*

```lean
def joinIds (D : Delivery U) (w : Validator) (m t G : ℕ) : Finset BlockId :=
  Base U t G ∪ ((viewUpto D w m).filter fun i => G < (U.block i).round)
```

What a joiner fetches: the attested base as its genesis layer, plus a correct peer's window strictly above the cut, up to frontier `m`. The round-`G` layer comes **only** from the base — that is the rebasing.

#### `joinView`

*def, `GC.Bootstrap.lean`*

```lean
def joinView {R m t : ℕ} (hs : Synchronised U R)
    (hw : w ∈ (Correct : Finset Validator)) (hcar : Populated U (m + 1))
    (hpop : Populated U t) (hR : R ≤ m + 1) (hmt : m + 2 ≤ t) :
    View Validator BlockId Payload (chop U G) where
  ids := joinIds D w m t G
  subset_ids := by
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨⟨hids, hround⟩, -⟩ := mem_base.mp h
      exact mem_chop_ids.mpr ⟨hids, by omega⟩
    · obtain ⟨hiv, hround⟩ := Finset.mem_filter.mp h
      exact mem_chop_ids.mpr ⟨viewUpto_subset_ids hiv, by omega⟩
  complete := by
    intro i hi j hj
    rw [chop_block_eq] at hj
    rcases Finset.mem_union.mp hi with h | h
    · obtain ⟨⟨hids, hround⟩, -⟩ := mem_base.mp h
      rw [chopBlock_refs_of_le (by omega)] at hj
      simp at hj
    · obtain ⟨hiv, hround⟩ := Finset.mem_filter.mp h
      have hiids : i ∈ U.ids := viewUpto_subset_ids hiv
      rw [chopBlock_refs_of_lt hround] at hj
      have hjv : j ∈ viewUpto D w m := mem_viewUpto_of_mem_refs hiv hj
      have hjr : (U.block j).round + 1 = (U.block i).round :=
        U.round_of_mem_refs hiids hj
      rcases Nat.lt_or_ge G (U.block j).round with hlt | hge
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hjv, hlt⟩)
      · exact Finset.mem_union_left _
          (accepted_mem_base hs hw hjv (by omega) hcar hpop hR hmt)
```

**G12, the assembly.** Base plus window is a bona-fide view of the truncation. Closure is the whole content: a window reference above the cut is in the window (stores are reference-closed), and a window reference *at* the cut is a round-`G` block the peer accepted — which is exactly what G11 puts in the base. The base layer itself has no references to chase: `chop` made it the genesis layer.

### Odontoceti

#### `Faults5`

*class, `Odontoceti.Rules.lean`*

```lean
class Faults5 (Validator : Type*) [Fintype Validator] [DecidableEq Validator]
    extends Faults Validator where
  /-- There are at least `5f+1` validators. -/
  card_validators5 : 5 * f + 1 ≤ Fintype.card Validator
```

The Odontoceti committee: `n ≥ 5f+1`. An extension of `Faults`, so every existing theorem applies to the same types unchanged; the new bound is consumed only where the two-round arithmetic needs it.

#### `DirectCommit`

*def, `Odontoceti.Rules.lean`*

```lean
def DirectCommit (U : BlockUniverse Validator BlockId Payload)
    (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (supporters U L (r + 1)).card
```

**Direct commit**: a quorum of distinct authors support `L` at its decision round.

#### `DirectSkip`

*def, `Odontoceti.Rules.lean`*

```lean
def DirectSkip (U : BlockUniverse Validator BlockId Payload)
    (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (blames U L (r + 1)).card
```

**Direct skip**: a quorum of distinct authors blame `L` at its decision round.

#### `coneSupports`

*def, `Odontoceti.Rules.lean`*

```lean
def coneSupports (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Finset Validator :=
  creatorsOf U.block
    ((blocksAt U (r + 1)).filter
      (fun q => L ∈ (U.block q).refs ∧ q ∈ history U A))
```

The authors of decision-round support blocks for `L` visible in `A`'s cone. Counted by **distinct authors**, not raw blocks: an equivocating supporter can plant any number of support-twins in a cone, so the block count is adversary-inflatable; the author count is the one the arithmetic on both sides actually bounds.

#### `ThickLink`

*def, `Odontoceti.Rules.lean`*

```lean
def ThickLink (U : BlockUniverse Validator BlockId Payload)
    (A L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - 3 * F.f) ≤ (coneSupports U A L r).card
```

**The indirect test** (the thesis's ThickLink): at least `n − 3f` distinct authors of support blocks for `L` in the anchor's cone. At `n = 5f+1` this is the thesis's `2f+1`.

#### `decisionRound`

*def, `Odontoceti.Decision.lean`*

```lean
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 1
```

The round at which a slot's verdict is settled: its supports live here. One round, not two — there is no certificate round.

#### `Eligible`

*def, `Odontoceti.Decision.lean`*

```lean
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j
```

`j` may anchor `k`: its proposal lies past `k`'s decision round. A predicate on the slot pair alone — which is what lets the agreement induction match two validators' premises against each other.

#### `supportersIn`

*def, `Odontoceti.Decision.lean`*

```lean
def supportersIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun q => L ∈ (U.block q).refs)) ∩ V.ids)
```

The supporters a view actually holds.

#### `blamesIn`

*def, `Odontoceti.Decision.lean`*

```lean
def blamesIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun q => L ∉ (U.block q).refs)) ∩ V.ids)
```

The blamers a view actually holds.

#### `DirectCommitIn`

*def, `Odontoceti.Decision.lean`*

```lean
def DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (supportersIn U V L r).card
```

Direct commit, as judged from a single view.

#### `DirectSkipIn`

*def, `Odontoceti.Decision.lean`*

```lean
def DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  (Fintype.card Validator - F.f) ≤ (blamesIn U V L r).card
```

Direct skip, as judged from a single view.

#### `Decided`

*inductive, `Odontoceti.Decision.lean`*

```lean
inductive Decided (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      Decided U V k (some L)
  /-- The direct rule blames every candidate — vacuously, when the
  leader produced nothing. -/
  | directSkip {k : ℕ} :
      (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      Decided U V k none
  /-- Anchored on the nearest eligible committed slot, the least
  candidate passing the indirect test is committed. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      IsLeaderBlock U k L → ThickLink U A L (S.slotRound k) →
      (∀ L', IsLeaderBlock U k L' → ThickLink U A L' (S.slotRound k) →
        ¬ L' < L) →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate
  passes the indirect test. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ ThickLink U A L (S.slotRound k)) →
      Decided U V k none
```

`Decided U V k v` — a validator holding `V` has settled slot `k`.

Mirrors Mysticeti's relation: the anchor is the **nearest eligible** committed slot (the intermediate premise, stated positively), and the skip case quantifies over all candidate blocks. The one new element is the canonicity premise on `indirectCommit` — the committed candidate is the `≤`-least one passing the test at the anchor — which is the implementation's deterministic iteration order made explicit; see the module docstring for why agreement is unprovable without it.

#### `SpansEligible`

*def, `Odontoceti.Liveness.lean`*

```lean
def SpansEligible (c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator i (b + c - 1)
```

A run of `c` slots reaches past everything below it: the last slot of a run starting at `b` is an eligible anchor for every slot below `b`.


---

## Appendix C. The theorem reference

The 147 theorems that another module of the development
depends on: the results the rest of the report reasons with, as
opposed to the steps internal to one file. Each is the source
statement, unabridged. Generated with Appendix B.

### The validator set and the fault model

#### `mem_correct`

*theorem, `Validators.lean`*

```lean
theorem mem_correct {v : Validator} : v ∈ (Correct : Finset Validator) ↔ v ∉ F.byzantine
```

Correctness is the complement of the Byzantine set.

#### `card_correct_add_byzantine`

*theorem, `Validators.lean`*

```lean
theorem card_correct_add_byzantine :
    (Correct : Finset Validator).card + F.byzantine.card = Fintype.card Validator
```

The correct and Byzantine validators partition the whole set.

Stated additively so it yields both bounds without ℕ subtraction. The *upper* bound on `Correct.card` is the one the counting arguments need — they divide an incidence count by the number of correct validators, for which a lower bound is useless.

#### `card_correct`

*theorem, `Validators.lean`*

```lean
theorem card_correct : Fintype.card Validator - F.f ≤ (Correct : Finset Validator).card
```

The correct validators alone meet the quorum threshold: at least `n − f` of them. This is what the threshold `n − f` is *for* — the correct pool suffices on its own.

#### `two_f_add_one_le_card_correct`

*theorem, `Validators.lean`*

```lean
theorem two_f_add_one_le_card_correct :
    2 * F.f + 1 ≤ (Correct : Finset Validator).card
```

At least `2f+1` validators are correct — the `n = 3f+1` reading of `card_correct`, kept for arguments that count in `f` alone.

#### `exists_correct_of_card`

*theorem, `Validators.lean`*

```lean
theorem exists_correct_of_card {S : Finset Validator} (h : F.f + 1 ≤ S.card) :
    ∃ v ∈ S, v ∈ (Correct : Finset Validator)
```

Any set of more than `f` validators contains a correct one, since the Byzantine validators number at most `f`.

#### `card_le_card_inter_correct_add_byzantine`

*theorem, `Validators.lean`*

```lean
theorem card_le_card_inter_correct_add_byzantine (S : Finset Validator) :
    S.card ≤ (S ∩ (Correct : Finset Validator)).card + F.byzantine.card
```

Byzantine validators can absorb at most `f` of any set: removing the correct members of `S` leaves something no bigger than the Byzantine set.

The workhorse behind "a quorum still contains many correct validators". Stated additively so it composes without ℕ subtraction.

#### `card_inter_correct_of_quorum`

*theorem, `Validators.lean`*

```lean
theorem card_inter_correct_of_quorum {S : Finset Validator}
    (h : Fintype.card Validator - F.f ≤ S.card) :
    F.f + 1 ≤ (S ∩ (Correct : Finset Validator)).card
```

A quorum contains at least `f+1` *correct* validators: `(n − f) − f = n − 2f ≥ f+1`.

The cardinality strengthening of `exists_correct_of_card`, which only produces one.

#### `exists_correct_mem_inter`

*theorem, `Validators.lean`*

```lean
theorem exists_correct_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : Fintype.card Validator - F.f ≤ Q₁.card)
    (h₂ : Fintype.card Validator - F.f ≤ Q₂.card) :
    ∃ v ∈ Q₁ ∩ Q₂, v ∈ (Correct : Finset Validator)
```

**T0.** Two quorums always share a *correct* validator. This is the form every later proof cites.

### Blocks, validity, and the universe

#### `mem_creatorsOf`

*theorem, `Block.lean`*

```lean
theorem mem_creatorsOf {blk : BlockId → Block Validator BlockId Payload}
    {s : Finset BlockId} {v : Validator} :
    v ∈ creatorsOf blk s ↔ ∃ i ∈ s, (blk i).creator = v
```

Membership in `creatorsOf`, unfolded: a validator is a creator of a set of ids exactly when it authored one of them.

#### `nonempty_of_creatorsOf_card_pos`

*theorem, `Block.lean`*

```lean
theorem nonempty_of_creatorsOf_card_pos {blk : BlockId → Block Validator BlockId Payload}
    {s : Finset BlockId} (h : 0 < (creatorsOf blk s).card) : s.Nonempty
```

A nonempty creator set can only come from a nonempty set of ids: the image of `∅` is `∅`.

Small, but it was inlined in three places — `ValidWrt.refs_nonempty` here, and the two "a quorum implies at least one block" steps in `Persistence` and `Mysticeti`.

#### `refs_empty_of_round_zero`

*theorem, `Block.lean`*

```lean
theorem refs_empty_of_round_zero (h : ValidWrt blk b) (h0 : b.round = 0) : b.refs = ∅
```

Genesis blocks have no references — derived from the predecessor condition, not assumed.

#### `refs_nonempty`

*theorem, `Block.lean`*

```lean
theorem refs_nonempty (h : ValidWrt blk b) (h0 : 0 < b.round) : b.refs.Nonempty
```

A non-genesis block has at least one reference. Used by T3's inductive step, which needs only this much of validity.

Proved from the quorum condition **alone**, deliberately not via `card_refs`: the image of `∅` is `∅`, so an empty `refs` would give an empty creator set. Routing through `card_refs` would drag `distinct_creators` onto T3's dependency path, and the whole point of §3.2's analysis is that Phase 1 and 1b never need it.

#### `exists_correct_mem_creators_inter`

*theorem, `Block.lean`*

```lean
theorem exists_correct_mem_creators_inter
    {blk : BlockId → Block Validator BlockId Payload} {s t : Finset BlockId}
    (hs : (Fintype.card Validator - F.f) ≤ (creatorsOf blk s).card)
    (ht : (Fintype.card Validator - F.f) ≤ (creatorsOf blk t).card) :
    ∃ v ∈ creatorsOf blk s ∩ creatorsOf blk t, v ∈ (Correct : Finset Validator)
```

**T0'.** Two id-sets whose creator sets are quorums share a *correct* author.

Stated on bare `Finset BlockId`s rather than on blocks, because that is what every call site needs: T3 intersects a block's refs with an arbitrary set `Q`, and T5 intersects two arbitrary sets, neither of which is any block's refs. For a block, apply it with `s := b.refs` and discharge the hypothesis with `ValidWrt.quorum`.

#### `eq_of_creator_eq`

*theorem, `BlockDag.lean`*

```lean
theorem eq_of_creator_eq {v : Validator} {i j : BlockId}
    (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∈ (Correct : Finset Validator))
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) :
    i = j
```

**T1.** A correct validator authors at most one block per round, so two ids in the universe with the same correct author and the same round are the *same id*.

Phrased around the author `v` rather than around `(U.block i).creator`, because that is how every use site arrives: a quorum intersection yields a correct validator, and T1 turns two blocks known to be authored by it into a single concrete id.

#### `round_of_mem_refs`

*theorem, `BlockDag.lean`*

```lean
theorem round_of_mem_refs {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ (U.block i).refs) :
    (U.block j).round + 1 = (U.block i).round
```

A reference sits in the round immediately below its referrer.

#### `creators_quorum`

*theorem, `BlockDag.lean`*

```lean
theorem creators_quorum {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (U.block i).refs).card
```

References of a non-genesis block carry a quorum of distinct authors. This is the hypothesis T0' consumes.

#### `refs_nonempty`

*theorem, `BlockDag.lean`*

```lean
theorem refs_nonempty {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    (U.block i).refs.Nonempty
```

A non-genesis block references at least one block.

#### `exists_common_mem_of_quorums`

*theorem, `BlockDag.lean`*

```lean
theorem exists_common_mem_of_quorums {s t : Finset BlockId} {n : ℕ}
    (hs : ∀ q ∈ s, q ∈ U.ids ∧ (U.block q).round = n)
    (ht : ∀ q ∈ t, q ∈ U.ids ∧ (U.block q).round = n)
    (hsq : (Fintype.card Validator - F.f) ≤ (creatorsOf U.block s).card)
    (htq : (Fintype.card Validator - F.f) ≤ (creatorsOf U.block t).card) :
    ∃ q, q ∈ s ∧ q ∈ t
```

**Two quorum-backed sets of round-`n` blocks must share a block.**

T0' gives a correct author common to both creator sets, and T1 makes that author's round-`n` block unique — so the two blocks it contributes coincide.

This is the recurring "peel off one certification layer" step: it is exactly what M5′ does to two certificates' vote sets, and what M5 would otherwise do a second time to two certificate sets.

### Causal structure

#### `refl`

*theorem, `CausalHistory.lean`*

```lean
theorem refl {c : BlockId} : Reaches U c c
```

Every block is in its own causal history.

#### `single`

*theorem, `CausalHistory.lean`*

```lean
theorem single {i j : BlockId} (h : j ∈ (U.block i).refs) : Reaches U i j
```

A direct reference is one step of causal history.

#### `trans`

*theorem, `CausalHistory.lean`*

```lean
theorem trans {a b c : BlockId} (h₁ : Reaches U a b) (h₂ : Reaches U b c) : Reaches U a c
```

Causal history composes. This is what glues `c → i` onto `i` reaches `b` at the end of both branches of T3.

#### `of_mem_refs`

*theorem, `CausalHistory.lean`*

```lean
theorem of_mem_refs {i j b : BlockId} (hij : j ∈ (U.block i).refs) (hjb : Reaches U j b) :
    Reaches U i b
```

Prepend a direct reference: if `i` references `j` and `j` reaches `b`, then `i` reaches `b`. The exact shape T3's inductive step needs.

#### `mem_ids_of_reaches`

*theorem, `CausalHistory.lean`*

```lean
theorem mem_ids_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) : b ∈ U.ids
```

Causal history stays inside the universe: completeness propagates along every step.

#### `eq_of_reaches_of_refs_empty`

*theorem, `CausalHistory.lean`*

```lean
theorem eq_of_reaches_of_refs_empty {c b : BlockId} (hc : (U.block c).refs = ∅)
    (h : Reaches U c b) : b = c
```

A block with no references reaches only itself. In particular genesis blocks (§3.2, `refs_empty_of_round_zero`) are causal-history leaves.

#### `round_le_of_reaches`

*theorem, `CausalHistory.lean`*

```lean
theorem round_le_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    (U.block b).round ≤ (U.block c).round
```

**T2.** Causal history runs downward in rounds: anything `c` reaches sits at a round no greater than `c`'s.

This is the substantive half of T2 — reflexivity, single steps and transitivity are inherited from `ReflTransGen`. It rests on §3.2's predecessor condition, applied at each step to an intermediate id that `mem_ids_of_reaches` keeps inside the universe.

#### `mem_history_iff`

*theorem, `History.lean`*

```lean
theorem mem_history_iff {b i : BlockId} (hb : b ∈ U.ids) :
    i ∈ history U b ↔ Reaches U b i
```

**The representation is faithful** (§7 S6). For a block of the universe, membership of `history` and reachability are the same thing.

#### `mem_history_self`

*theorem, `History.lean`*

```lean
theorem mem_history_self {b : BlockId} : b ∈ history U b
```

A block lies in its own causal history.

#### `history_subset_ids`

*theorem, `History.lean`*

```lean
theorem history_subset_ids {b : BlockId} (hb : b ∈ U.ids) : history U b ⊆ U.ids
```

Histories stay inside the universe.

#### `history_subset_of_reaches`

*theorem, `History.lean`*

```lean
theorem history_subset_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    history U b ⊆ history U c
```

Histories nest along reachability — the `Finset` form of transitivity, and what makes D12 one line.

#### `mem_history_succ_iff`

*theorem, `History.lean`*

```lean
theorem mem_history_succ_iff {b : BlockId} (hb : b ∈ U.ids) {i : BlockId} :
    i ∈ history U b ↔ i = b ∨ ∃ j ∈ (U.block b).refs, i ∈ history U j
```

The one-step unfolding: a history is its block, plus the histories of its references. The fuel bookkeeping is what makes this need a proof rather than `rfl` — the recursion hands out `round b` steps, and each reference wants `round + 1` of its own, which the predecessor condition reconciles.

#### `round_le_of_mem_history`

*theorem, `History.lean`*

```lean
theorem round_le_of_mem_history {b i : BlockId} (hb : b ∈ U.ids) (hi : i ∈ history U b) :
    (U.block i).round ≤ (U.block b).round
```

Causal history runs downward (T2), in the `Finset` form.

#### `eq_of_mem_history_of_round_eq`

*theorem, `History.lean`*

```lean
theorem eq_of_mem_history_of_round_eq {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round = (U.block b).round) : i = b
```

Nothing in a block's history sits at the block's own round except the block itself: a reference step drops the round strictly.

#### `mem_refs_of_mem_history_of_round_succ`

*theorem, `History.lean`*

```lean
theorem mem_refs_of_mem_history_of_round_succ {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round + 1 = (U.block b).round) :
    i ∈ (U.block b).refs
```

**The layer one below is exactly the reference set.** Anything in `b`'s history at round `round b - 1` is a direct reference of `b`.

#### `mem_history_of_mem_refs`

*theorem, `History.lean`*

```lean
theorem mem_history_of_mem_refs {b j : BlockId} (hb : b ∈ U.ids) (hj : j ∈ (U.block b).refs) :
    j ∈ history U b
```

A block's references lie in its history, one step down.

#### `mem_blocksAt`

*theorem, `Support.lean`*

```lean
theorem mem_blocksAt {i : BlockId} {n : ℕ} :
    i ∈ blocksAt U n ↔ i ∈ U.ids ∧ (U.block i).round = n
```

Membership in `blocksAt`, unfolded.

#### `mem_authorsAt`

*theorem, `Support.lean`*

```lean
theorem mem_authorsAt {v : Validator} {n : ℕ} :
    v ∈ authorsAt U n ↔ ∃ i ∈ U.ids, (U.block i).round = n ∧ (U.block i).creator = v
```

Membership in `authorsAt`, unfolded: an author of a round is anyone with a block there.

#### `creators_refs_subset_authorsAt`

*theorem, `Support.lean`*

```lean
theorem creators_refs_subset_authorsAt {c : BlockId} {n : ℕ}
    (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    creatorsOf U.block (U.block c).refs ⊆ authorsAt U n
```

The creators of a round-`(n+1)` block's references all hold round-`n` blocks. This is what confines a round-`(r+2)` block's choices to the same pool the threshold is measured against.

#### `exists_mem_refs_of_correct_support_of_card`

*theorem, `Support.lean`*

```lean
theorem exists_mem_refs_of_correct_support_of_card
    {P : BlockId → Prop} {n : ℕ} {T : Finset Validator}
    (hT : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = n ∧ P q ∧ (U.block q).creator = v)
    (hT_correct : ∀ v ∈ T, v ∈ (Correct : Finset Validator))
    (hcard : F.f + 1 ≤ T.card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    ∃ q ∈ (U.block c).refs, P q
```

**The hitting lemma, uniform form.** `f+1` correct backers always suffice: a round-`(n+1)` block names `n - f` of at most `n` participating authors, so it misses at most `f`.

#### `reaches_pred_of_round_le`

*theorem, `Support.lean`*

```lean
theorem reaches_pred_of_round_le {P : BlockId → Prop} {N : ℕ}
    (hbase : ∀ c ∈ U.ids, (U.block c).round = N → ∃ b, P b ∧ Reaches U c b)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : N ≤ (U.block c).round) :
    ∃ b, P b ∧ Reaches U c b
```

**Propagation.** Reaching something is inherited upward: if every block at round `N` reaches a `P`-block, so does every block above `N`.

Shared by T3 and M2, both of which are otherwise just a base case. The step needs nothing but nonempty references and transitivity — height is carried by `Reaches` alone.

#### `reaches_of_correct_support`

*theorem, `Support.lean`*

```lean
theorem reaches_of_correct_support
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ q ∈ U.ids,
      (U.block q).round = r + 1 ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v)
    (hS_correct : ∀ v ∈ S, v ∈ (Correct : Finset Validator))
    (hp : (authorsAt U (r + 1)).card + F.f + 1 ≤ S.card + Fintype.card Validator)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b
```

**Coverage, participation-sensitive form.** A block backed by `p + f + 1 - n` correct round-`(r+1)` validators is reached by every round-`(r+2)` block.

The `P`-instance of the hitting lemma where every target references `b`.

#### `reaches_of_correct_support_of_card`

*theorem, `Support.lean`*

```lean
theorem reaches_of_correct_support_of_card
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ q ∈ U.ids,
      (U.block q).round = r + 1 ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v)
    (hS_correct : ∀ v ∈ S, v ∈ (Correct : Finset Validator))
    (hcard : F.f + 1 ≤ S.card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b
```

**Coverage, uniform form.** `f+1` correct supporters always suffice.

This is the form to use when supporters come from a quorum rather than from counting — see T3, where n−f distinct creators contain `f+1` correct ones by `card_inter_correct_of_quorum`.

#### `mem_supporters`

*theorem, `Support.lean`*

```lean
theorem mem_supporters {b : BlockId} {n : ℕ} {v : Validator} :
    v ∈ supporters U b n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v
```

Membership in `supporters`, unfolded: a supporter has a round-`n` block referencing `b`.

#### `correctSupporters_subset`

*theorem, `Support.lean`*

```lean
theorem correctSupporters_subset {b : BlockId} {n : ℕ} :
    correctSupporters U b n ⊆ supporters U b n
```

Correct supporters are supporters.

#### `correctSupporters_correct`

*theorem, `Support.lean`*

```lean
theorem correctSupporters_correct {b : BlockId} {n : ℕ} {v : Validator}
    (hv : v ∈ correctSupporters U b n) : v ∈ (Correct : Finset Validator)
```

And they are correct.

#### `mem_blames`

*theorem, `Support.lean`*

```lean
theorem mem_blames {L : BlockId} {n : ℕ} {v : Validator} :
    v ∈ blames U L n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ L ∉ (U.block q).refs ∧ (U.block q).creator = v
```

Membership in `blames`, unfolded: a blamer has a round-`n` block that omits `L`.

#### `card_supporters_le_of_card_blames`

*theorem, `Support.lean`*

```lean
theorem card_supporters_le_of_card_blames {L : BlockId} {n : ℕ}
    (h : (Fintype.card Validator - F.f) ≤ (blames U L n).card) :
    (supporters U L n).card ≤ 2 * F.f
```

**The counting core of M3.** A quorum of blamers caps the supporters at `2f`, one short of a quorum.

A correct validator sits on at most one side, so the overlap is confined to the Byzantine set: `|supporters| ≤ (3f+1) − (2f+1) + f = 2f`. Nothing about certificates enters, which is why this belongs here rather than beside the commit rules that consume it.

#### `mem_correctBlocksAt`

*theorem, `CommonCore.lean`*

```lean
theorem mem_correctBlocksAt {i : BlockId} {n : ℕ} :
    i ∈ correctBlocksAt U n ↔
      i ∈ U.ids ∧ (U.block i).round = n ∧ (U.block i).creator ∈ (Correct : Finset Validator)
```

Membership in `correctBlocksAt`, unfolded.

### The commit rule, and the ledger

#### `mem_certificates`

*theorem, `Mysticeti.lean`*

```lean
theorem mem_certificates {C L : BlockId} {r : ℕ} :
    C ∈ certificates U L r ↔ C ∈ U.ids ∧ (U.block C).round = r + 2 ∧ Certifies U C L
```

Membership in `certificates`, unfolded: a round-`r+2` block that certifies `L`.

#### `certificates_nonempty_of_directCommit`

*theorem, `Mysticeti.lean`*

```lean
theorem certificates_nonempty_of_directCommit {L : BlockId} {r : ℕ}
    (h : DirectCommit U L r) : (certificates U L r).Nonempty
```

A direct commit needs `2f+1` distinct certificate authors, so in particular at least one certificate.

#### `certificates_nonempty_of_certifiedIn`

*theorem, `Mysticeti.lean`*

```lean
theorem certificates_nonempty_of_certifiedIn {A L : BlockId} {r : ℕ}
    (h : CertifiedIn U A L r) : (certificates U L r).Nonempty
```

A certificate in reach is, in particular, a certificate that exists. This is what lets M5′ compare an *indirect* commit against anything else.

#### `eligible_iff`

*theorem, `Mysticeti.lean`*

```lean
theorem eligible_iff {k j : ℕ} :
    Eligible Validator k j ↔ S.slotRound k + 3 ≤ S.slotRound j
```

Eligibility, unfolded: an anchor must sit three rounds above the slot it decides — one for votes, one for certificates, one to separate them.

#### `lt_of_eligible`

*theorem, `Mysticeti.lean`*

```lean
theorem lt_of_eligible {k j : ℕ} (h : Eligible Validator k j) : k < j
```

An eligible anchor is a later slot. Monotonicity is what carries it: were `j ≤ k`, the anchor's round could not exceed `k`'s, let alone clear its decision round.

This makes the `k < j` premises of `Decided` redundant. They are kept anyway: `decided_unique` recurses on them and hands them to `lt_trichotomy`, and re-deriving them at each use would be noise.

#### `eligible_of_lt_of_spacing`

*theorem, `Mysticeti.lean`*

```lean
theorem eligible_of_lt_of_spacing (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k + 1))
    {k j : ℕ} (h : k < j) : Eligible Validator k j
```

**Conservativity.** Under a schedule whose consecutive slots are three rounds apart — the `spacing` field this class used to carry — *every* later slot is eligible to anchor an earlier one, and the generalised premise implies the three-round one.

So the generalised `Decided` has exactly the constructors the three-round form has whenever three-round spacing holds: no derivation available before the change is unavailable after it. This is the three-round spacing bound, demoted from a consequence of the class to a consequence of a hypothesis.

#### `directCommit_of_directCommitIn`

*theorem, `Mysticeti.lean`*

```lean
theorem directCommit_of_directCommitIn {V : View Validator BlockId Payload U}
    {L : BlockId} {r : ℕ} (h : DirectCommitIn U V L r) : DirectCommit U L r
```

**A view can only under-report.** Everything it sees is real, so a view-relative direct commit is a genuine one.

This one line is what lets all of Stage A be reused unchanged: M2, M4 and M5 are stated universe-level, and a validator's local judgement feeds straight into them.

#### `isLeaderBlock_of_decided`

*theorem, `Mysticeti.lean`*

```lean
theorem isLeaderBlock_of_decided {V : View Validator BlockId Payload U} {j : ℕ} {A : BlockId}
    (h : Decided U V j (some A)) : IsLeaderBlock U j A
```

Whatever route it took, a committed verdict names a genuine candidate for that slot. Needed because the agreement proof must feed another validator's anchor into the visibility lemma, which wants its round.

#### `decided_unique`

*theorem, `Mysticeti.lean`*

```lean
theorem decided_unique {V₁ : View Validator BlockId Payload U} {k : ℕ} {v₁ : Option BlockId}
    (h₁ : Decided U V₁ k v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided U V₂ k v₂ → v₁ = v₂
```

**M6 (agreement).** No two validators reach conflicting decisions for a slot, whatever views they hold and whichever routes they took.

As with T5 this is *no-conflicting-decision*: a validator that has not yet decided is not in disagreement.

Structural induction on the first derivation. Of the sixteen constructor pairings, fifteen close outright — every commit-versus-commit case by M5′, and the direct-versus-indirect crossings by cross-view M1, the visibility lemma, or M3. The one real case is *indirect commit against indirect skip*, settled by comparing the two anchors: if they coincide the IH forces the same anchor block, and otherwise the earlier anchor is covered by the *other* validator's intermediate-skip premise, which is exactly the sub-derivation the IH needs.

That is why "nearest anchor" had to be stated positively. The negative reading would carry no sub-derivation here, and the induction would have nothing to stand on.

**Why eligibility may not be view-relative.** Since the intermediate premise now ranges over eligible slots only, invoking the other validator's copy of it needs `Eligible k j` as a side condition — and what discharges it is *this* validator's own eligibility premise for the same pair. The two match because `Eligible` is a predicate on the slot pair alone: both derivations concern the same `k`, so they agree on which slots may anchor it. Were eligibility indexed by the decider — "an anchor far enough ahead *as far as I can see*" — the premises would not meet and this case would not close.

### Delivery, growth, and coverage

#### `card_authorsAt_of_lt`

*theorem, `Liveness.lean`*

```lean
theorem card_authorsAt_of_lt {r n : ℕ} (hn : n < r) {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    (Fintype.card Validator - F.f) ≤ (authorsAt U n).card
```

**L0 — the DAG is dense below its frontier.** If any block exists at round `r`, then *every* round `n < r` has at least `2f+1` distinct authors.

Downward induction on the gap `r - n`. The step is where the two lemmas above meet: the inductive hypothesis gives a quorum of authors one round higher, that quorum is nonempty so some block sits there, and `card_authorsAt_of_succ` walks it down one more round.

The induction runs on the gap rather than on `r` itself because the statement is not about `r`: nothing distinguishes the block's own round, and generalising over `n` is what lets the step re-enter at `n+1`.

#### `card_authorsAt_of_populated`

*theorem, `Liveness.lean`*

```lean
theorem card_authorsAt_of_populated {r : ℕ} (h : Populated U r) :
    (Fintype.card Validator - F.f) ≤ (authorsAt U r).card
```

A populated round carries a quorum of authors — the step that feeds a production induction back into its build rule, and the first consumer `card_correct` was kept for.

#### `synchronised_of_delivery`

*theorem, `Liveness.lean`*

```lean
theorem synchronised_of_delivery (D : Delivery U) (h : EventuallyDelivers D R) :
    Synchronised U R
```

**L7.** `Synchronised` is a theorem, not an assumption: `refs ⊇ held ⊇` every correct block below.

L4–L6 are untouched — they still take `Synchronised`, which this now supplies a second way.

#### `directCommit_of_leader_mem`

*theorem, `Liveness.lean`*

```lean
theorem directCommit_of_leader_mem (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

**L4.** A slot with a correct leader, whose three rounds are populated and which sits after synchrony, is directly committed.

#### `directCommit_of_correct_leader`

*theorem, `Liveness.lean`*

```lean
theorem directCommit_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

**L4 at `T := Correct`.** The original statement, recovered.

#### `directCommitIn_full`

*theorem, `Liveness.lean`*

```lean
theorem directCommitIn_full (h : DirectCommit U L r) :
    DirectCommitIn U (View.full U) L r
```

A universe-level direct commit is one the full view also sees.

#### `decided_of_leader_mem`

*theorem, `Liveness.lean`*

```lean
theorem decided_of_leader_mem (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**L4, as a decision.** What L6 consumes and L3 propagates.

#### `decided_of_correct_leader`

*theorem, `Liveness.lean`*

```lean
theorem decided_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

The same at `T := Correct`.

#### `decided_none_of_leader_absent`

*theorem, `Liveness.lean`*

```lean
theorem decided_none_of_leader_absent {V : View Validator BlockId Payload U}
    (h : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k) :
    Decided U V k none
```

**L5 — an absent leader is skipped.** If the slot-`k` leader has no block at its round, every view decides `none`.

#### `le_slotRound_slotAt`

*theorem, `Liveness.lean`*

```lean
theorem le_slotRound_slotAt (n : ℕ) : n ≤ S.slotRound (slotAt Validator n)
```

`slotAt n` names a slot at or past round `n` — the defining property of the index.

#### `slotAt_zero`

*theorem, `Liveness.lean`*

```lean
theorem slotAt_zero : slotAt Validator 0 = 0
```

Round `0` is served by slot `0`.

#### `commits_recur`

*theorem, `Liveness.lean`*

```lean
theorem commits_recur (fair : FairSchedule (Validator := Validator)) (R : ℕ) (k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      CommitsAt BlockId Payload (Correct : Finset Validator) R k'
```

**L6 at `T := Correct`.** The original statement, recovered.

#### `decided_below_of_committed_run`

*theorem, `Liveness.lean`*

```lean
theorem decided_below_of_committed_run {V : View Validator BlockId Payload U} {b n : ℕ}
    (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B, Decided U V j (some B)) :
    ∀ i, i < b → ∃ v, Decided U V i v
```

**P7′ — a committed run decides everything below it.**

This is L8 with `helig` removed, and it is the shape liveness actually needs. The hypotheses are:

* `hrun` — the slots `b … n` are all committed; * `hspan` — every slot below `b` has `n` as an *eligible* anchor, which under pipelining just says the run spans three rounds, i.e. `n ≥ b + 2`.

Then every slot below `b` is decided. No synchrony, no timing, no fairness, and no hypothesis on the schedule — those enter only when discharging `hrun`, which L4 does for a run of `T`-led slots.

Two changes from L8 make it work. The anchor is the nearest **eligible** committed slot rather than the nearest committed one, which is what removes `helig`; and an eligible intermediate is shown to lie below `b` — if it were in `b … n` it would be committed by `hrun`, contradicting minimality — which is what lets the induction hypothesis reach it.

That second step is the whole content. It is why three consecutive commits suffice and why a *single* commit does not: the slots just below `b` have no eligible intermediates at all (their eligible range starts inside the run), so they resolve outright, and everything lower descends onto them.

#### `no_stall`

*theorem, `Network.Quorum.lean`*

```lean
theorem no_stall {D : Delivery U} (H : Live U D N) (hd : DeliversQuorum D) :
    ∀ r ≤ N, Populated U r
```

**L1 — no stall.** Under `Live U D N` and `DeliversQuorum D`, every correct validator has a block at every round up to the horizon.

Induction on the round. The base is `genesis`. The step goes in two hops now that `builds` is view-relative: the induction hypothesis makes `Correct` a subset of `authorsAt U r`, so a quorum *exists*; `DeliversQuorum` turns that into each correct validator *holding* a quorum; and only then does `builds` apply.

That second hop is the content of question 2. Without it the theorem would be claiming validators build on blocks they may never have received.

L1 is the **only** result where the horizon does real work. Its whole job is to turn the growth assumption into the local `Populated` facts L4 consumes — which is why L4 itself never mentions `N` (`liveness.md` §4.4).

### Time: GST, drift, and the backoff

#### `le_built`

*theorem, `Timing.lean`*

```lean
theorem le_built {v : Validator} (hv : v ∈ T) : ∀ n ≤ N, n ≤ tm.built v n
```

Rounds advance real time, so any round past `gst` was built past `gst`. This is what stops `gst` needing its own assumption.

#### `synchronisedOn_of_timing`

*theorem, `Timing.lean`*

```lean
theorem synchronisedOn_of_timing (hT : T ⊆ (Correct : Finset Validator))
    (hD : tm.DriftFrom R D) (hgst : tm.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + tm.delay ≤ tm.timeout n) :
    SynchronisedOn U T R
```

**Q1, discharged.** Once the timeout exceeds `drift + delay` and the rounds are past GST, coverage among `T` holds — `SynchronisedOn` becomes a theorem.

The chain is four inequalities: `built w n ≤ built v n + D` (drift), `D + delay ≤ timeout n` (backoff), `built v n + timeout n ≤ built v (n+1)` (waiting), hence `built w n + delay ≤ built v (n+1)`, which is exactly what `covers` wants.

Non-equivocation does the remaining work: `SynchronisedOn` quantifies over *every* `T`-authored block, and T1 identifies each with the `blk` this structure names. That is why `T ⊆ Correct` is needed here — a Byzantine author could have several blocks in a round and `blk` would name only one.

#### `driftFrom_of_prompt`

*theorem, `Timing.lean`*

```lean
theorem driftFrom_of_prompt {n₀ : ℕ}
    (hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D)
    (hto : ∀ n, n₀ ≤ n → tm.delay ≤ tm.timeout n) :
    tm.DriftFrom n₀ D
```

**Drift is preserved, not assumed.** Once the timeout has reached the delivery bound, the spread between `T`-validators at a round never grows — so a bound at *one* round gives a bound at all later ones.

The step is a two-case split on `prompt`'s `max`:

- **timeout-limited** — the validator advanced by exactly the same `timeout n` as everyone else, so the spread is unchanged; - **delivery-limited** — it waited for the round below and finished by `latest n + delay`. `latest` is *attained* by some `T`-validator, so the inductive bound applies to that one, and `delay ≤ timeout n` absorbs the rest.

Note what this does **not** show: that drift shrinks. It does not — every clock advances by the same timeout. *Bounded* is all Q1 needs, and bounded is what the argument gives.

#### `exists_synchronisedOn_of_backoff`

*theorem, `Timing.lean`*

```lean
theorem exists_synchronisedOn_of_backoff (tm : Timing U T N)
    (hT : T ⊆ (Correct : Finset Validator))
    (hmono : Monotone tm.timeout) (hub : ∀ m, ∃ n, m ≤ tm.timeout n)
    {n₀ : ℕ} (hdel : ∀ n, n₀ ≤ n → tm.delay ≤ tm.timeout n)
    (hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D) :
    ∃ R, SynchronisedOn U T R
```

**The headline.** Under GST with a bounded drift and an unbounded backoff, `SynchronisedOn` holds from *some* round — no longer assumed.

Everything above this file consumes `SynchronisedOn` and is unchanged: L4 and L6 still take it as a hypothesis, and this supplies it, exactly as `synchronised_of_delivery` supplies it from `Delivery`.

#### `synchronisedOn_of_rate`

*theorem, `Quantitative.lean`*

```lean
theorem synchronisedOn_of_rate (tm : Timing U T N) (hT : T ⊆ (Correct : Finset Validator))
    (hrate : Rated tm.timeout) {n₀ : ℕ} (hn₀ : tm.delay ≤ n₀)
    (hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D) :
    SynchronisedOn U T (max (max (D + tm.delay) n₀) tm.gst)
```

**Q3, the synchrony half.** With a rated backoff, coverage holds from an **explicit** round:

`R = max (max (D + delay) n₀) gst`

and each summand is what it looks like — the threshold the timeout must clear, the round the drift bound is measured from, and GST. Compare `exists_synchronisedOn_of_backoff`, which concludes `∃ R` and can say no more.

Nothing else changes: the drift argument and the coverage argument are reused verbatim, and `Monotone` is gone.

The hypothesis `tm.delay ≤ n₀` is what lets `driftFrom_of_prompt` fire from `n₀` — it asks that the drift base be measured at a round by which the rate has already carried the timeout past `delay`. Taking `n₀ := tm.delay` always satisfies it.

#### `slotRound_le_of_boundedSpacing`

*theorem, `Quantitative.lean`*

```lean
theorem slotRound_le_of_boundedSpacing {s : ℕ}
    (hs : BoundedSpacing (Validator := Validator) s) (k d : ℕ) :
    S.slotRound (k + d) ≤ S.slotRound k + s * d
```

Bounded spacing accumulates: `d` slots on costs at most `s * d` rounds.

#### `commits_recur_by_round`

*theorem, `Quantitative.lean`*

```lean
theorem commits_recur_by_round {s : ℕ} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card) (fair : FairWithin T w)
    (hs : BoundedSpacing (Validator := Validator) s) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ S.slotRound k' ≤ S.slotRound (max k (slotAt Validator R)) + s * w ∧
      R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r ≤ N, Populated U r) → SynchronisedOn U T R →
        S.slotRound (max k (slotAt Validator R)) + s * w + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L)
```

**Q4 in rounds.** The committing slot's round is bounded, so the horizon a DAG must reach before it is guaranteed to commit becomes an explicit number rather than "far enough".

Read the two summands: `slotRound (max k (slotAt R))` is where the search starts, and `s * w` is the worst-case cost of walking to the next `T`-leader. The `+ 2` is the certificate round — L4's `r + 2`, unchanged.

At the standard settings — round-robin over `3f+1` so `w = f + 1`, and slots every three rounds so `s = 3` — this reads `3 * (f + 1)` rounds past the starting slot, which is the concrete latency figure `liveness.md` §8 Q4 asks for.

**This bound is blind to multiple leaders.** `BoundedSpacing s` says consecutive slots are at most `s` rounds apart, and with `m` leaders sharing a round that is still `s = 1`, not `0` — only one step in `m` advances the round, which `BoundedSpacing` cannot see. So `s * w` reads `w` rounds for `w` slots however large `m` is. A bound that improves with `m` needs the schedule to expose it, which `Slots.uniform` does; this statement is kept because it is the only one that says anything about an irregular schedule.

#### `decided_of_wait`

*theorem, `Quantitative.lean`*

```lean
theorem decided_of_wait (tm : Timing U T N) (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hstart : ∀ v ∈ T, ∀ w ∈ T, tm.built w 0 ≤ tm.built v 0 + D₀)
    (hwait : ∀ n, D₀ + tm.delay ≤ tm.timeout n)
    (hgst : tm.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**The wait bound, as a decision.** What the ledger is defined over.

#### `directCommit_of_wait_two_delay`

*theorem, `Quantitative.lean`*

```lean
theorem directCommit_of_wait_two_delay (tm : Timing U T N)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hstart : ∀ v ∈ T, ∀ w ∈ T, tm.built w 0 ≤ tm.built v 0 + tm.delay)
    (hwait : ∀ n, 2 * tm.delay ≤ tm.timeout n)
    (hgst : tm.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

**`Delay(Δ) = 2Δ`.** The headline case: validators that started within one delivery bound of each other, waiting two, commit every correct leader after GST.

`D₀ ≤ Δ` is what a common start signal gives — the signal itself takes at most Δ to reach everyone. `D₀ = 0` (a synchronised start) would give `Delay(Δ) = Δ`; the factor of two is the price of not having synchronised clocks.

### View convergence

#### `synchronisedOn_of_converges`

*theorem, `ViewSync.lean`*

```lean
theorem synchronisedOn_of_converges (hT : T ⊆ (Correct : Finset Validator))
    {R D : ℕ} (hD : vs.DriftFrom R D) (hgst : vs.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vs.delay ≤ vs.timeout n) :
    SynchronisedOn U T R
```

**Reference coverage from view convergence.** The statement the design notes originally asked for, now a theorem: after GST, with validators waiting long enough that the timeout clears drift plus the delivery bound, every correct block references every correct block of the round below.

The premises divide exactly along the trust boundary — `converges` is the network's, `references` and `waits` are the protocol's — and no clause of the one stands in for the other.

#### `populatedOn`

*theorem, `ViewSync.lean`*

```lean
theorem populatedOn (vs : ViewSync U T N) {n : ℕ} (hn : n ≤ N) :
    PopulatedOn U T n
```

**Production.** The structure asserts a block per `T`-validator per round, so rounds are populated with no appeal to N1 or L1.

#### `populatedOn`

*theorem, `ViewSync.lean`*

```lean
theorem populatedOn (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn vg.built T R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n) :
    ∀ n, R ≤ n → n ≤ N → PopulatedOn U T n
```

**Production, derived.** From the seed round on, every round below the horizon is populated — the timed counterpart of `populated_of_viewsConverge`, and the same induction.

The step is the argument of `blk_mem_holds` run in the other direction: rather than moving a block that `blk` asserts exists, it moves the blocks the induction hypothesis provides. Each `w ∈ T` authored a round-`n` block, holds it at `built w n` (`holds_own`), which is past GST since rounds advance time; convergence puts it in `v`'s hands by `built w n + delay`, and drift, the wait and the backoff put that before `built v (n+1)`. So `v`'s build-time view contains a round-`n` block from every member of `T` — a quorum of distinct authors — and `builds` applies.

The conclusion starts at `R` rather than at `0`, and the hypothesis is a single round rather than every round beneath `R`, because the step consumes only its predecessor. Below `R` nothing is derivable and nothing is assumed: `converges` is silent before `gst`, and its unbounded companion `ConvergesEventually`, though it does hold there, cannot substitute — a lag that merely exists cannot be ordered against a build time, which is the comparison `hbackoff` performs. What lets the untimed route begin at round `0` is not the absence of a GST but the index alignment of `ViewsConverge`, which supplies that ordering by fiat.

#### `synchronisedOn_of_converges`

*theorem, `ViewSync.lean`*

```lean
theorem synchronisedOn_of_converges [Nonempty BlockId]
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn vg.built T R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n)
    (hbelow : ∀ n < R, PopulatedOn U T n) :
    SynchronisedOn U T R
```

**L7c with production derived.** Reference coverage from view convergence, on a structure that assumes no blocks exist.

#### `mem_toDelivery`

*theorem, `ViewSync.lean`*

```lean
theorem mem_toDelivery {v : Validator} {n : ℕ} {b : BlockId} :
    b ∈ vg.toDelivery.held v n ↔
      b ∈ vg.holds v (vg.built v (n + 1)) ∧ (U.block b).round = n ∧ v ∈ T
```

Membership in the induced delivery, unfolded.

#### `eventuallyDelivers_toDelivery`

*theorem, `ViewSync.lean`*

```lean
theorem eventuallyDelivers_toDelivery
    (vg : ViewGrowth U (Correct : Finset Validator) R N)
    (hD : DriftOn vg.built (Correct : Finset Validator) R D N) (hgst : vg.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vg.delay ≤ vg.timeout n) :
    EventuallyDelivers vg.toDelivery R
```

**N2a, derived.** The induced delivery satisfies eventual DAG synchrony from `R` on — the assumption of §6.7, obtained from view convergence and the schedule.

The horizon is no longer an obstruction. `EventuallyDelivers` quantifies over every round, including `N`, where it asserts that a correct round-`N` block is in hand when its holder builds for round `N+1`; `waits` reaching past the horizon is exactly what supplies that step, and above `N` the statement is vacuous because no block exists there.

#### `viewsConverge_toDelivery`

*theorem, `ViewSync.lean`*

```lean
theorem viewsConverge_toDelivery (vg : ViewGrowth U (Correct : Finset Validator) 0 N)
    (hD : DriftOn vg.built (Correct : Finset Validator) 0 D N) (hgst : vg.gst = 0)
    (hbackoff : ∀ n, D + vg.delay ≤ vg.timeout n) :
    ViewsConverge vg.toDelivery
```

**The bridge, at the untimed condition's own parameters.** When the reliable set is all of `Correct` and stabilisation has already happened, the induced delivery satisfies `ViewsConverge` outright — the assumption of the untimed route, obtained as a theorem of the timed one.

The two hypotheses `T = Correct` and `R = 0` are carried in the type rather than assumed, since both are parameters of the structure. They are the exact price of the passage: outside `T` the timed structure says nothing, and below `gst` neither does the network.

### Chain quality

#### `card_correct_le_two_mul_coveredAt_of_decided`

*theorem, `Quality.Coverage.lean`*

```lean
theorem card_correct_le_two_mul_coveredAt_of_decided
    {V : View Validator BlockId Payload U} {k : ℕ}
    (h : Decided U V k (some L)) (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card ≤ 2 * (coveredAt U L δ).card
```

**CQ2 (the half, exactly).** Every commit carries, at every round below it, blocks from at least half of the correct validators: `|Correct| ≤ 2·|covered|`, since `|Correct| ≥ 2f + 1`.

#### `mem_ledgerSet_of_mem_history`

*theorem, `Quality.Coverage.lean`*

```lean
theorem mem_ledgerSet_of_mem_history {g : ℕ → Option BlockId} {n k : ℕ}
    (hg : g k = some L) (hk : k < n) (hL : L ∈ U.ids)
    (hb : b ∈ history U L) : b ∈ ledgerSet U g n
```

A cone block of a committed slot is in the ledger — the one unfolding both CQ3 and CQ6 rest on.

#### `mem_history_of_decided_commit`

*theorem, `Quality.Inclusion.lean`*

```lean
theorem mem_history_of_decided_commit (hs : Synchronised U R)
    {V : View Validator BlockId Payload U} {k : ℕ}
    (hdec : Decided U V k (some L))
    (hLc : (U.block L).creator ∈ (Correct : Finset Validator))
    (hb : b ∈ U.ids) (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hR : R ≤ (U.block b).round)
    (hlt : (U.block b).round < (U.block L).round) :
    b ∈ history U L
```

**CQ5.** Post-`R`, every correct block is in the cone of **every** committed leader block with a correct author at a later round — any commit route, any view. The backbone does all the work.

#### `committed_of_correct_block`

*theorem, `Quality.Inclusion.lean`*

```lean
theorem committed_of_correct_block (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (fair : FairScheduleOn T) (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k'
```

**CQ6 (inclusion liveness).** Under a fair schedule over reliable validators and post-`R` synchrony, for every round `m ≥ R` there is a committed slot — above `m`, led by a correct validator — whose flush contains **every** correct round-`m` block; hence every such block is in the agreed ledger of any verdict assignment covering that slot.

The slot is produced *before* the universe is quantified, exactly as in L6: the schedule fixes it, and any sufficiently grown synchronous DAG then commits it.

### Denial of service

#### `mem_historyBlocksOf`

*theorem, `DoS.Exposure.lean`*

```lean
theorem mem_historyBlocksOf {b i : BlockId} {X : Validator} {n : ℕ} :
    i ∈ historyBlocksOf U b X n ↔
      i ∈ history U b ∧ (U.block i).creator = X ∧ (U.block i).round = n
```

Membership in `historyBlocksOf`, unfolded.

#### `not_exposedIn_iff_card_le_one`

*theorem, `DoS.Exposure.lean`*

```lean
theorem not_exposedIn_iff_card_le_one {b : BlockId} {X : Validator} :
    ¬ ExposedIn U b X ↔ ∀ n, (historyBlocksOf U b X n).card ≤ 1
```

**Not exposed** and **at most one block per round** are the same condition.

The counting form of `ExposedIn`, and the whole content of D11: an author that is never exposed in `b`'s history contributes at most one block per round to it, so the equivocation achieved nothing.

#### `not_exposedIn_of_round_le_one`

*theorem, `DoS.Exposure.lean`*

```lean
theorem not_exposedIn_of_round_le_one {b : BlockId} {X : Validator} (hb : b ∈ U.ids)
    (hr : (U.block b).round ≤ 1) : ¬ ExposedIn U b X
```

Nothing is exposed below round 2: there is not room for a merge.

#### `mem_exposedTo`

*theorem, `DoS.Exposure.lean`*

```lean
theorem mem_exposedTo {b : BlockId} {X : Validator} :
    X ∈ exposedTo U b ↔ ExposedIn U b X
```

`exposedTo` collects exactly the authors exposed in the block's history — the `Finset` form of `ExposedIn`.

#### `card_exposedTo_le`

*theorem, `DoS.Exposure.lean`*

```lean
theorem card_exposedTo_le {b : BlockId} (hb : b ∈ U.ids) : (exposedTo U b).card ≤ F.f
```

**At most `f` authors can be exposed**, since exposure requires equivocation and only Byzantine validators equivocate.

#### `mem_missingAt`

*theorem, `DoS.Density.lean`*

```lean
theorem mem_missingAt {b : BlockId} {δ : ℕ} {v : Validator} :
    v ∈ missingAt U b δ ↔ v ∈ (Correct : Finset Validator) ∧
      ∀ i ∈ history U b, ¬ ((U.block i).creator = v ∧ (U.block i).round = δ)
```

Membership in `missingAt`, unfolded: a correct validator is missing at depth `δ` when the history contains none of its blocks there.

#### `card_missingAt_le`

*theorem, `DoS.Density.lean`*

```lean
theorem card_missingAt_le {b : BlockId} (hb : b ∈ U.ids) {δ : ℕ}
    (hδ : δ < (U.block b).round) : (missingAt U b δ).card ≤ F.f
```

**D25 (density).** A valid block's history contains a block by all but at most `f` of the correct validators at every round strictly below it.

#### `card_filter_creator_le`

*theorem, `DoS.Counting.lean`*

```lean
theorem card_filter_creator_le (hb : b ∈ U.ids) (h : ¬ ExposedIn U b X) :
    ((history U b).filter (fun j => (U.block j).creator = X)).card ≤ (U.block b).round + 1
```

An author not exposed in `b`'s history contributes at most one block per round to it, hence at most `round b + 1` in all.

#### `eq_of_not_exposedIn`

*theorem, `DoS.Adoption.lean`*

```lean
theorem eq_of_not_exposedIn {c i j : BlockId} {X : Validator} (h : ¬ ExposedIn U c X)
    (hi : i ∈ history U c) (hj : j ∈ history U c)
    (hic : (U.block i).creator = X) (hjc : (U.block j).creator = X)
    (hround : (U.block i).round = (U.block j).round) : i = j
```

The pointwise form of D11's counting: two blocks by an author unexposed in a history, at one round of it, are equal.

#### `exists_referencer`

*theorem, `DoS.Adoption.lean`*

```lean
theorem exists_referencer {b i : BlockId} (hb : b ∈ U.ids) (hi : i ∈ history U b)
    (hne : i ≠ b) : ∃ j ∈ history U b, i ∈ (U.block j).refs
```

Everything in a history except the block itself is referenced from within the history.

#### `mem_history_of_creator_eq_of_not_exposedIn`

*theorem, `DoS.Adoption.lean`*

```lean
theorem mem_history_of_creator_eq_of_not_exposedIn {b i j : BlockId} {X : Validator}
    (hb : b ∈ U.ids) (hX : ¬ ExposedIn U b X)
    (hi : i ∈ history U b) (hj : j ∈ history U b)
    (hic : (U.block i).creator = X) (hjc : (U.block j).creator = X)
    (hround : (U.block i).round ≤ (U.block j).round) : i ∈ history U j
```

**Unexposed means one chain.** Two same-author blocks of a history, the author unexposed there, are chain-related: the lower lies in the higher one's history. With D20 this says an unexposed author's content *is* a single self-parent chain.

#### `mem_topsOf`

*theorem, `DoS.Adoption.lean`*

```lean
theorem mem_topsOf {b t : BlockId} {X : Validator} :
    t ∈ topsOf U b X ↔ t ∈ history U b ∧ (U.block t).creator = X ∧
      ∀ c ∈ history U b, (U.block c).creator = X → t ∉ (U.block c).refs
```

Membership in `topsOf`, unfolded: a top is a block of `X` in the history with no later block of `X` reachable above it.

#### `exists_top_of_mem_history`

*theorem, `DoS.Adoption.lean`*

```lean
theorem exists_top_of_mem_history {b i : BlockId} {X : Validator} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hic : (U.block i).creator = X) :
    ∃ t ∈ topsOf U b X, i ∈ history U t
```

Every `X`-block of a history lies in some top's history: walk up `X`-children as far as they go.

#### `card_filter_creator_le_card_topsOf`

*theorem, `DoS.Adoption.lean`*

```lean
theorem card_filter_creator_le_card_topsOf (hdos : DoSValid U) {b : BlockId}
    (hb : b ∈ U.ids) (X : Validator) :
    ((history U b).filter fun i => (U.block i).creator = X).card
      ≤ (topsOf U b X).card * ((U.block b).round + 1)
```

An author's whole content is at most one block per (top, round) pair: each block sits on the chain of some top, and a top's own history holds one `X`-block per round (D21 applied to the top itself).

#### `top_eq_of_mem_namer_history`

*theorem, `DoS.Adoption.lean`*

```lean
theorem top_eq_of_mem_namer_history (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    {X : Validator} {t₁ t₂ j : BlockId}
    (ht₁ : t₁ ∈ topsOf U b X) (ht₂ : t₂ ∈ topsOf U b X)
    (hj : j ∈ history U b) (hjref : t₂ ∈ (U.block j).refs)
    (h₁j : t₁ ∈ history U j) : t₁ = t₂
```

**The adoption collapse.** Two tops, one lying inside the history of a block that references the other, coincide: a namer's history has room for only one `X`-chain, and a named `X`-block strictly below another has an `X`-child there — so it was no top.

#### `not_mem_creators_refs_of_correct_exposed`

*theorem, `DoS.Exclusion.lean`*

```lean
theorem not_mem_creators_refs_of_correct_exposed (hdos : DoSValid U) {X : Validator} {n : ℕ}
    (hexp : ∀ c ∈ U.ids, (U.block c).round = n + 1 →
      (U.block c).creator ∈ (Correct : Finset Validator) → ExposedIn U c X)
    {b : BlockId} (hb : b ∈ U.ids) (hbr : n + 2 ≤ (U.block b).round) :
    X ∉ creatorsOf U.block (U.block b).refs
```

The form the condition consumes: from `n+2` on, nobody may name `X`.

#### `mem_history_of_correct`

*theorem, `DoS.Exclusion.lean`*

```lean
theorem mem_history_of_correct {R : ℕ} (hs : SynchronisedOn U (Correct : Finset Validator) R) :
    ∀ d : ℕ, ∀ c ∈ U.ids, ∀ a ∈ U.ids,
      (U.block c).creator ∈ (Correct : Finset Validator) →
      (U.block a).creator ∈ (Correct : Finset Validator) →
      R ≤ (U.block a).round → (U.block a).round + 1 + d = (U.block c).round →
      a ∈ history U c
```

**The backbone lemma.** After `R`, correct histories contain the whole correct past.

#### `mem_novelty`

*theorem, `DoS.Novelty.lean`*

```lean
theorem mem_novelty : i ∈ novelty U V b ↔ i ∈ history U b ∧ i ∉ V
```

Membership in `novelty`, unfolded: the novel blocks are those in the history and not already in the view.

#### `viewUpto_succ`

*theorem, `DoS.Novelty.lean`*

```lean
theorem viewUpto_succ (n : ℕ) :
    viewUpto D v (n + 1) =
      viewUpto D v n ∪ (D.accepted v (n + 1)).biUnion (history U)
```

The view after round `n+1` is the previous view together with the histories of everything newly accepted.

#### `viewUpto_mono`

*theorem, `DoS.Novelty.lean`*

```lean
theorem viewUpto_mono (h : m ≤ n) : viewUpto D v m ⊆ viewUpto D v n
```

Views only grow with the round index.

#### `history_subset_viewUpto`

*theorem, `DoS.Novelty.lean`*

```lean
theorem history_subset_viewUpto {a : BlockId} (hmn : m ≤ n)
    (ha : a ∈ D.accepted v m) : history U a ⊆ viewUpto D v n
```

An accepted block's whole history is retained.

#### `viewUpto_subset_history`

*theorem, `DoS.Novelty.lean`*

```lean
theorem viewUpto_subset_history (hw : w ∈ (Correct : Finset Validator))
    {b : BlockId} (hb : b ∈ U.ids) (hbc : (U.block b).creator = w)
    (hbr : (U.block b).round = n + 1) :
    viewUpto D w n ⊆ history U b
```

A correct validator's block carries everything its author ever accepted: `includes` per round, chained by the self-parent (S10).

#### `card_viewUpto_le'`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_viewUpto_le' {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hra : RefsAccepted D)
    (hv : v ∈ (Correct : Finset Validator)) {n : ℕ} (hn : R + 1 ≤ n) :
    (viewUpto D v n).card ≤ (viewUpto D v (R + 1)).card +
      (n - (R + 1)) *
        ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ)
```

**B3′ — linear storage from the enforceable rule alone.** After `R`, a correct validator's view grows by at most `|Correct|·(f·κ + 1) + f·κ` per round, under nothing but the Byzantine budget and the reference discipline: the correct side is supplied by C3″.

#### `viewUpto_subset_ids`

*theorem, `DoS.Novelty.lean`*

```lean
theorem viewUpto_subset_ids : viewUpto D v n ⊆ U.ids
```

A view holds real blocks.

#### `card_viewUpto_filter_correct_le`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_viewUpto_filter_correct_le (v : Validator) (n : ℕ) :
    ((viewUpto D v n).filter
      fun i => (U.block i).creator ∈ (Correct : Finset Validator)).card ≤
      (Correct : Finset Validator).card * (n + 1)
```

The correct part of a view counts itself: one block per correct author per round (`no_equivocation`), so at most `|Correct|·(n+1)`.

#### `mem_byzPool`

*theorem, `DoS.Novelty.lean`*

```lean
theorem mem_byzPool {i : BlockId} :
    i ∈ byzPool D n ↔ ∃ w ∈ (Correct : Finset Validator),
      i ∈ viewUpto D w n ∧
        (U.block i).creator ∉ (Correct : Finset Validator)
```

Membership in `byzPool`, unfolded: a Byzantine-authored block that some correct validator's view already contains.

#### `card_byzPool_le`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_byzPool_le {κ : ℕ} (hbyz : ByzBudget D κ) (hra : RefsAccepted D)
    (n : ℕ) :
    (byzPool D n).card ≤ (Correct : Finset Validator).card * F.f +
      n * ((Correct : Finset Validator).card * (F.f * κ))
```

The pool, telescoped: linear from round 0.

#### `card_viewUpto_le`

*theorem, `DoS.Novelty.lean`*

```lean
theorem card_viewUpto_le {κ : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hv : v ∈ (Correct : Finset Validator)) (n : ℕ) :
    (viewUpto D v n).card ≤
      (Correct : Finset Validator).card * (n + 1) +
        ((Correct : Finset Validator).card * F.f +
          n * ((Correct : Finset Validator).card * (F.f * κ)))
```

**B4 — unconditional linear storage.** Under nothing but the enforceable budget and the reference discipline — no synchrony, no `R`, no delivery guarantee — every correct validator's retained view is linear in the round: at most one block per correct author per round, plus the global Byzantine pool. This is the §6 pre-`R` conjecture, closed: the base the capstone measures from is itself linear, so the DoS bound holds from round 0 under full asynchrony.

### Garbage collection

#### `chopBlock_creator`

*theorem, `GC.Chop.lean`*

```lean
theorem chopBlock_creator :
    (chopBlock U G i).creator = (U.block i).creator
```

Truncation leaves authorship unchanged.

#### `chopBlock_round`

*theorem, `GC.Chop.lean`*

```lean
theorem chopBlock_round :
    (chopBlock U G i).round = (U.block i).round - G
```

Truncation rebases rounds by the cut.

#### `chopBlock_payload`

*theorem, `GC.Chop.lean`*

```lean
theorem chopBlock_payload :
    (chopBlock U G i).payload = (U.block i).payload
```

Truncation leaves payloads unchanged.

#### `chopBlock_refs_of_le`

*theorem, `GC.Chop.lean`*

```lean
theorem chopBlock_refs_of_le (h : (U.block i).round ≤ G) :
    (chopBlock U G i).refs = ∅
```

At or below the cut a block becomes a genesis: its references are dropped.

#### `chopBlock_refs_of_lt`

*theorem, `GC.Chop.lean`*

```lean
theorem chopBlock_refs_of_lt (h : G < (U.block i).round) :
    (chopBlock U G i).refs = (U.block i).refs
```

Above the cut references are untouched.

#### `creatorsOf_chopBlock`

*theorem, `GC.Chop.lean`*

```lean
theorem creatorsOf_chopBlock (s : Finset BlockId) :
    creatorsOf (chopBlock U G) s = creatorsOf U.block s
```

Creators are untouched, so creator sets are, pointwise.

#### `mem_chop_ids`

*theorem, `GC.Chop.lean`*

```lean
theorem mem_chop_ids :
    i ∈ (chop U G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round
```

The truncated universe holds exactly the blocks at or above the cut.

#### `chop_block_eq`

*theorem, `GC.Chop.lean`*

```lean
theorem chop_block_eq : (chop U G).block = chopBlock U G
```

The truncated universe looks blocks up through `chopBlock`.

#### `blocksAt_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem blocksAt_chop (m : ℕ) :
    blocksAt (chop U G) m = blocksAt U (G + m)
```

Round `m` of the truncation is round `G + m` of the original.

#### `authorsAt_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem authorsAt_chop (m : ℕ) :
    authorsAt (chop U G) m = authorsAt U (G + m)
```

And so are its authors.

#### `history_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem history_chop (hb : b ∈ (chop U G).ids) :
    history (chop U G) b =
      (history U b).filter fun i => G ≤ (U.block i).round
```

**The cone above the cut**: truncation intersects every cone with the window. This is the lemma the windowed budget (`garbage.md` G13) and the statute of limitations both run on.

#### `certificates_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem certificates_chop {L : BlockId} (s : ℕ) :
    certificates (chop U G) L s = certificates U L (G + s)
```

Certificates for the slot at rebased round `s` are the original slot's certificates, verbatim.

#### `certifiedIn_chop`

*theorem, `GC.Chop.lean`*

```lean
theorem certifiedIn_chop {A L : BlockId} (hA : A ∈ (chop U G).ids) (s : ℕ) :
    CertifiedIn (chop U G) A L s ↔ CertifiedIn U A L (G + s)
```

**The indirect test survives the cut**: an anchor above the horizon certifies a slot above the horizon in the truncation exactly when it did in the original. With `directCommit_chop`/`directSkip_chop` this is the per-slot decision invariance of `garbage.md` G3 — the indirect verdict is a property of the anchor's cone, and never consults the pruned prefix.

#### `decided_agree_chop`

*theorem, `GC.ChopDecided.lean`*

```lean
theorem decided_agree_chop (hd : G ≤ S.slotRound d)
    {W : View Validator BlockId Payload (chop U G)}
    {V : View Validator BlockId Payload U} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := S.chop G d hd) (chop U G) W k w)
    (hV : Decided U V (d + k) v) :
    w = v
```

**G4.** A validator that joined from the truncation — holding an **arbitrary** view `W` of `chop U G`, with no history below the cut and no relation to any full-history view — agrees slot for slot with every full-history validator. `decided_unique` runs inside the truncation against the truncated full-history view, and `decided_chop` carries the verdict across the cut.

#### `mem_viewUpto`

*theorem, `GC.Window.lean`*

```lean
theorem mem_viewUpto {t : ℕ} :
    x ∈ viewUpto D v t ↔
      ∃ k, k ≤ t ∧ ∃ a ∈ D.accepted v k, x ∈ history U a
```

Membership in the accumulated store, unrolled: something accepted at some round up to `t` carries `x` in its cone.

#### `chopD_accepted`

*theorem, `GC.Window.lean`*

```lean
theorem chopD_accepted (m : ℕ) :
    (chopD D G).accepted v m = D.accepted v (G + m)
```

The truncated delivery accepts at round `m` what the original accepted at `G + m`.

#### `card_retained_le`

*theorem, `GC.Window.lean`*

```lean
theorem card_retained_le {κ Λ t : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hv : v ∈ (Correct : Finset Validator))
    (hG : G ≤ t) (hΛ : t ≤ G + Λ) :
    ((viewUpto D v t).filter fun i => G ≤ (U.block i).round).card ≤
      (Correct : Finset Validator).card * (Λ + 1) +
        ((Correct : Finset Validator).card * F.f +
          Λ * ((Correct : Finset Validator).card * (F.f * κ)))
```

**G6.** A validator whose horizon `G` trails its current round `t` by at most `Λ` retains a **constant** number of blocks — independent of `t`, hence of how long the system has run. B4 gave linear-forever; the horizon makes it constant-at-lag-`Λ`. Stated per time: the retained store is the truncated store (G14), which B4 bounds on `chop U G` at window depth `t − G ≤ Λ`.

#### `mem_attesters`

*theorem, `GC.AttestedBase.lean`*

```lean
theorem mem_attesters {v : Validator} :
    v ∈ attesters U t y ↔
      ∃ a ∈ U.ids, (U.block a).round = t ∧ y ∈ history U a ∧
        (U.block a).creator = v
```

Membership in `attesters`, unfolded: an attester is a correct author of a round-`t` block whose history reaches `y`.

#### `mem_base`

*theorem, `GC.AttestedBase.lean`*

```lean
theorem mem_base :
    y ∈ Base U t G ↔
      (y ∈ U.ids ∧ (U.block y).round = G) ∧
        F.f + 1 ≤ (attesters U t y).card
```

Membership in `Base`, unfolded: a round-`G` block attested by at least `f+1` validators.

#### `exists_correct_attester_of_mem_base`

*theorem, `GC.AttestedBase.lean`*

```lean
theorem exists_correct_attester_of_mem_base (hy : y ∈ Base U t G) :
    ∃ a ∈ U.ids, (U.block a).round = t ∧
      (U.block a).creator ∈ (Correct : Finset Validator) ∧
      y ∈ history U a
```

**G10, soundness.** Everything in the base has a correct attester — `f+1` authors always include one — and so lies in a correct cone. The adversary cannot smuggle fabrications into anyone's base.

### Odontoceti

#### `not_directSkip_of_directCommit`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem not_directSkip_of_directCommit (hc : DirectCommit U L r)
    (hk : DirectSkip U L r) : False
```

**O1 (thesis Lemma 1).** No leader block is both directly committed and directly skipped: the two quorums share `n − 2f ≥ f+1` authors, all equivocators — one too many. Needs only `n ≥ 3f+1`.

#### `eq_of_directCommit`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem eq_of_directCommit {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (h₂ : DirectCommit U L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂
```

**O1′ (M5 analogue).** Two directly committed blocks by one author at one round are equal: their support quorums share `n − 2f ≥ f+1` authors, each supporting both — all equivocators. Needs only `n ≥ 3f+1`.

#### `not_thickLink_of_directSkip`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem not_thickLink_of_directSkip (hk : DirectSkip U L r)
    (A : BlockId) : ¬ ThickLink U A L r
```

**O2 (thesis Lemma 2).** A directly skipped leader fails the indirect test against **every** anchor: `≤ 2f < n − 3f`. This is where `n ≥ 5f+1` is used.

#### `thickLink_of_directCommit`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem thickLink_of_directCommit (h : DirectCommit U L r) {A : BlockId}
    (hA : A ∈ U.ids) (hround : r + 2 ≤ (U.block A).round) :
    ThickLink U A L r
```

**O3 (thesis Lemma 3) — propagation, the heart.** If `L` is directly committed, then **every** block from two rounds above it on — Byzantine-authored included, validity is structural — carries at least `n − 3f` distinct authors of support blocks in its cone. One hop is quorum intersection minus the twin discount; depth is cone monotonicity. Every anchor's cone *is* the certificate.

#### `eq_of_directCommit_of_thickLink`

*theorem, `Odontoceti.Rules.lean`*

```lean
theorem eq_of_directCommit_of_thickLink {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (ht : ThickLink U A L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂
```

**O4′.** A directly committed block is the **only** same-author block that can pass the indirect test, at any anchor: `n−f` supporters of `L₁` and `n−3f` in-cone supporters of `L₂` would overlap in `≥ n−5f ≥ 1` correct authors, each supporting two twins — impossible. The second place `n ≥ 5f+1` bites, and the replacement for Mysticeti's M5′ in every direct-versus-indirect crossing.

#### `eligible_iff`

*theorem, `Odontoceti.Decision.lean`*

```lean
theorem eligible_iff {k j : ℕ} :
    Eligible Validator k j ↔ S.slotRound k + 2 ≤ S.slotRound j
```

Eligibility, unfolded. Two rounds rather than Mysticeti's three, which is what the stronger committee affords.

#### `lt_of_eligible`

*theorem, `Odontoceti.Decision.lean`*

```lean
theorem lt_of_eligible {k j : ℕ} (h : Eligible Validator k j) : k < j
```

An eligible anchor is a later slot.

### Not otherwise grouped

#### `exists_self_ancestor`

*theorem, `DoS.SelfParent.lean`*

```lean
theorem exists_self_ancestor {b : BlockId} (hb : b ∈ U.ids) {t : ℕ}
    (ht : t ≤ (U.block b).round) :
    ∃ i ∈ history U b,
      (U.block i).creator = (U.block b).creator ∧ (U.block i).round = t
```

**D20 (chains reach the ground).** A block's history holds a block by its own author at *every* round below it. Contiguity is the content: an author cannot appear at round `t` without a full pedigree at `t-1, …, 0`.

#### `not_exposedIn_self_creator`

*theorem, `DoS.SelfParent.lean`*

```lean
theorem not_exposedIn_self_creator (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    ¬ ExposedIn U b (U.block b).creator
```

**D21 (no self-laundering).** Under the DoS condition no valid block is exposed to its own author. A block cites its self-parent, and `DoSValid` forbids citing an exposed author — so once an author's equivocation is visible in some history, that author can never build on that history again.

This is the indispensable half of D20: the fresh "carrier" block that adopts an equivocation branch while carrying none of its author's past — the mechanism of every super-linear history family — cannot exist.

---

## Appendix D. Index of internal lemmas

The 334 lemmas used only within the file that proves
them. They are steps of the arguments above rather than results
in their own right, so they are listed rather than displayed;
the source is the reference for their statements.

| Lemma | Module | Role |
|:---|:---|:---|
| `card_creators` | `Block` | Distinct creators means the creator map does not collapse the refs, so the creator set has exactly as many … |
| `card_refs` | `Block` | A non-genesis block references at least `2f+1` blocks. |
| `refs_subset` | `BlockDag` | Completeness, as a subset statement. |
| `View.exists_reaches_iff` | `CausalHistory` | T6a, in the form the commit rules consume. Asking "is there a `P`-block in `c`'s causal history?" gives … |
| `View.mem_of_reaches` | `CausalHistory` | T6a. Causal history never escapes a view. |
| `not_reaches_of_round_lt` | `CausalHistory` | A block cannot reach anything strictly above it. Contrapositive of T2, and the form that rules out … |
| `card_authorsAt_le` | `CommonCore` | The author pool at round `n` is covered by the correct authors together with the Byzantine validators, … |
| `card_creatorsOf_correctBlocksAt` | `CommonCore` | — |
| `creator_injOn_correctBlocksAt` | `CommonCore` | Distinct correct round-`n` blocks have distinct authors — non-equivocation (T1) in the form the count needs. |
| `creatorsOf_correctBlocksAt_subset` | `CommonCore` | — |
| `exists_common_correct_ancestor` | `CommonCore` | T3c (Common correct ancestor). If any block exists at round `r+2`, some correct validator's round-`r` … |
| `exists_correct_common_support` | `CommonCore` | T3a (Correct-support counting). Some correct validator's round-`r` block is backed by enough correct … |
| `support_threshold_arith` | `CommonCore` | The arithmetic core of T3a, isolated from the combinatorics. |
| `Accepted.card_le` | `DoS.Acceptance` | One block per author out of the `n` validators. This is the whole reason the acceptance rule buys anything. |
| `View.card_ofAccepted_add_one` | `DoS.Acceptance` | D3. `|V| = |H(b)| - 1`, stated additively. |
| `View.card_ofAccepted_le` | `DoS.Acceptance` | D2 — the bridge. A view generated by an accepted set is at most `3f+1` histories wide. |
| `View.mem_ofAccepted` | `DoS.Acceptance` | — |
| `View.ofAccepted_mono` | `DoS.Acceptance` | Exclusion governs what you reference, not what you retain. Retaining more is monotone on its own, so a … |
| `View.ofAccepted_subset` | `DoS.Acceptance` | D4. If everything accepted before is reachable from something accepted now, the view has only grown. |
| `View.ofAccepted_subset_of_refs` | `DoS.Acceptance` | The form self-reference supplies: `v`'s next block is accepted at the next round and references everything … |
| `history_eq_insert_ofAccepted` | `DoS.Acceptance` | The view generated by `b`'s references is `b`'s history, less `b`. |
| `notMem_ofAccepted_self` | `DoS.Acceptance` | A block is never inside the view its own references generate: everything there sits a round lower. |
| `card_history_le_of_card_exposedTo_le_one` | `DoS.Adoption` | The same bound with the hypothesis in counted form: at most one author caught in the whole history. |
| `card_history_le_of_f_le_one` | `DoS.Adoption` | C1′ at `f ≤ 1`, unconditionally. Exposure is Byzantine (D15) and the Byzantine set has at most one member, … |
| `card_history_le_of_unique_equivocator` | `DoS.Adoption` | The main bound, unique-equivocator regime. If at most one author is exposed in `b`'s history, the history … |
| `card_topsOf_le` | `DoS.Adoption` | Tops are as scarce as authors. When every author other than `X` is unexposed — its blocks a single chain — … |
| `accepted_correct_of_allExposed` | `DoS.Composition` | After exposure-complete, a correct validator accepts nothing Byzantine-authored: its next block would have … |
| `byzPool_mono` | `DoS.Composition` | — |
| `byzPool_subset_of_allExposed` | `DoS.Composition` | The pool freezes. After exposure-complete at `m`, the global Byzantine pool never grows past its … |
| `byzPool_succ_subset` | `DoS.Composition` | The freeze step: a round in which every correct acceptance is correct-authored adds nothing to the pool — … |
| `card_viewUpto_le_of_allExposed` | `DoS.Composition` | B5 — the slope decays to the correct-production rate. After exposure-complete at `m`, a correct view is … |
| `card_viewUpto_le_of_allExposed'` | `DoS.Composition` | B5, with the constant made explicit by the budget: the frozen pool is at most `|Correct|·f·(1 + (m+1)·κ)`. … |
| `EquivFree.subset` | `DoS.Counting` | — |
| `View.card_le_of_equivFree` | `DoS.Counting` | D5. A view whose blocks reach no higher than round `r`, and which holds no equivocation, holds at most … |
| `blocksAt_disjoint` | `DoS.Counting` | Distinct rounds hold disjoint blocks: a block sits at one round. |
| `blocksAt_eq_atRound` | `DoS.Counting` | — |
| `card_atRound_le` | `DoS.Counting` | One round of an equivocation-free set has at most one block per validator, so at most `3f+1` blocks. |
| `card_authorsAt_le_card_blocksAt` | `DoS.Counting` | Authors are the image of blocks, so a round has at least as many blocks as authors. |
| `card_blocksAt_of_lt` | `DoS.Counting` | L0 in blocks rather than authors. |
| `card_filter_creator_le_of_mem_refs` | `DoS.Counting` | D19b. Under the DoS condition, an author a block *references* contributes at most `round b + 1` blocks to … |
| `card_history_le_of_not_exposed` | `DoS.Counting` | D19a. A history exposing nobody is linear in the round: at most `(3f+1)(r+1)` blocks, which is the … |
| `card_ids_bounds` | `DoS.Counting` | The bounds together, on a universe with no equivocation at all: linear in the round from both sides. |
| `card_ids_ge_of_round` | `DoS.Counting` | D6. A universe holding a block at round `r` holds at least `(n−f)·r + 1` blocks: `2f+1` at every round … |
| `card_le_of_equivFree` | `DoS.Counting` | The general counting bound. An equivocation-free set spanning rounds `0…r` holds at most `(3f+1)(r+1)` blocks. |
| `equivFree_history_iff` | `DoS.Counting` | — |
| `mem_atRound` | `DoS.Counting` | — |
| `card_missingAt_le_aux` | `DoS.Density` | — |
| `card_missingAt_le_base` | `DoS.Density` | The one-round case: the references themselves witness all but at most `f` of the correct validators of the … |
| `missingAt_subset_of_mem_refs` | `DoS.Density` | Missing is monotone through references: what `b` lacks, its references lack. |
| `card_creators_accepted_of_eventuallyDelivers` | `DoS.Exclusion` | Where the quorum comes from after `R` — and the settled answer to the plan's Q1. |
| `card_creators_correctBlocksAt` | `DoS.Exclusion` | The correct blocks of a populated round carry a quorum of authors. |
| `correctBlocksAt_admissible_quorum` | `DoS.Exclusion` | D15b — the threshold is met by the correct set alone. |
| `correct_subset_creators_correctBlocksAt` | `DoS.Exclusion` | A populated round carries every correct validator among its correct blocks' authors. |
| `creator_notMem_exposedTo_of_mem_correctBlocksAt` | `DoS.Exclusion` | No correct block's author is ever excluded — D15, in the form a builder needs. |
| `dosValid_refs_of_correctBlocksAt` | `DoS.Exclusion` | The same, phrased as the DoS condition permits it: a block whose references are correct round-`n` blocks … |
| `eq_of_both_name_of_shared` | `DoS.Exclusion` | The intersection lemma. Two blocks that both name `X` agree about `X` wherever their shared correct … |
| `exists_accepted_of_mem_ids` | `DoS.Exclusion` | What the two policies do buy: nothing an author publishes is invisible to the correct population. If any … |
| `exists_correct_mem_refs` | `DoS.Exclusion` | Every non-genesis block references a correct block of the round below. |
| `exists_shared_correct_ref` | `DoS.Exclusion` | Two blocks of the same round share a correct reference, when the correct validators are as few as the … |
| `exposedIn_of_accepted_span` | `DoS.Exclusion` | D8a. A validator whose accepted set spans two disagreeing histories exposes the author in its own next block. |
| `exposedIn_of_correct_disagree` | `DoS.Exclusion` | D16 — after `R`, agree or be exposed. If the histories of two correct round-`n` blocks between them hold … |
| `exposedIn_of_correct_exposed` | `DoS.Exclusion` | D17 — exclusion is total, and permanent. If every correct block of round `n+1` is exposed to `X`, then so … |
| `mem_history_of_pinned` | `DoS.Exclusion` | D18 — pinning. If all but at most `f` correct validators put `A` into their round-`(j+1)` block, then … |
| `not_exposedIn_refs_of_policy` | `DoS.Exclusion` | The condition is implementable. A correct validator following the policy produces blocks that satisfy the … |
| `EquivPair.symm` | `DoS.Exposure` | — |
| `ExposedIn.mono` | `DoS.Exposure` | D12. Exposure is inherited by everything above: what one block's history reveals, every block reaching it … |
| `ExposedIn.not_correct` | `DoS.Exposure` | D15 — exclusion is sound. An exposed author is Byzantine. |
| `ExposedIn.of_mem_refs` | `DoS.Exposure` | Exposure passes up a single reference — the form the induction in D17 will want. |
| `card_creators_refs_add_card_exposedTo_le` | `DoS.Exposure` | D15a — the margin. The authors a block references and the authors it has caught are disjoint subsets of … |
| `card_le_one_or_not_mem_refs` | `DoS.Exposure` | D11. Under the DoS condition, for every block and every author exactly one of two things holds: the author … |
| `creators_refs_disjoint_exposedTo` | `DoS.Exposure` | A block never names an author its own history has caught — `DoSValid`, read as a disjointness. |
| `creators_refs_eq_correct` | `DoS.Exposure` | D15a at the bound. Once a block has caught the whole fault budget, its references are *exactly* the … |
| `eq_of_mem_refs_of_creator_eq` | `DoS.Exposure` | D7, the no-equivocation half. A block's references carry distinct authors, so the layer immediately below … |
| `exposedIn_iff_of_view` | `DoS.Exposure` | D13. Restricting the search for an equivocation to a view that holds `b` costs nothing: the witnesses … |
| `exposedIn_iff_reaches` | `DoS.Exposure` | — |
| `exposedTo_subset_byzantine` | `DoS.Exposure` | — |
| `history_subset_view` | `DoS.Exposure` | Causal history never escapes a view — T6a in `Finset` form. |
| `round_add_two_le_of_equivPair` | `DoS.Exposure` | D8. An equivocation shows up in a history only two rounds above the round it happened at. |
| `UniformBudget.byzBudget` | `DoS.Novelty` | Dropping a guard weakens nothing: the author-blind cap implies the Byzantine-side budget with the same … |
| `card_byzPool_succ_le` | `DoS.Novelty` | The accounting step. A Byzantine block enters the pool only as a direct budgeted acceptance: if it arrived … |
| `card_byzPool_zero_le` | `DoS.Novelty` | Round 0 seeds the pool with at most `f` Byzantine geneses per correct validator. |
| `card_filter_correct_le` | `DoS.Novelty` | One acceptance per author: the frontier splits into at most `|Correct|` correct-authored blocks… |
| `card_filter_not_correct_le` | `DoS.Novelty` | …and at most `f` Byzantine-authored ones. |
| `card_history_le_card_add_card_novelty` | `DoS.Novelty` | A history costs at most the view plus the novelty. |
| `card_history_le_of_stepNovelty` | `DoS.Novelty` | The telescope. Under `StepNovelty`, a correct author's history is linear: `|H(b)| ≤ κ'·r + 1`. Descent … |
| `card_history_le_of_stepNovelty_aux` | `DoS.Novelty` | — |
| `card_novelty_le_of_byzBudget` | `DoS.Novelty` | C3″ — the correct side of the budget is a theorem. A validator enforcing only the Byzantine clause `κ` … |
| `card_novelty_le_viewGap_add_one` | `DoS.Novelty` | C3a. After `R`, a block built from `w`'s acceptances is, at any correct `v`, at most one plus the gap … |
| `card_viewGap_succ_le` | `DoS.Novelty` | C3′ — the gap is constant, not a drift. After `R`, as long as the author has a current block (which L1 … |
| `card_viewUpto_succ_le_of_bounds` | `DoS.Novelty` | The generic one-round step: any per-block novelty bounds on the correct and Byzantine acceptances bound … |
| `dos_resistance` | `DoS.Novelty` | DoS resistance, from enforceable conditions only. Liveness and linear storage from round 0 under full … |
| `dos_resistance'` | `DoS.Novelty` | The post-`R` incremental form of the headline: the same enforceable conduct, plus the network's … |
| `history_eq_singleton_of_round_zero` | `DoS.Novelty` | A genesis history is a singleton — round 0 needs no budget clause. |
| `novelty_anti` | `DoS.Novelty` | Antitone in the view — the load-bearing property. Deferral is a rate limiter, not a verdict: as the view … |
| `round_le_of_mem_viewUpto` | `DoS.Novelty` | Nothing retained by round `n` sits above round `n`. |
| `sum_novelty_not_correct_le` | `DoS.Novelty` | The Byzantine spend of one round: at most `f` acceptances, `κ` each. |
| `uniform_of_byzBudget` | `DoS.Novelty` | The sandwich, converse direction. After `R`, a `ByzBudget κ` schedule is uniformly budgeted at `f·κ + 1` … |
| `viewUpto_zero` | `DoS.Novelty` | — |
| `adoptedUnder_unique` | `DoS.Pedigree` | The adoption collapse, packaged: one adopted top per (adopter, author). |
| `card_historyBlocksOf_le` | `DoS.Pedigree` | C1′, in full. Under `DoSValid` with self-parents, an author contributes at most `c(f) = (3f+2)^(3f+1)` … |
| `card_historyBlocksOf_le'` | `DoS.Pedigree` | C1′, tightened. The per-round contribution of any author to any history is at most `1 + 3f·f^(f-1)` — down … |
| `card_historyBlocksOf_le_card_topsOf` | `DoS.Pedigree` | An author's per-round contribution never exceeds its chain count: each round-`n` block sits on the chain … |
| `card_history_le` | `DoS.Pedigree` | The general bound. Every DoS-valid history is linear in its round, at every fault budget: |
| `card_history_le'` | `DoS.Pedigree` | The tightened total. `|H(b)| ≤ (3f+1 + 3f^(f+1))·(r+1)`: the unexposed authors contribute one chain each, … |
| `card_topsOf_le_of_exposed` | `DoS.Pedigree` | The tightened top count. With `e := |exposedTo U b|`, an exposed author has at most `(3f+1-e) · e^(e-1)` … |
| `card_topsOf_le_one_of_not_exposedIn` | `DoS.Pedigree` | An unexposed author has at most one chain. Two tops would be chain-related, and the lower would have a … |
| `card_topsOf_le_pow` | `DoS.Pedigree` | The general top count. A top is determined by its own author and its pedigree's duplicate-free author … |
| `encodeList_injOn` | `DoS.Pedigree` | The encoding is faithful. Two lists over `E'` of length at most `m` with the same encoding are equal: the … |
| `exists_child_of_mem_history_of_creator_eq` | `DoS.Pedigree` | A same-author block strictly inside a history is on the root's chain (D21/D22), so it has a same-author … |
| `exists_pedigree` | `DoS.Pedigree` | Pedigrees exist, with fresh authors all the way. Every top climbs to `b` through adopters whose authors, … |
| `exists_pedigreeVia` | `DoS.Pedigree` | Anchored pedigrees exist. The top of an *exposed* author climbs through exposed-author adopters to the … |
| `exists_pedigree_data` | `DoS.Pedigree` | Every top has an anchored pedigree, in totalised form. |
| `pedigreeVia_cons_inv` | `DoS.Pedigree` | — |
| `pedigreeVia_deterministic` | `DoS.Pedigree` | Anchored determinism: given the anchor and the intermediate author list, the top is unique. |
| `pedigreeVia_nil_inv` | `DoS.Pedigree` | — |
| `pedigreeVia_spec` | `DoS.Pedigree` | Every recorded author is realised by a top strictly above the subject, containing it — the nesting that … |
| `pedigreeVia_top` | `DoS.Pedigree` | — |
| `pedigree_cons_inv` | `DoS.Pedigree` | Inverting one pedigree step against a cons list. |
| `pedigree_deterministic` | `DoS.Pedigree` | Pedigrees determine. Two tops of one author with the same pedigree author-list are equal: each step … |
| `pedigree_spec` | `DoS.Pedigree` | Every author on a pedigree is realised by a *top* strictly above the pedigree's base, whose history … |
| `self_mem_topsOf` | `DoS.Pedigree` | The block itself tops its own chain: nothing in its history can reference it. |
| `card_filter_creator_of_mem_refs` | `DoS.SelfParent` | D23, totalled. For any *other* author the block references, the cost is exactly `round` blocks: rounds `0` … |
| `card_filter_self_creator` | `DoS.SelfParent` | D22, totalled. The own-author content of a history is exactly `round + 1` blocks — one per round, the … |
| `card_historyBlocksOf_of_mem_refs` | `DoS.SelfParent` | D23, per round. Referencing a block puts its author into the history exactly once per round strictly below … |
| `card_historyBlocksOf_self` | `DoS.SelfParent` | D22, per round. A block's own author sits in its history *exactly once* per round: at least once by the … |
| `card_history_ge` | `DoS.SelfParent` | D24 (the floor). With self-parents, histories have a *minimum* size: a valid block at round `r` carries at … |
| `exists_self_ancestor_aux` | `DoS.SelfParent` | — |
| `correct_mem_base` | `GC.AttestedBase` | G10, completeness. Post-`R`, every correct block of the layer is in every correct attestation (the … |
| `accepted_mem_base` | `GC.Bootstrap` | G11. Every round-`G` block a correct validator accepted into its window by `m` — Byzantine-authored … |
| `base_subset_retained` | `GC.Bootstrap` | The base is inside every correct peer's retained store: each base block sits in a correct attester's cone … |
| `bootstrap_agree` | `GC.Bootstrap` | G12 (bootstrap safety). A joiner that assembles its view from the attested base and a correct peer's … |
| `card_base_le` | `GC.Bootstrap` | The base alone is bounded by the G6 constant. |
| `card_joinIds_le` | `GC.Bootstrap` | G6b. The joiner's entire fetch is inside one correct peer's retained store, hence bounded by the G6 … |
| `card_serve_le` | `GC.Bootstrap` | G7, priced. Serving cost is the G6 constant plus one. |
| `history_chop_subset_retained` | `GC.Bootstrap` | G7. The windowed relay obligation: everything a correct author can be asked to serve for its block — the … |
| `history_subset_insert_viewUpto` | `GC.Bootstrap` | A correct author's cone is its own retained store plus the block itself: `RefsAccepted` one step down, S10 … |
| `joinView_ids` | `GC.Bootstrap` | — |
| `mem_viewUpto_of_mem_refs` | `GC.Bootstrap` | A retained store is closed under references: whatever cone brought `i` also holds everything `i` references. |
| `blames_chop` | `GC.Chop` | — |
| `certifies_chop` | `GC.Chop` | — |
| `chopBlock_refs_subset` | `GC.Chop` | The truncation's references never exceed the original's. |
| `directCommit_chop` | `GC.Chop` | — |
| `directSkip_chop` | `GC.Chop` | — |
| `dosValid_chop` | `GC.Chop` | G1, DoS half — the one-way door. The condition survives truncation; the converse fails by design (the … |
| `exposedIn_of_exposedIn_chop` | `GC.Chop` | Exposure in the truncation is exposure in the original: the witnessing pair survives un-rebasing. |
| `reaches_chop_iff` | `GC.Chop` | — |
| `reaches_chop_of_reaches` | `GC.Chop` | A path of the original whose endpoint stays at or above the cut never dips below it, so it survives … |
| `reaches_of_reaches_chop` | `GC.Chop` | A step in the truncation is a step in the original. |
| `supporters_chop` | `GC.Chop` | — |
| `votesIn_chop` | `GC.Chop` | — |
| `Slots.chop_leader` | `GC.ChopDecided` | — |
| `Slots.chop_slotRound` | `GC.ChopDecided` | — |
| `View.chop_ids` | `GC.ChopDecided` | — |
| `anchor_mem_chop_ids` | `GC.ChopDecided` | The anchor of a decided slot at or past the base slot survives the cut. |
| `certificatesIn_chop` | `GC.ChopDecided` | The view filter is invisible to the certificate count: certificates for a slot above the cut live two … |
| `decided_chop` | `GC.ChopDecided` | G3. The decision relation survives the cut, both ways: a validator re-running Mysticeti on the truncation, … |
| `decided_chop_of_decided` | `GC.ChopDecided` | Backward: the original decision is reached on the truncation. Stated over an arbitrary slot `n = d + k` so … |
| `decided_of_decided_chop` | `GC.ChopDecided` | Forward: a decision reached on the truncation, from a truncated view, is the original decision. Structural … |
| `directCommitIn_chop` | `GC.ChopDecided` | — |
| `directSkipIn_chop` | `GC.ChopDecided` | — |
| `eligible_chop` | `GC.ChopDecided` | — |
| `horizon_le_slotRound` | `GC.ChopDecided` | Every slot from the base slot on clears the horizon. |
| `isLeaderBlock_chop` | `GC.ChopDecided` | — |
| `block_eq_of` | `GC.Horizon` | — |
| `chopBlock_chop` | `GC.Horizon` | — |
| `chop_chop` | `GC.Horizon` | G8, the composition law. A deeper cut is just another cut: two admissible horizons are always related by … |
| `decided_agree_horizons` | `GC.Horizon` | G8. Validators truncated at *different* horizons agree on every shared slot, from arbitrary views of their … |
| `pruned_subset_peer_store` | `GC.Horizon` | G9 (no desync). What a validator prunes at any horizon, every correct peer already holds one round later: … |
| `universe_eq_of` | `GC.Horizon` | — |
| `viewUpto_subset_viewUpto_succ` | `GC.Horizon` | G9, the engine. Post-`R`, everything any correct validator retains by round `m` is in every correct … |
| `byzBudget_chopD` | `GC.Window` | — |
| `history_chop_anti` | `GC.Window` | Advancing the cut only shrinks cones… |
| `novelty_chop_anti` | `GC.Window` | …so it only shrinks novelty: pruning cheapens blocks — an affordable block never becomes unaffordable as … |
| `populated_chop` | `GC.Window` | G5. The truncated universe never stalls above the cut. |
| `refsAccepted_chopD` | `GC.Window` | — |
| `viewUpto_chopD` | `GC.Window` | G14. The truncated store *is* the store of the truncation: pruning below `G` and accumulating in the … |
| `historyUpto_mono` | `History` | More fuel never loses anything. Needed because `mem_history_iff` fixes the fuel at `round + 1` while the … |
| `historyUpto_succ` | `History` | — |
| `historyUpto_zero` | `History` | — |
| `mem_historyUpto_of_reaches` | `History` | Completeness, with the fuel accounted for. A path from `b` drops the round by one per step (T2), so `round … |
| `mem_historyUpto_self` | `History` | — |
| `mem_historyUpto_succ` | `History` | — |
| `reaches_of_mem_historyUpto` | `History` | Soundness. Anything the fuelled search finds really is reachable. No hypothesis on `b`: even off the … |
| `FairRunOn.fairScheduleOn` | `Liveness` | A run of `c` slots contains a `T`-led slot, so `FairRunOn` refines `FairScheduleOn` and everything proved … |
| `PopulatedOn.mono` | `Liveness` | Population is antitone: a smaller set is easier to populate. This is what lets L1 keep concluding about … |
| `SynchronisedOn.mono` | `Liveness` | Coverage is antitone too: mutual coverage among a larger set implies it among any subset. So existing … |
| `all_decided_below_of_fairRun` | `Liveness` | L10. For every slot `k` there is a `b ≥ k` such that every slot below `b` is decided, in any sufficiently … |
| `all_decided_below_of_fairRun_correct` | `Liveness` | L10 at `T := Correct`. |
| `all_decided_below_of_spacing` | `Liveness` | L8 under the old three-round spacing. Combining L6 with L8: for every slot `k` there is a slot `n ≥ k` … |
| `card_authorsAt_of_succ` | `Liveness` | One step of L0: a block at round `n+1` forces a quorum of authors at round `n`. |
| `certificatesIn_full` | `Liveness` | — |
| `certifies_of_synchronisedOn` | `Liveness` | A correct round-`(r+2)` block certifies any correct round-`r` block, once round `r+1` is populated and … |
| `commits_recur_on` | `Liveness` | L6 — commits recur. For every slot `k` there is a later slot `k'` that every sufficiently grown … |
| `decided_full` | `Liveness` | L3 — commit propagation. Whatever any validator decides on any view, the same verdict holds on the full view. |
| `decided_mono` | `Liveness` | L2 — decisions are monotone in the view. If `V ⊆ V'` then `Decided U V k v → Decided U V' k v`. |
| `decided_none_of_no_candidate` | `Liveness` | L5, in the form the `Decided` constructor wants. |
| `decided_of_committed_above` | `Liveness` | L8. Given a committed slot, every slot below it is decided — provided every later slot may anchor an … |
| `decided_of_first_eligible_commit` | `Liveness` | The escape. If `j` is committed and *nothing strictly between `k` and `j` is eligible to anchor `k`*, then … |
| `decided_of_leader_of_populated` | `Liveness` | L4, against a horizon. The form every capstone uses: production is available as a single `Populated` … |
| `directCommitIn_mono` | `Liveness` | A larger view can only see more certificates. |
| `directCommit_of_synchronisedOn` | `Liveness` | L4, at the round level. A correct block at round `r` is directly committed, given coverage from `r` and … |
| `directSkipIn_mono` | `Liveness` | A larger view can only see more blame. |
| `exists_eligible` | `Liveness` | Every slot has an eligible anchor somewhere. |
| `exists_isLeaderBlock` | `Liveness` | A correct leader has a candidate block, once its round is populated. `Populated` at the leader's own round … |
| `exists_mem_of_authorsAt_card_pos` | `Liveness` | A round with any author at all has a block. The bridge that lets L0's induction step back down: a … |
| `exists_slotRound_ge` | `Liveness` | Some slot sits at or beyond any given round. |
| `notMem_stuck_of_decided` | `Liveness` | L9. Nothing in a stuck set is ever decided, on any view. |
| `stuck_empty_below_commit_of_spacing` | `Liveness` | L8 and L9 are consistent, and their hypotheses are jointly exhaustive. |
| `anchor_eq` | `Mysticeti` | The anchor comparison. Two indirect decisions for one slot each name an anchor, together with the premise … |
| `certificates_eq_empty_of_directSkip` | `Mysticeti` | M3. A directly skipped block has no certificate anywhere in the universe — not merely none in some view. |
| `certifiedIn_iff_of_view` | `Mysticeti` | The indirect test is view-independent: a validator holding the anchor computes the same verdict from its … |
| `certifiedIn_of_directCommit` | `Mysticeti` | M4, commit half. A directly committed block is found by *every* anchor from round `r+3` on. This is M2 … |
| `certifiedIn_of_directCommitIn` | `Mysticeti` | The engine of M6. A direct commit made in *any* view is visible from *every* later slot's leader block. A … |
| `certifiedIn_of_directCommitIn_at_anchor` | `Mysticeti` | Visibility from an anchor. A slot committed directly is certified at any eligible anchor above it: the … |
| `commitSeq_agree` | `Mysticeti` | The committed-leader sequence is agreed. Two validators that have settled the first `n` slots — on … |
| `decided_agree` | `Mysticeti` | M6, in the shape callers want: two validators' verdicts for a slot agree. |
| `directSkip_of_directSkipIn` | `Mysticeti` | — |
| `eq_of_certificates_nonempty` | `Mysticeti` | M5′ (certificate uniqueness). A slot admits at most one *certifiable* block: if certificates exist for two … |
| `eq_of_decided_commit` | `Mysticeti` | No two validators commit *different* blocks for one slot. |
| `eq_of_directCommitIn` | `Mysticeti` | Cross-view M5: two validators cannot directly commit *different* blocks for one slot. Both candidates are … |
| `eq_of_directCommit_of_creator_eq` | `Mysticeti` | M5. At most one block per slot is directly committed. |
| `eq_of_hasCertificate` | `Mysticeti` | Two commits for one slot agree, however each was reached. Both routes yield a certificate, so this is M5′ … |
| `exists_certificate_reaches_of_directCommit` | `Mysticeti` | M2. Once a block is directly committed, its certificate becomes unavoidable: every block from round `r+3` … |
| `indirect_agrees_with_direct` | `Mysticeti` | M4. Where the direct rule decides, the indirect rule agrees. |
| `ledgerSet_agree` | `Mysticeti` | Two validators output the same blocks. |
| `ledgerSet_mono` | `Mysticeti` | Nothing is ever dropped. The ledger only grows as more slots settle. |
| `mem_votesIn_spec` | `Mysticeti` | A vote counted by a round-`(r+2)` certificate really is a round-`(r+1)` block of the universe that … |
| `not_certifiedIn_of_directSkip` | `Mysticeti` | M4, skip half. A directly skipped block is found by *no* anchor whatsoever — no round hypothesis needed, … |
| `not_certifiedIn_of_directSkipIn` | `Mysticeti` | A direct skip made in any view is invisible from every anchor — no round hypothesis needed, since M3 rules … |
| `not_decided_skip_of_decided_commit` | `Mysticeti` | No validator commits a slot another has skipped. This is the shape that matters operationally: a committed … |
| `not_directCommit_of_directSkip` | `Mysticeti` | M1. No block is both directly committed and directly skipped. |
| `not_directSkipIn_of_directCommitIn` | `Mysticeti` | Cross-view M1: one validator cannot directly commit what another directly skips. |
| `not_directSkip_of_directCommitIn` | `Mysticeti` | Direct decisions agree across views. If one validator directly commits a slot, no other validator can … |
| `outputAt_agree` | `Mysticeti` | And validators agree on which slot that is. |
| `outputAt_unique` | `Mysticeti` | A block enters the ledger once. Its position is not merely stable over time — there is no second slot it … |
| `slot_eq_of_decided_commit` | `Mysticeti` | And so a committed block belongs to one slot. The ledger reads verdicts off in slot order, so without this … |
| `slot_eq_of_isLeaderBlock` | `Mysticeti` | A block is the candidate of at most one slot. |
| `card_authorsAt_of_live` | `Network.Quorum` | L1 in the form L0 consumes: under `Live U D N` every round up to the horizon carries a quorum of authors, … |
| `deliversQuorum_chopD` | `Network.Quorum` | — |
| `live_chopD` | `Network.Quorum` | — |
| `no_stall_and_card_viewUpto_le` | `Network.Quorum` | The capstone, unconditional. `EventuallyDelivers` is gone: growth plus quorum delivery give liveness (L1 … |
| `no_stall_and_card_viewUpto_le'` | `Network.Quorum` | The composed statement — DoS resistance in one theorem. One set of hypotheses — growth (`Live`), quorum … |
| `anchor_round_le` | `Odontoceti.Decision` | The anchor's round clears the slot's decision round by one — enough for O3 to read the whole certificate … |
| `decided_unique` | `Odontoceti.Decision` | O5 (thesis Lemma 5; the M6 analogue). No two validators reach conflicting decisions for a slot, whatever … |
| `directCommit_of_directCommitIn` | `Odontoceti.Decision` | A view can only under-report: its direct commit is genuine. |
| `directSkip_of_directSkipIn` | `Odontoceti.Decision` | A view can only under-report: its direct skip is genuine. |
| `eq_of_directCommitIn` | `Odontoceti.Decision` | Cross-view O1′: two direct commits for one slot agree. |
| `eq_of_directCommitIn_of_thickLink` | `Odontoceti.Decision` | O4′, from a view: a view-level direct commit is the only same-slot candidate that can pass the indirect … |
| `isLeaderBlock_of_decided` | `Odontoceti.Decision` | A committed slot's block is a candidate of that slot. |
| `not_directSkipIn_of_directCommitIn` | `Odontoceti.Decision` | Cross-view O1: one validator cannot directly commit what another directly skips. |
| `not_thickLink_of_directSkipIn` | `Odontoceti.Decision` | O2, from a view: a view-level direct skip fails the indirect test everywhere. |
| `safety` | `Odontoceti.Decision` | O6 (safety). Two committed blocks for one slot are the same block, across any two views and any two routes. |
| `thickLink_of_directCommitIn` | `Odontoceti.Decision` | O3, from a view: a view-level direct commit passes the indirect test at every block two rounds up. |
| `thickLink_of_directCommitIn_at_anchor` | `Odontoceti.Decision` | Visibility from an anchor. A slot committed directly carries a thick link at any eligible anchor above it … |
| `all_decided_below_of_fairRun` | `Odontoceti.Liveness` | O10 (thesis Theorem 12). Under `Live`, `DeliversQuorum`, and post-`R` synchrony, a recurring run of `c` … |
| `all_decided_below_of_fairRun_correct` | `Odontoceti.Liveness` | O10 at `T := Correct`. |
| `decided_below_of_committed_run` | `Odontoceti.Liveness` | O9 (thesis Lemma 11). Every slot below a committed run of eligible span is decided: walk down from the … |
| `decided_of_correct_leader` | `Odontoceti.Liveness` | The same at `T := Correct`. |
| `decided_of_leader_mem` | `Odontoceti.Liveness` | O7, as a decision. |
| `decided_of_leader_of_populated` | `Odontoceti.Liveness` | O7 against a horizon, the two-round counterpart of `decided_of_leader_of_populated`: the rule needs the … |
| `directCommitIn_full` | `Odontoceti.Liveness` | — |
| `directCommit_of_leader_mem` | `Odontoceti.Liveness` | O7, commit half (thesis Lemma 8 + Corollary 9). Post-`R`, a `T`-led slot is directly committed: … |
| `spansEligible_two` | `Odontoceti.Liveness` | O8. Under a pipelined identity-round schedule, `c = 2` spans: slot `b − 1` cannot anchor on slot `b` — one … |
| `supportersIn_full` | `Odontoceti.Liveness` | The full view sees every supporter. |
| `card_supporters_le_of_directSkip` | `Odontoceti.Rules` | O2, the counting half. A directly skipped leader's supporters — anywhere in the universe — number at most … |
| `coneSupports_subset_of_reaches` | `Odontoceti.Rules` | Cones nest, so in-cone support does. |
| `coneSupports_subset_supporters` | `Odontoceti.Rules` | In-cone supporters are supporters. |
| `mem_coneSupports` | `Odontoceti.Rules` | — |
| `not_correct_of_supports_and_blames` | `Odontoceti.Rules` | A validator that both supports and blames `L` has two distinct blocks at the decision round, so it is not … |
| `not_correct_of_supports_two` | `Odontoceti.Rules` | A validator supporting two *distinct* same-author blocks is not correct: one supporting block cannot … |
| `thickLink_of_directCommit_aux` | `Odontoceti.Rules` | — |
| `mem_ids_and_round_of_quorum_support` | `Persistence` | The quorum hypothesis already forces `b` into the universe at round `r`, so T3 need not assume either. A … |
| `reaches_of_quorum_support` | `Persistence` | T3 (Persistence). If `b` is referenced by a quorum of round-`(r+1)` blocks, every block at round `r+2` or … |
| `chain_quality` | `Quality.Capstone` | CQ7 (the capstone). Chain quality in one statement, enforceable or standard conditions only. … |
| `committed_of_correct_block_by_round` | `Quality.Capstone` | CQ7, by round. With bounded slot spacing, the committing slot's round is within `s·w` rounds of the first … |
| `committed_of_correct_block_within` | `Quality.Capstone` | CQ7, windowed. Under a windowed-fair schedule, the committing slot for round-`m` blocks lies within `w` … |
| `slotAt_le_slotAt` | `Quality.Capstone` | The least slot at or above a round is monotone in the round. |
| `card_coveredAt_ge` | `Quality.Coverage` | CQ1, the count. A valid block's cone covers all but at most `f` of the correct validators, at every round … |
| `card_coveredAt_ge_of_decided` | `Quality.Coverage` | CQ1. A committed leader's flush covers all but at most `f` of the correct validators at every round below … |
| `coveredAt_eq_sdiff` | `Quality.Coverage` | Covered and missing partition the correct validators. |
| `coveredAt_subset_correct` | `Quality.Coverage` | — |
| `ledger_coverage` | `Quality.Coverage` | CQ3 (ledger coverage, cumulative). For a verdict assignment `g` of a view with a committed slot `k < n` … |
| `mem_coveredAt` | `Quality.Coverage` | — |
| `committed_of_correct_block_correct` | `Quality.Inclusion` | CQ6 at `T := Correct`. |
| `FairWithin.fairScheduleOn` | `Quantitative` | A rated schedule is a fair one, so everything already proved from `FairScheduleOn` applies to it unchanged. |
| `Timing.populatedOn` | `Quantitative` | `Timing` already asserts a block per `T`-validator per round below the horizon, so it populates rounds … |
| `backoff_ge_of_rate` | `Quantitative` | A rated backoff clears any threshold by the threshold itself. |
| `commits_recur_within` | `Quantitative` | Q4, the schedule half. L6 with the committing slot bounded. |
| `directCommit_of_wait` | `Quantitative` | The wait bound. After GST, a correct leader is committed provided every `T`-validator waits at least `D₀ + … |
| `slotRound_le_of_lt` | `Quantitative` | A slot bound becomes a round bound. |
| `unbounded_of_rated` | `Quantitative` | Every rated backoff is unbounded, so `Rated` really is a strengthening of `exists_backoff_ge`'s hypothesis … |
| `one_hblock` | `Schedule` | With one leader per round the distinctness condition is vacuous: slots in a round are the round, so no two … |
| `uniformSingle_slotRound` | `Schedule` | — |
| `uniformSingle_spacing` | `Schedule` | The old `spacing` field, recovered. Consecutive slots of `uniformSingle 3` really are three rounds apart, … |
| `uniform_leader` | `Schedule` | — |
| `uniform_slotRound` | `Schedule` | — |
| `blames_inter_supporters_subset_byzantine` | `Support` | A correct validator cannot both vote for `L` and blame it: that would be two distinct round-`n` blocks by … |
| `card_authorsAt_le_univ` | `Support` | The author pool never exceeds the validator set. This is what turns the `p - 2f` threshold into the … |
| `exists_mem_refs_of_correct_support` | `Support` | The hitting lemma. A round-`(n+1)` block cannot avoid referencing a block satisfying `P`, once `f+1`-or-so … |
| `supporters_subset_authorsAt` | `Support` | — |
| `DriftFrom.mono` | `Timing` | Drift from a later round is implied by drift from an earlier one. |
| `exists_backoff_ge` | `Timing` | A backoff that grows without bound eventually clears any fixed threshold. |
| `card_inter_ge_of_quorum` | `Validators` | T0 (cardinality half). Two quorums overlap in at least `f+1` validators: `(n−f) + (n−f) − n = n − 2f ≥ f+1`. |
| `faults_arith` | `Validators` | The standing arithmetic of the fault model, in the form `omega` consumes it: the correct and Byzantine … |
| `Timing.driftFrom_iff_driftOn` | `ViewSync` | — |
| `ViewSync.convergesEventually` | `ViewSync` | Every `ViewSync` converges in the qualitative sense too — the bound is extra information, not a different … |
| `ViewSync.convergesWithin` | `ViewSync` | The `converges` field *is* the bounded form — the definition is the field, unfolded. |
| `all_decided_below_of_converges` | `ViewSync` | L10 on this foundation. Every slot below a committed run is decided, so the ledger does not stall — again … |
| `blk_mem_holds` | `ViewSync` | Build-time views agree, from `R` on. Every `T`-authored round-`n` block is in *every* `T`-validator's … |
| `commits_recur_of_converges` | `ViewSync` | L6 on this foundation. Commits recur: for every slot there is a later one, past any given bound on GST, … |
| `convergesEventually_of_within` | `ViewSync` | A bounded lag is a lag: the timed form implies the untimed one, even before `gst`, since holdings only grow. |
| `convergesWithin_iff_bounded` | `ViewSync` | The factoring. Under monotone holdings, convergence within a bound and bounded eventual convergence are … |
| `convergesWithin_of_bounded` | `ViewSync` | And conversely: eventual convergence whose lag is uniformly bounded after `gst` *is* convergence within … |
| `covers_of_converges` | `ViewSync` | The derivation. `Timing.covers` — a `T`-block built after GST and early enough is referenced — follows … |
| `decided_of_leader_of_converges` | `ViewSync` | L4 on this foundation. A `T`-led slot past GST is committed, given only view convergence, the referencing … |
| `eventuallyDelivers_of_viewsConverge` | `ViewSync` | Untimed view convergence is `EventuallyDelivers` from round `0`: the author holds its own block, and … |
| `exists_blk_of_populatedOn` | `ViewSync` | `blk` is `PopulatedOn`, Skolemised. A population of every round below the horizon yields a function naming … |
| `exists_synchronisedOn_of_converges` | `ViewSync` | And with an unbounded backoff, from some round on — the `ViewSync` form of L7b's headline, with drift … |
| `holdsOwn_toDelivery` | `ViewSync` | A validator holds its own block when it builds the next, in the induced delivery — `HoldsOwn` relative to `T`. |
| `holdsOwn_toDelivery'` | `ViewSync` | `HoldsOwn`, in full. With `T = Correct` the induced delivery satisfies the clause outright, at every … |
| `le_built_of_waits` | `ViewSync` | Rounds advance real time — `Timing.le_built`'s argument over a schedule alone, for the same reason. |
| `populated_of_viewsConverge` | `ViewSync` | L1 without N1. Under untimed view convergence, every round below the horizon is populated — the conclusion … |
| `synchronised_toDelivery` | `ViewSync` | And hence coverage, the second way. `synchronised_of_delivery` (L7a) applies to the induced delivery, so … |
| `toTiming_built` | `ViewSync` | — |
| `toTiming_delay` | `ViewSync` | — |
| `toTiming_gst` | `ViewSync` | — |
| `toTiming_timeout` | `ViewSync` | — |
| `toViewSync_built` | `ViewSync` | — |
| `toViewSync_delay` | `ViewSync` | — |
| `toViewSync_gst` | `ViewSync` | — |
| `toViewSync_timeout` | `ViewSync` | — |
| `viewsAgree_of_converges` | `ViewSync` | The bridge, with the protocol clause made explicit. |
| `viewsConvergeOn_toDelivery` | `ViewSync` | The untimed condition, derived. From `R` on, the induced delivery satisfies view convergence relative to `T`. |
| `viewsConverge_of_viewsConvergeOn` | `ViewSync` | At `T = Correct` and `R = 0` the relative condition is the original. |

<!-- END GENERATED REFERENCE -->
