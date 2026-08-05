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
> *(ii) We propose* **eventual DAG synchrony**, *a structural assumption on the
> DAG: beyond some round, every correct block references every correct block of
> the round below.*
>
> *(iii) We give a machine-checked development of safety and liveness for a
> Mysticeti-style commit rule above this assumption, in which no theorem
> mentions time.*
>
> *(iv) We discharge the assumption from the standard partial-synchrony model,
> so that it is a reformulation rather than a strengthening.*
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
   round below. The statement mentions no clock, no message and no Δ.

2. A machine-checked **safety** development — agreement, uniqueness of the
   committed leader sequence, and non-retraction of the ledger — which assumes
   nothing whatsoever about the network, not even eventual delivery.

3. A machine-checked **liveness** development above the structural assumption,
   in which no theorem mentions time.

4. **Two independent discharges** of the structural assumption: from an abstract
   delivery model (§6.7), and from GST together with two protocol build rules
   (§6.8). The assumption is therefore a reformulation of standard hypotheses
   rather than a new one.

5. An analysis of what the natural **view-based** formulation of the assumption
   does and does not supply (§7.1): a delivery guarantee alone does not yield
   reference coverage without a rule governing *when* validators build; and
   because a block's references are fixed at construction, the guarantee must be
   indexed to the moment of building.

6. **Quantitative forms** (§6.10): the round from which coverage holds, given
   explicitly; a bound on the slot at which the next commit occurs; and an
   operational statement — a correct leader is committed once every correct
   validator waits `D₀ + Δ`, which is `2Δ` under a common start.

### 1.4 Scope and non-goals

The development is deliberately bounded in four respects.

- **No cryptography.** Signatures, authentication and equivocation detection are
  outside the model. Non-equivocation of correct validators is a modelling
  assumption (§2.3), not a mechanism.
- **No executions.** The object of study is a DAG together with invariants, not
  a transition system with traces. What an operational model would establish as a
  reachability invariant is here discharged by assumption.
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

`Correct` is a set complement and carries no behavioural content. It is
satisfied, in particular, by a validator that crashes at round 0 and never
speaks again. This is deliberate: it is what allows every safety result to hold
of crashed validators, and it is the reason the liveness development must
introduce positive rules explicitly (§6.0). It is also the reason
non-equivocation must be assumed rather than derived (§2.3): nothing else in the
model constrains the behaviour of a correct validator.

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
encoded on the safety side. In modelling terms it is where the statement "this
DAG arose from an execution in which correct validators followed the protocol"
is recorded.

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
one. It also determines the shape of the growth assumption (§6.3).

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

## 4. Assumptions

### 4.1 Safety

| | Assumption | Character | Formalisation |
|---|---|---|---|
| A1 | there are `3f+1` validators | fault model | `Faults.card_validators` |
| A2 | at most `f` are Byzantine | fault model | `Faults.card_byzantine` |
| A3 | references lie one round below | well-formedness | `ValidWrt.predecessor` |
| A4 | no block cites one author twice | well-formedness | `ValidWrt.distinct_creators` |
| A5 | non-genesis blocks cite `2f+1` distinct authors | well-formedness | `ValidWrt.quorum` |
| A6 | referenced blocks exist | well-formedness | `BlockUniverse.complete` |
| A7 | correct validators do not equivocate | fault model | `BlockUniverse.no_equivocation` |
| A8 | slots are at least three rounds apart | protocol parameter | `Slots.spacing` |

No assumption about the network appears. The safety results of §5 hold under
arbitrary asynchrony, arbitrary message loss and arbitrary divergence between
views.

None of A1–A8 is an axiom in the logical sense. A1, A2 and A8 are fields of the
classes `Faults` and `Slots`, and A3–A7 fields of `ValidWrt` and
`BlockUniverse`; every theorem quantifying over a universe or over those
instances therefore carries them as antecedents. Their joint satisfiability is
consequently a proof obligation, discharged by exhibition (§8), rather than
something the logic must be trusted for.

### 4.2 Liveness

| | Assumption | Character | Formalisation |
|---|---|---|---|
| B1 | correct validators possess genesis blocks | protocol | `Live.genesis` |
| B2 | holding a quorum, a correct validator builds (below `N`) | protocol | `Live.builds` |
| B3 | a quorum that exists is eventually held | network (asynchronous) | `DeliversQuorum` |
| B4 | a correct block references everything its author held | protocol | `Delivery.includes` |
| B5 | eventual DAG synchrony beyond round `R` | structural | `SynchronisedOn` |
| B6 | the schedule names a `T`-leader arbitrarily far out | schedule | `FairScheduleOn` |
| B7 | `T ⊆ Correct` and `2f+1 ≤ T.card` | fault budget | hypotheses of L4, L6 |

B3 and B4 require eventual delivery only, not synchrony, and are what carry the
results that hold before GST.

Assumption B5 is discharged by two independent routes:

| Route | Discharging assumptions | Character | Result |
|---|---|---|---|
| Delivery | `EventuallyDelivers`, with B4 | network | `synchronised_of_delivery` |
| Timing | `Timing.covers` (GST and Δ) | network | `synchronisedOn_of_timing` |
| | `Timing.waits`, `Timing.prompt` | protocol | |

### 4.3 Quantitative assumptions

The following are required only for the results of §6.10. Each strengthens an
assumption already in play, and every result of §5 and §6.1–§6.9 stands without
them.

| | Assumption | Yields |
|---|---|---|
| R1 | `Rated timeout`, i.e. `∀ n, n ≤ timeout n` | an explicit round `R` |
| R2 | `FairWithin T w`: a `T`-leader within every window of `w` slots | a bounded committing slot |
| R3 | `BoundedSpacing s`: slots at most `s` rounds apart | that slot's round, and a horizon |
| R4 | round-`0` spread at most `D₀`, and `∀ n, D₀ + Δ ≤ timeout n` | the wait bound `Delay(Δ)` |

### 4.4 The combined fault budget

Assumption B7 merits separate comment. The principal liveness argument counts to
`2f+1` and no higher, so what it requires is a *quorum of reliable* validators
rather than the participation of every correct one. Formulating it as
`T ⊆ Correct` together with `2f+1 ≤ T.card` yields the operative budget:

> `actual_byzantine + persistently_slow_correct ≤ f`

A correct validator which is persistently slow consumes fault budget exactly as
a Byzantine one does. At `f = 1` there are four validators and
`|Correct| = 3 = 2f+1` exactly, so no slack exists: every correct validator must
belong to the reliable set. Slack appears only when fewer than `f` validators are
in fact faulty, and the `T`-parameterised statements make it available
automatically. The specialisations at `T := Correct`
(`directCommit_of_correct_leader`, `decided_of_correct_leader`, `commits_recur`)
recover the conventional statements.

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
which is not itself a certificate reaches none. This is the origin of A8.

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
(T0′); `w`'s unique round-`(r+1)` block votes for both (T1); and `A4` forbids one
block from referencing two round-`r` blocks by a single author. This is the only
use of A4 in the development.

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

### 6.0 The insufficiency of `Correct`

Since `Correct` is a negative condition (§2.1), liveness statements are vacuous
without positive rules. Three primitives are introduced, and they differ in
character:

- **(a)** correct validators produce blocks — a protocol rule;
- **(b)** correct blocks cover the correct blocks below them — an *outcome* the
  protocol produces but cannot name (§7.2);
- **(c)** correct leaders recur — a property of the schedule.

Rules (a) and (b) act in opposition, and the timing layer brackets them
precisely: (a) is a floor, requiring that a validator eventually build
(`Timing.prompt`, an upper bound on build time); (b) is a delay, requiring that
it not build too early (`Timing.waits`, a lower bound).

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

The assumption is restricted to correct authors on both sides, and both
restrictions are load-bearing.

Nothing may be assumed about the existence of Byzantine blocks: a Byzantine
validator may publish nothing, or publish and reveal selectively, so no argument
may depend upon its blocks being available. Nothing need be assumed either, since
the commitment argument counts only correct certificates and the correct
validators form a quorum. The stronger reading — that every block is referenced —
would amount to assuming that Byzantine validators behave.

Well-formedness survives the restriction: a correct block referencing every
correct block of the round below already names at least `2f+1` distinct creators,
so A5 is satisfied without any Byzantine reference.

The predicate is antitone in `T` (`SynchronisedOn.mono`), which allows results
established at `T := Correct` to be supplied to the quorum-relative statements of
§6.6.

§7 is devoted to the discussion of this assumption.

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

### 6.7 Discharging the assumption: delivery

```lean
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ Correct, ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ Correct → a ∈ D.held v n

theorem synchronised_of_delivery (D : Delivery U) (h : EventuallyDelivers D R) :
    Synchronised U R
```

The proof is the chain `refs ⊇ held ⊇` every correct block below.

The gain is not logical: one assumption becomes two, and nothing becomes
unconditional. The gain is that each component is a single kind of thing.
`includes` is a protocol rule which an implementation can execute and an observer
can check; `EventuallyDelivers` is a pure network guarantee.

`EventuallyDelivers` is view convergence *indexed to the moment of building*: it
does not state that correct blocks eventually reach `v`, but that they are members
of `D.held v n`. That indexing performs the work, and it is exactly what a
view-shaped statement lacks (§7.1).

### 6.8 Discharging the assumption: timing

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

**The assumption, discharged.**
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

> *[Figure 3]* The layer diagram.
>
> ```
>   L6  commits recur           ─┐
>   L4  a correct leader commits │  no time appears in this region
>   L1  no stall                 │
>   L0  density                 ─┘
>        ▲
>        │  SynchronisedOn  — the interface
>        │
>   L7a  EventuallyDelivers (delivery model)
>   L7b  Timing: GST, Δ, waits, prompt
> ```

No theorem above the interface mentions time, and no theorem below it mentions
certificates.

### 6.10 Quantitative results

The results of this section are collected in a separate module which nothing else
imports. Each strengthens a result above and is purchased with a strengthened
hypothesis (§4.3); a reader declining those hypotheses retains §6.1–§6.9 intact.

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

`Timing.populatedOn` supplies the three population hypotheses of L4 from the
`Timing` structure itself, which already asserts a block per reliable validator
per round below the horizon. These statements consequently require neither
`Live`, nor `DeliversQuorum`, nor L1: their only temporal hypotheses are the
start spread, the wait, and the position of the slot relative to GST.

---

## 7. Discussion: eventual DAG synchrony

### 7.1 Relation to the view formulation

The assumption may be stated instead in terms of views:

> beyond GST, if a correct validator holds a view `V₁`, then within Δ the views
> of all correct validators contain `V₁`.

This formulation is attractive. `View` is already a first-class structure,
inclusion between views is already meaningful, and every safety result is already
view-relative. It yields L3 immediately, the common view being `View.full`.

It also yields reference coverage by the expected mechanism: rapid propagation
places every correct round-`n` block in every correct validator's possession, and
a validator which waits sufficiently long before building at round `n+1`
references all of them. §6.8 is that argument, formalised.

The view formulation does not, however, supply two further ingredients.

**A build rule.** View convergence is a claim about the network. Coverage requires
in addition a claim about *when validators build*. A network propagating
perfectly still commits nothing if validators build upon the arrival of the
`2f+1`st block, since they would then reference the fastest quorum and no more.
The assumption therefore pairs a delivery bound with a protocol obligation, which
is why `waits` and `prompt` are fields of `Timing`, and why the delivery route
factors into `EventuallyDelivers` and `includes`.

**A build-time index.** A block's references are fixed at its construction, so
what bears on the argument is not what a validator holds eventually but what it
held at the moment it built. `View` records no time, so a view-convergence
statement cannot be applied directly. `Delivery.held v n` supplies the index, and
with it the delivery route is a single line. This is a point about the
formulation rather than about the mechanism, but it is the reason the assumption
is stated on `refs`.

A third point is easily overlooked: the timeout must exceed `delay + D`, not
`delay`. Validators enter a round at different times, so the wait must
accommodate both the propagation bound and the spread. This is the origin of the
factor of two in §6.10.

The claim advanced here is that the view formulation is *incomplete*, not that it
is incorrect, and the contribution is the identification of the two missing
ingredients.

### 7.2 Executability

`SynchronisedOn` is not a rule a validator can follow. `Correct` is a
model-level object, so the instruction to reference every correct block of the
round below names two quantities a validator cannot determine: which of the
blocks it holds are correct-authored, and whether all of them have arrived, a
missing block being indistinguishable from one never published.

What a validator can do is wait a fixed period, build upon whatever has arrived,
and increase the period when progress fails. These are `waits`, `prompt` and the
backoff, all of which are executable.

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
3. The interface admits two independent discharges (§6.7, §6.8) and a third,
   quantitative route (§6.10), against an unchanged statement.
4. The assumption composes with the safety development, mentioning only `U.ids`,
   `U.block` and `refs` — the vocabulary that development already employs.

### 7.4 Costs

Δ does not appear above the interface. Introducing it would require views indexed
by an instant and every statement quantified over instants, for no proof content.
The quantitative statements recover what is needed *below* the interface without
propagating time upward.

The gain is not logical. One assumption becomes two, and nothing becomes
unconditional: in the absence of a time model the chain must terminate at a
delivery assumption.

### 7.5 Related work

> *[Editorial: position against (i) liveness arguments for DAG-BFT protocols as
> conventionally presented — DAG-Rider, Narwhal/Bullshark, Mysticeti,
> Shoal/Sailfish — identifying where the synchrony assumption is located in each;
> (ii) partial synchrony in the sense of Dwork, Lynch and Stockmeyer, and the
> standard GST/Δ formulation; (iii) mechanised consensus, and the level of
> abstraction at which existing formalisations operate. The specific question to
> settle is whether the synchrony assumption has previously been stated
> structurally on the DAG rather than on message delivery.]*

---

## 8. Satisfiability

Every structure carrying assumptions is exhibited satisfiable by a concrete model
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
the combined fault budget of §4.4 appearing as a concrete obstruction rather than
as an inequality.

---

## 9. Limitations

The quantitative bounds are established (§6.10). The following remain open.

**The backoff loop.** `Rated`, and the threshold condition generally, are assumed
rather than derived from the feedback mechanism of §7.2. Moreover
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
