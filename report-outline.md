# lean-dag — Report outline

A machine-checked development of block-DAG consensus (Mysticeti-style) in
Lean 4 + Mathlib. This outline fixes the report's structure, its definitions,
its assumptions, and the statements it presents. Everything quoted below is the
**actual Lean**, copied from the source.

**Scope discipline.** The report presents the *final* definitions, assumptions
and theorems. Proofs stay in the repository; the report says what is proved and
what it rests on. Where a definition's shape is load-bearing — the positive
form of "nearest anchor", the universe-level indirect test, the horizon — the
report says why *that definition is the right one*, not how it was arrived at.
Nothing about the development history belongs here.

> **Status.** Draft outline. Sections marked **[EXPAND]** are stubs for George
> to fill.

---

## 0. Front matter

- **Title.** Lead with the contribution, which is the *assumption*, not the
  mechanisation.
  - *Eventual DAG Synchrony: a machine-checked liveness argument for DAG-based
    consensus*
  - *Liveness without messages: DAG-level synchrony, formalised*
- **Abstract.** [EXPAND] In order: (i) DAG BFT is widely deployed but its
  liveness arguments are stated per-message; (ii) we propose *eventual DAG
  synchrony*, a structural assumption on the DAG itself; (iii) we mechanise
  safety and liveness for a Mysticeti-style commit rule above it; (iv) we
  discharge the DAG-level assumption from GST + Δ + a build rule, so it is a
  convenience rather than a strengthening; (v) we give the quantitative form —
  a correct leader commits once validators wait `2Δ`.

---

## 1. Introduction

### 1.1 The setting

- DAG-based BFT: validators broadcast round-indexed blocks referencing a quorum
  of the round below; consensus is a deterministic *read* of the DAG rather
  than a separate voting protocol.
- Uncertified variant (Mysticeti): no explicit certificate round — the
  certificate is *found* in the DAG two rounds up. This is what makes the
  commit rule combinatorial, and it is what lets the whole development proceed
  with no cryptographic layer.

### 1.2 Per-message synchrony, and why it is awkward

> Traditional proofs of liveness assume some synchrony on a message per message
> basis. Something like after GST messages between honest parties arrive within
> a bound Δ. This is awkward as it requires us to think of the mechanics of how
> the DAG is transmitted in terms of messages.

- A message-level assumption forces the *whole* proof to carry a time model:
  every statement quantified over instants, every lemma re-deriving that enough
  arrived.
- The commit rule never mentions time. It counts references. The mismatch is
  real work with no proof content.

### 1.3 Contributions

1. **Eventual DAG synchrony** (`SynchronisedOn`), stated structurally: after
   round `R`, every correct block references every correct block of the round
   below. No clock, no messages, no Δ.
2. A **machine-checked safety development** — agreement, uniqueness, no
   retraction — assuming *nothing* about the network, not even eventual
   delivery.
3. A **machine-checked liveness development** above the DAG-level assumption,
   in which no theorem mentions time.
4. **The assumption is discharged, two ways** — from a delivery model (§6.7)
   and from GST + Δ + a build rule (§6.8). It is not a new axiom.
5. **What the view formulation needs beside it** (§7.1): a delivery guarantee
   alone does not give coverage without a rule about *when* to build; and
   because references are fixed at construction, the guarantee must be indexed
   to the build moment (`Delivery.held`).
6. **The quantitative form** (§6.10): coverage from an explicit round, a bounded
   committing slot, and — the operational statement — **a correct leader
   commits once every validator waits `2Δ`**.

### 1.4 What is not claimed

- No wall-clock latency. `Delay(Δ)` is a duration; total time to commit is not,
  since converting a round count to elapsed time is not done (§9).
- The block-level total order needs a tie-break within a flush that the
  development declines to assume; only the *committed-leader sequence* and the
  *ledger set* are agreed (§5.6).
- No cryptography, no equivocation *detection*, no reconfiguration.

---

## 2. System model

### 2.1 Validators and faults

```lean
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  f : ℕ
  byzantine : Finset Validator
  card_validators : Fintype.card Validator = 3 * f + 1
  card_byzantine : byzantine.card ≤ f

def Correct : Finset Validator := (F.byzantine)ᶜ
```

Quorum = `2f+1`. Derived: `card_correct : 2 * F.f + 1 ≤ Correct.card`.

**`Correct` carries no behaviour.** It is a set complement — a purely negative
condition, satisfied by a validator that crashes at round 0. That is what makes
every safety result hold for crashed validators too, and it is why liveness
must add positive rules (§6.0). It is also why non-equivocation has to be
asserted (§2.4): nothing else in the model says what a correct validator does.

### 2.2 Blocks

```lean
structure Block (Validator BlockId Payload : Type*) where
  round : ℕ
  creator : Validator
  refs : Finset BlockId
  payload : Payload
```

Blocks are **id-addressed**: `refs : Finset BlockId`, not `Finset Block`. That
is what lets a view and the universe share one `U.block`, so two validators can
disagree about *which* blocks they hold and never about *what an id denotes*.
`Payload` is opaque and inert throughout.

### 2.3 Validity

```lean
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  quorum : 0 < b.round → 2 * F.f + 1 ≤ (creators blk b).card
```

- `predecessor` is stated **additively**, which avoids ℕ-subtraction and makes
  genesis *derivable* rather than a second case: at round 0 the equation is
  unsatisfiable, so `refs = ∅` follows.
- `distinct_creators` is load-bearing in exactly one place, M5′ (§5.4).
- `quorum` is stated on the **creator set**, not `refs.card` — the faithful
  reading of "2f+1 blocks from the previous round" is 2f+1 *validators*.

### 2.4 The block universe and views

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

**Non-equivocation is stated at the universe level, and must be.** Per-view
would be strictly weaker: `V₁` could hold `b₁` by correct validator `v` at
round `r` and `V₂` a different `b₂` by the same `v` at the same round, with
both views satisfying "at most one block per correct author per round"
internally. That is `v` equivocating with both views well-formed. Every
cross-view result (M6) needs the two blocks identified as *one id*, which only
a universe-level statement delivers. Views then inherit it for free, which is
why `View` carries no such field.

**It is also independent of the other fields** — duplicating a correct-authored
block under a fresh id preserves `complete` and `valid` and breaks only
`no_equivocation` — and it is the *only* place correct-validator behaviour is
encoded on the safety side. [EXPAND — this is the modelling trade worth a
paragraph: the development models a DAG snapshot plus invariants, not an
execution, so what an operational model would prove as a reachability
invariant is discharged here by assumption.]

```lean
structure View (Validator BlockId Payload : Type*) … (U : BlockUniverse …) where
  ids : Finset BlockId
  subset_ids : ids ⊆ U.ids
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids
```

**`ids` is a `Finset`.** Every universe is finite. That is what makes
`authorsAt` have a cardinality at all — every quorum argument counts one — and
it is what forces the horizon in §6.3.

### 2.5 Causal history

```lean
def RefStep (U) (i j : BlockId) : Prop := j ∈ (U.block i).refs
def Reaches (U) : BlockId → BlockId → Prop := Relation.ReflTransGen (RefStep U)
```

### 2.6 Counting vocabulary

| | |
|---|---|
| `blocksAt U n` | ids in `U` at round `n` |
| `authorsAt U n` | their creators |
| `creatorsOf U.block s` | creators of an arbitrary id-set |
| `supporters U b n` | round-`n` authors referencing `b` |
| `blames U L n` | round-`n` authors *not* referencing `L` |

`creatorsOf` is defined on an arbitrary `Finset BlockId`, not on a block's
refs: T3's hypothesis, the commit rule and T0′ all quantify over id-sets that
are nobody's references. Such sets carry no distinctness invariant, which is
why every quorum hypothesis is on the creator set — a Byzantine author could
otherwise pad one with equivocating blocks.

---

## 3. The commit rule

### 3.1 Certificates

```lean
def votesIn (U) (C L : BlockId) : Finset BlockId :=
  (U.block C).refs.filter (fun q => L ∈ (U.block q).refs)

def Certifies (U) (C L : BlockId) : Prop :=
  2 * F.f + 1 ≤ (creatorsOf U.block (votesIn U C L)).card

def certificates (U) (L : BlockId) (r : ℕ) : Finset BlockId :=
  (blocksAt U (r + 2)).filter (fun C => Certifies U C L)
```

There is no certificate *message*. A round-`(r+2)` block **is** a certificate
for `L` when its own references contain a quorum of `L`'s voters.

> **[FIGURE 1]** Three rounds: `L` at `r`; voters at `r+1` referencing `L`; a
> certificate at `r+2` whose refs contain a quorum of those voters.

### 3.2 The direct rules

```lean
def DirectCommit (U) (L : BlockId) (r : ℕ) : Prop :=
  2 * F.f + 1 ≤ (creatorsOf U.block (certificates U L r)).card

def DirectSkip (U) (L : BlockId) (r : ℕ) : Prop :=
  2 * F.f + 1 ≤ (blames U L (r + 1)).card
```

### 3.3 The indirect rule

```lean
def CertifiedIn (U) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ C ∈ certificates U L r, Reaches U A C
```

**`CertifiedIn` is universe-level, and must be.** T6a (§5.1) shows the
view-restricted computation agrees, so nothing is lost — and it is what makes
L2 (§6.5) true. A view-relative indirect test would make `indirectSkip`'s
premise *anti*-monotone, so growing a view could reveal a certificate and flip
a skip into a commit.

### 3.4 The slot schedule

```lean
class Slots (Validator : Type*) where
  slotRound : ℕ → ℕ
  leader : ℕ → Validator
  spacing : ∀ k, slotRound k + 3 ≤ slotRound (k + 1)

def IsLeaderBlock (U) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k
```

**Spacing ≥ 3 is a safety parameter, not a throughput one.** It is exactly what
puts every later anchor at round `≥ r+3`, which is M4's commit requirement
(§5.3). Say this plainly — the constant looks arbitrary and is not.

`IsLeaderBlock` is a predicate over *candidates*, not a selection: a Byzantine
leader may have several, a correct one at most one by T1. That choice is what
makes L5 (§6.6) close vacuously when the leader published nothing.

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

Three properties of the definition to state:

1. **A relation, not a function.** A `decide` function recurses upward in slot
   index with no a-priori bound, needing fuel or partiality for nothing — none
   of this needs to compute.
2. **"Nearest anchor" is stated positively.** The direct reading — *no slot
   strictly between is committed* — is a negative premise an inductive
   definition cannot carry. Stated as *every slot strictly between is decided
   `none`* it is equivalent (the sweep decides every slot it passes) and keeps
   every recursive occurrence positive. This is what supplies the
   sub-derivation M6's hardest case consumes (§5.5).
3. **View-relative direct rules, universe-level indirect test** (§3.3).

---

## 4. Assumptions

The report should carry these as **one table each**, with what consumes them.

### 4.1 Safety

| # | Assumption | Kind | Where |
|---|---|---|---|
| A1 | `3f+1` validators | fault model | `Faults.card_validators` |
| A2 | `≤ f` Byzantine | fault model | `Faults.card_byzantine` |
| A3 | refs sit one round below | well-formedness | `ValidWrt.predecessor` |
| A4 | a block never cites one author twice | well-formedness | `ValidWrt.distinct_creators` |
| A5 | non-genesis blocks cite `2f+1` distinct authors | well-formedness | `ValidWrt.quorum` |
| A6 | referenced blocks exist | well-formedness | `BlockUniverse.complete` |
| A7 | correct validators do not equivocate | fault model | `BlockUniverse.no_equivocation` |
| A8 | slots are ≥ 3 rounds apart | protocol parameter | `Slots.spacing` |

**There is no network assumption.** Safety — agreement, uniqueness, no
retraction — holds under arbitrary asynchrony, arbitrary loss and arbitrary
view divergence. State this as a result, not as an aside.

### 4.2 Liveness

| # | Assumption | Kind | Where |
|---|---|---|---|
| B1 | correct validators have genesis blocks | protocol | `Live.genesis` |
| B2 | holding a quorum ⟹ build (below horizon `N`) | protocol | `Live.builds` |
| B3 | a quorum that exists is eventually held | network (async) | `DeliversQuorum` |
| B4 | a correct block references everything its author held | protocol | `Delivery.includes` |
| B5 | **eventual DAG synchrony** from round `R` | *the seam* | `SynchronisedOn` |
| B6 | the schedule names a `T`-leader arbitrarily far out | schedule | `FairScheduleOn` |
| B7 | `T ⊆ Correct` and `2f+1 ≤ T.card` | fault budget | L4, L6 hypotheses |

B5 is discharged, two ways:

| | Discharging assumptions | Kind | Result |
|---|---|---|---|
| Route A | `EventuallyDelivers` (+ B4) | network | `synchronised_of_delivery` |
| Route B | `Timing.covers` (GST + Δ) | network | `synchronisedOn_of_timing` |
| | `Timing.waits`, `Timing.prompt` | protocol | |

### 4.3 Quantitative assumptions

Used only in §6.10. Each is optional: every result in §5 and §6.1–§6.9 stands
without them.

| # | Assumption | Buys |
|---|---|---|
| R1 | `Rated timeout` — `∀ n, n ≤ timeout n` | an explicit `R` |
| R2 | `FairWithin T w` — a `T`-leader within every `w` slots | a bounded committing slot |
| R3 | `BoundedSpacing s` — slots at most `s` rounds apart | that slot's round |
| R4 | round-`0` spread `≤ D₀`, and `∀ n, D₀ + Δ ≤ timeout n` | the wait bound `Delay(Δ)` |

### 4.4 The combined fault budget

B7 deserves its own paragraph. L4 counts to `2f+1` and never higher, so it
needs a *quorum of reliable* validators, not every correct one. Writing it as
`T ⊆ Correct` with `2f+1 ≤ T.card` yields the real budget:

> `actual_byzantine + slow_correct ≤ f`

A correct validator that is persistently slow consumes fault budget exactly
like a Byzantine one. At `f = 1` there are four validators and
`|Correct| = 3 = 2f+1` **exactly**, so there is no slack at all — every correct
validator must be in the fast set. Slack appears only when fewer than `f` are
actually faulty, and the `T`-parameterised statements deliver it automatically.
The `T := Correct` corollaries recover the textbook forms.

---

## 5. Safety

Each theorem gets: the Lean statement, one sentence on what it says, one on why
it is stated that way, and — where it is the point — one on the proof.

### 5.1 Foundations

**T0 — quorum intersection.**
```lean
theorem exists_correct_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : 2 * F.f + 1 ≤ Q₁.card) (h₂ : 2 * F.f + 1 ≤ Q₂.card) :
    ∃ v ∈ Q₁ ∩ Q₂, v ∈ (Correct : Finset Validator)
```

**T0′** (`exists_correct_mem_creators_inter`) — the same at block level: two
id-sets whose *creator sets* are quorums share a correct author.

**T1 — non-equivocation, in usable form.**
```lean
theorem BlockUniverse.eq_of_creator_eq {v : Validator} {i j : BlockId}
    (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∈ Correct)
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) : i = j
```
Phrased around the author `v`, because that is how every use site arrives: a
quorum intersection yields a correct validator, and T1 turns two blocks known
to be authored by it into a single concrete id.

**T0 + T1 composed** (`BlockUniverse.exists_common_mem_of_quorums`) — two
quorum-backed sets of round-`n` blocks share a *block*. The recurring "peel off
one certification layer" step.

**T2** (`round_le_of_reaches`) — causal history runs downward in rounds.

**T6a — causal history never escapes a view.**
```lean
theorem View.mem_of_reaches (hc : c ∈ V.ids) (h : Reaches U c b) : b ∈ V.ids
theorem View.exists_reaches_iff (hc : c ∈ V.ids) :
    (∃ b, b ∈ V.ids ∧ P b ∧ Reaches U c b) ↔ (∃ b, P b ∧ Reaches U c b)
```
This is what makes a view-relative certificate check well defined: two
validators with different views but the same anchor cannot disagree.

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

Once a quorum backs a block it can never be forgotten. Two points:

- **The bound `r+2` is tight.** [EXPAND — reproduce the four-validator
  counterexample at `r+1`; it is short and makes the mechanism visible.]
  Quorum intersection needs *two* ref-quorums to compare, and `r+2` is the
  first round that has them.
- **Quorum intersection is used exactly once**, in the base case; height above
  it is carried by transitivity alone.

**T3c — a common correct ancestor.**
```lean
theorem exists_common_correct_ancestor {r : ℕ} {c₀ : BlockId}
    (hc₀ : c₀ ∈ U.ids) (hc₀r : (U.block c₀).round = r + 2) :
    ∃ bw ∈ U.ids, (U.block bw).round = r ∧
      (U.block bw).creator ∈ Correct ∧
      ∀ c ∈ U.ids, (U.block c).round = r + 2 → Reaches U c bw
```
The only premise is that a round-`(r+2)` block *exists* — a fact about the DAG
in hand, not an assumption that anyone makes progress. Proved by double
counting. [EXPAND — the arithmetic obligation reduces to `c² ≤ f(l+c)`, which
`l ≤ c` turns into `c ≤ 2f`, impossible since `b ≤ f` forces `c ≥ 2f+1`.]

### 5.3 The direct rules are consistent

- **M3** `certificates_eq_empty_of_directSkip` — a skipped block has **no
  certificate anywhere in the universe**, not merely none in some view. With
  `2f+1` blamers and correct validators unable to sit on both sides,
  supporters number at most `2f`.
- **M1** `not_directCommit_of_directSkip` — immediate from M3.
- **M2** `exists_certificate_reaches_of_directCommit` — a committed block's
  certificate is unavoidable from round `r+3` on. **Tight**: a round-`(r+2)`
  block that is not itself a certificate reaches none. This is why A8 is `+3`.
- **M4** `indirect_agrees_with_direct` — where the direct rule decides, the
  indirect rule agrees. **Note the asymmetry**: commit needs the anchor at
  `r+3`, since the certificate must be *reachable*; skip needs nothing, since
  M3 rules the certificate out universe-wide.

### 5.4 Uniqueness

**M5′ — certificate uniqueness.**
```lean
theorem eq_of_certificates_nonempty {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : (certificates U L₁ r).Nonempty) (h₂ : (certificates U L₂ r).Nonempty)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂
```
Stronger than M5, and the form the indirect rule needs — it commits on a
*single* certificate in reach, not a quorum. The proof needs no relationship
between the two certificates: each names `2f+1` distinct voters, the voter sets
intersect in a correct `w` (T0′), `w`'s single round-`(r+1)` block votes for
both (T1), and **distinctness** forbids one block referencing two round-`r`
blocks by one author. *This is the one place A4 is load-bearing.*

**M5** `eq_of_directCommit_of_creator_eq` — a corollary.

### 5.5 Agreement

**M6.**
```lean
theorem decided_agree {V₁ V₂ : View …} {k : ℕ} {v₁ v₂ : Option BlockId}
    (h₁ : Decided U V₁ k v₁) (h₂ : Decided U V₂ k v₂) : v₁ = v₂
```
No two validators reach conflicting decisions for a slot, whatever views they
hold and whichever routes they took. This is *no-conflicting-decision*: a
validator that has not yet decided is not in disagreement.

Structural induction on the first derivation. Of sixteen constructor pairings,
fifteen close outright. The one substantial case is *indirect commit against
indirect skip*, settled by trichotomy on the two anchors — and it is where
§3.5's positive "nearest anchor" formulation is consumed, since the negative
reading carries no sub-derivation for the induction to use.

> **[FIGURE 2]** The hard case: two validators, two anchors, trichotomy on `j`
> versus `j₂`.

Corollaries: `eq_of_decided_commit`, `not_decided_skip_of_decided_commit`.

### 5.6 The ledger

```lean
def commitSeq (g : ℕ → Option BlockId) (n : ℕ) : List BlockId :=
  (List.range n).filterMap g

theorem commitSeq_agree
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    commitSeq g₁ n = commitSeq g₂ n
```

```lean
def ledgerSet (U) (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ Reaches U L b}

theorem ledgerSet_mono  (h : n ≤ m) : ledgerSet U g n ⊆ ledgerSet U g m
theorem ledgerSet_agree …             : ledgerSet U g₁ n = ledgerSet U g₂ n
```

```lean
def OutputAt (U) (g : ℕ → Option BlockId) (b : BlockId) (k : ℕ) : Prop :=
  (∃ L, g k = some L ∧ Reaches U L b) ∧
    ∀ j, j < k → ∀ L, g j = some L → ¬ Reaches U L b

theorem outputAt_unique (h₁ : OutputAt U g b k₁) (h₂ : OutputAt U g b k₂) : k₁ = k₂
theorem outputAt_agree  … (hk : k < n) (ho : OutputAt U g₁ b k) : OutputAt U g₂ b k
```

**No retraction, stated without any order on ids.** A block, once written,
stays written, in the same place. Ordering *within* one flush needs a tie-break
the development does not assume — but **whether** and **when** a block is
output needs no order, and that is what retraction would violate. State this as
a deliberate boundary.

---

## 6. Liveness

### 6.0 Why `Correct` is not enough

`Correct` is negative (§2.1), so every liveness statement is vacuous without
positive rules. Three primitives are added, and their *kinds* differ:

- **(a) Correct validators produce blocks** — protocol.
- **(b) Correct blocks cover the correct blocks below them** — an **outcome**
  the protocol produces but cannot name (§7.2).
- **(c) Correct leaders recur** — schedule.

(a) and (b) pull against each other, and the timing layer brackets them
exactly: (a) is a **floor** — a validator must eventually build
(`Timing.prompt`, the upper bound on build time); (b) is a **delay** — it must
not build too early (`Timing.waits`, the lower bound).

### 6.1 L0 — the DAG is dense below its frontier

```lean
theorem card_authorsAt_of_lt {r n : ℕ} (hn : n < r) {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    2 * F.f + 1 ≤ (authorsAt U n).card
```
**No assumptions whatever** — validity alone. The content is not that the DAG
grows but that it **cannot grow tall and thin**: one block high up forces a
quorum of authors at every round beneath it.

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

- **`held`'s index is the point**: `held v n` is what `v` had in hand *at the
  moment it built its round-`(n+1)` block*, not what `v` ever receives. That is
  the build-time index a view cannot supply (§7.1).
- **It contains no clock.** With no time model, "waited longer" can only show
  up as a larger `held` — which is why `Timing` (§6.8) slots in underneath with
  nothing above changing.
- `DeliversQuorum` is **conditional** (existence first, holding second):
  unconditionally it would assert the very block production L1 proves.
- It carries **no round bound**, so it holds before GST too.

### 6.3 L1 — no stall, and the horizon

```lean
def PopulatedOn (U) (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r

structure Live (U) (D : Delivery U) (N : ℕ) : Prop where
  genesis : Populated U 0
  builds : ∀ r < N, ∀ v ∈ Correct,
    2 * F.f + 1 ≤ (creatorsOf U.block (D.held v r)).card →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r + 1

theorem no_stall {D : Delivery U} (H : Live U D N) (hd : DeliversQuorum D) :
    ∀ r ≤ N, Populated U r
```

**The horizon `N` is necessary, not cosmetic.** `U.ids` is a `Finset`; without
the bound `r < N` these fields force infinitely many distinct blocks into a
finite set, so **no universe satisfies them** and every theorem assuming them
is vacuous.

Three consequences:

1. **`N` is a demand, not a bound.** `Live U D N` requires blocks all the way
   to `N`, so a larger `N` is a **stronger** hypothesis satisfied by **fewer**
   universes. Coverage of every DAG comes from quantifying over `N`, never from
   choosing it large.
2. **Two independent axes.** `N` is *extent*, `R` is *quality*. All four
   combinations are real. [EXPAND — reproduce the 2×2 table.]
3. **Unboundedness is a property of the family.** "The ledger grows without
   bound" is not "one DAG commits infinitely often" — no `Finset` can — but
   "no slot is the last one a DAG can be grown far enough to commit".

L1 is the only result where the horizon does work; L4 never mentions `N`.

### 6.4 Eventual DAG synchrony — the seam

```lean
def SynchronisedOn (U) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ T →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ T → a ∈ (U.block b).refs
```

**The paper's central definition.** §7 is its argument. Structurally:

- **Honest-to-honest on both sides.** Nothing may be assumed about Byzantine
  blocks existing — a Byzantine validator may publish nothing, or publish and
  reveal selectively — and nothing needs to be, since L4 counts only correct
  certificates and there are `2f+1` correct validators. Assuming *all* blocks
  are referenced would be assuming Byzantine validators behave.
- **Well-formedness survives the restriction**: a correct block referencing
  every correct block below already names `≥ 2f+1` distinct creators, so A5 is
  met with no Byzantine reference.
- **Antitone in `T`** (`SynchronisedOn.mono`), which is what lets results
  proved at `Correct` feed the quorum-relative L4.

### 6.5 L2, L3 — decisions are monotone, and propagate

```lean
theorem decided_mono (hsub : V.ids ⊆ V'.ids) (h : Decided U V k v) : Decided U V' k v
def View.full (U) : View Validator BlockId Payload U   -- ids := U.ids
theorem decided_full (h : Decided U V k v) : Decided U (View.full U) k v
```

- L2 says a validator **never revises** a decision as its view grows. Safety
  says decisions do not *conflict*; this says they do not *change*. Distinguish
  them explicitly.
- L2 holds only because `CertifiedIn` is universe-level (§3.3).
- L3 is the informal claim *after GST, if one correct validator commits all
  will commit*, with the time content removed. `View.full` is every correct
  validator's eventual view, so this **is** "all correct validators eventually
  reach the same decision". It also fixes what `U` means: every block some
  correct validator ever held. A Byzantine block revealed to nobody is not in
  the universe.

### 6.6 L4, L5, L6 — commits happen, and recur

**L4 — a correct leader commits.** The one substantive proof.
```lean
theorem directCommit_of_leader_mem (hcard : 2 * F.f + 1 ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```
with `decided_of_leader_mem` the decision form.

**Two layers of coverage and nothing else.** Every correct round-`(r+1)` block
references `L` by coverage; every correct round-`(r+2)` block references all of
*those*, so its votes for `L` come from a quorum and it certifies; there are
`2f+1` correct validators, so the certificates themselves form a quorum.

**No horizon, no growth, no limit universe** — the hypotheses are three local
`PopulatedOn` facts.

**L5 — an absent leader is skipped.**
```lean
theorem decided_none_of_leader_absent {V : View …}
    (h : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k) :
    Decided U V k none
```
`Decided.directSkip`'s premise is `∀ L, IsLeaderBlock U k L → …`, which holds
**vacuously** when the leader published nothing. §3.4's quantify-over-candidates
choice is what buys this.

**L6 — commits recur.**
```lean
def FairScheduleOn (T : Finset Validator) : Prop := ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T

theorem commits_recur_on (hT : T ⊆ Correct) (hcard : 2 * F.f + 1 ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      ∀ U D N, Live U D N → DeliversQuorum D → SynchronisedOn U T R →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L)
```

**The quantifier order is the content.** The alternative reading — *given
`Live U D N`, for every `k` a committing `k' ≥ k` with `slotRound k' + 2 ≤ N`*
— is **false**: fairness promises a correct leader somewhere beyond `k`, and
that slot may lie past the horizon. As stated, `k'` depends only on the
**schedule**, and the DAG is grown to it afterwards.

### 6.7 L7a — the seam discharged from delivery

```lean
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ Correct, ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ Correct → a ∈ D.held v n

theorem synchronised_of_delivery (D : Delivery U) (h : EventuallyDelivers D R) :
    Synchronised U R
```

`refs ⊇ held ⊇` every correct block below. **The gain is not logical** — one
assumption becomes two and nothing turns unconditional. The gain is that each
piece is a *single kind of thing*: `includes` is implementable and observable;
`EventuallyDelivers` is pure network.

**`EventuallyDelivers` is view convergence *indexed to the build moment*** — it
does not say correct blocks reach `v` eventually, but that they are in
`D.held v n`. That indexing is doing the work, and it is exactly what a
view-shaped statement lacks (§7.1).

### 6.8 L7b — the seam discharged from GST

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

- `covers` **is** GST + Δ, and it is the only network field.
- `waits` (floor) and `prompt` (ceiling) are the two protocol build rules.
- `latest` is *attained* (`latest_mem`), not merely an upper bound, or it would
  carry no information.
- The horizon is required for the same reason as in `Live` (§6.3).

**Drift is derived, not assumed.**
```lean
def Timing.DriftFrom (n₀ D : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, n₀ ≤ n → n ≤ N → tm.built w n ≤ tm.built v n + D

theorem Timing.driftFrom_of_prompt {n₀ : ℕ}
    (hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D)
    (hto : ∀ n, n₀ ≤ n → tm.delay ≤ tm.timeout n) :
    tm.DriftFrom n₀ D
```
A two-case split on `prompt`'s `max`: **timeout-limited** (everyone advances by
the same `timeout n`, spread unchanged) or **delivery-limited** (finished by
`latest n + delay`, and `latest` is attained). **Drift is *preserved*, not
compressed** — every clock advances by the same timeout — and preservation is
what the argument needs.

**The seam, discharged.**
```lean
theorem Timing.synchronisedOn_of_timing (hT : T ⊆ Correct)
    (hD : tm.DriftFrom R D) (hgst : tm.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + tm.delay ≤ tm.timeout n) :
    SynchronisedOn U T R
```
Four inequalities chained — drift, backoff, waiting — give
`built w n + delay ≤ built v (n+1)`, exactly `covers`'s hypothesis.
Non-equivocation does the rest: `SynchronisedOn` quantifies over *every*
`T`-authored block and T1 identifies each with the `blk` the structure names.
*That is why `T ⊆ Correct` is needed here* — a Byzantine author could have
several blocks in a round, and `blk` names one.

**Note the hypothesis is a *threshold*, not a growth condition:** the timeout
must stay above `D + delay` from `R` on. A constant timeout satisfies it; so
does any scheme that stabilises above the bound.
`exists_synchronisedOn_of_backoff` packages one sufficient condition
(`Monotone` + unbounded) but is not the only route — §6.10 gives two others.

### 6.9 The liveness stack

> **[FIGURE 3]** The layer diagram — the load-bearing picture of the paper.
>
> ```
>   L6  commits recur          ─┐
>   L4  a correct leader commits │  no time anywhere in this region
>   L1  no stall                 │
>   L0  density                 ─┘
>        ▲
>        │  SynchronisedOn  ←── THE SEAM
>        │
>   L7a  EventuallyDelivers (delivery model)
>   L7b  Timing: GST + Δ + waits + prompt
> ```

**Nothing above the seam mentions time, and nothing below it mentions
certificates.**

### 6.10 Quantitative liveness

`LeanDag/Quantitative.lean`. Presented last because it sits **beside** the
stack: nothing imports it, every theorem strengthens one below, and each
strengthening is bought with a strengthened hypothesis (§4.3). A reader who
declines them keeps §6.1–§6.9 intact.

**Why the weak forms give no bound.** Two results conclude with a bare
existential (`∃ R, SynchronisedOn U T R`; `∃ k', k ≤ k' ∧ …`). That is forced:
each hypothesis is *itself* a bare existential, and under them **no bound
exists**.

- `hub : ∀ m, ∃ n, m ≤ tm.timeout n` admits `timeout n = ⌊log₂ (n+1)⌋` —
  monotone, unbounded, and needing `n ≥ 2^(D + delay) − 1`. Slower schedules
  push `R` out without limit.
- `FairScheduleOn T` admits a schedule naming `T`-leaders at slots
  `0, 10, 1000, …`.

So a bound requires a **rated** hypothesis, not a better proof.

**Part 1 — `R` becomes explicit.**
```lean
theorem synchronisedOn_of_rate (tm : Timing U T N) (hT : T ⊆ Correct)
    (hrate : Rated tm.timeout) {n₀ : ℕ} (hn₀ : tm.delay ≤ n₀)
    (hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D) :
    SynchronisedOn U T (max (max (D + tm.delay) n₀) tm.gst)
```
Each summand is what it looks like: the threshold, the drift base, GST. **A
hypothesis is dropped as well as added** — `backoff_ge_of_rate` needs no
monotonicity, since the bound at `n` comes from `n` itself and cannot lapse;
and `Rated` implies `hub` (`unbounded_of_rated`).

**Part 2 — the committing slot, then its round.**
```lean
theorem commits_recur_within … (fair : FairWithin T w) (R k : ℕ) :
    ∃ k', max k R ≤ k' ∧ k' < max k R + w ∧ R ≤ S.slotRound k' ∧ …

theorem commits_recur_by_round … (hs : BoundedSpacing s) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ S.slotRound k' ≤ S.slotRound (max k R) + s * w ∧ …
      S.slotRound (max k R) + s * w + 2 ≤ N → …
```
**`BoundedSpacing` has no weak counterpart.** `Slots.spacing` bounds slot
rounds from *below* (`+3`), which is what safety needs — M4's anchor must sit
three rounds up. A latency claim wants the *opposite* bound, and the class has
none, because no safety result asks. Adding the mirror image is what converts a
slot bound into a round bound.

**Part 3 — the wait bound. This is the statement to lead with.**
```lean
theorem directCommit_of_wait (tm : Timing U T N) (hT : T ⊆ Correct)
    (hcard : 2 * F.f + 1 ≤ T.card)
    (hstart : ∀ v ∈ T, ∀ w ∈ T, tm.built w 0 ≤ tm.built v 0 + D₀)
    (hwait : ∀ n, D₀ + tm.delay ≤ tm.timeout n)
    (hgst : tm.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k)
```

> After GST, if every `T`-validator waits at least `D₀ + Δ` before building,
> every correct leader is committed — where `D₀` bounds the spread at round `0`.

So **`Delay(Δ) = D₀ + Δ`**, and `2Δ` in the headline case
(`directCommit_of_wait_two_delay`), with `decided_of_wait` the decision form.

**The timeout is a constant** — no backoff, no `Rated`, no `Monotone`, no
existential `R`. That says what the backoff is *for*: it exists only because Δ
is unknown. Given Δ, no adaptation is needed.

**Where `D₀` comes from.** Drift is preserved rather than compressed (§6.8), so
the bound is not derived from Δ — it is taken at **round `0`**, where it states
how far apart validators *started*, and `driftFrom_of_prompt` carries it
forward unchanged. Validators starting together give `D₀ = 0` and
`Delay(Δ) = Δ`; a common start broadcast gives `D₀ ≤ Δ`, since the signal
itself takes at most Δ. **The factor of two is the price of not having
synchronised clocks.**

`Timing.populatedOn` makes these statements need no `Live`, no `DeliversQuorum`
and no L1: `Timing` already asserts a block per `T`-validator per round, so the
only hypotheses about time are the start spread, the wait, and GST.

---

## 7. Eventual DAG synchrony — the argument

The section the paper exists for. It should stand alone.

### 7.1 The view formulation, and the two things it needs beside it

Stated on **views**:

> after GST, if a correct validator has a view `V₁`, then within Δ all correct
> validators' views will contain `V₁`.

This is appealing — `View` is already first-class, `V₁ ⊆ V₂` already
meaningful, every safety result already view-relative — and it gives L3
outright: the common view *is* `View.full`.

**The mechanism for coverage is the expected one and it works.** Fast
propagation puts every correct round-`n` block into every correct validator's
hands; a validator that waits long enough before building at `n+1` references
all of them. §6.8 is that argument, formalised.

What the view statement does not supply is **two further ingredients**:

**(i) A build rule.** View convergence is a claim about the network; coverage
additionally needs a claim about *when validators build*. A perfectly
propagating network still commits nothing if validators build the moment they
hold `2f+1` — they would reference the fastest quorum and no more. So the
assumption pairs a delivery bound with a protocol obligation, which is why
`waits` and `prompt` are `Timing` fields, and why the delivery route splits
into `EventuallyDelivers` (network) and `includes` (protocol).

**(ii) A build-time index on the view.** References are fixed at construction,
so what matters is not what a validator holds *eventually* but what it held *at
the moment it built*. `View` records no time, so a view-convergence statement
cannot be plugged in as it stands. `Delivery.held v n` supplies the index, and
with it L7a is a single line. This is a modelling point rather than a claim
about mechanism — but it is why the assumption is phrased on `refs`.

**A third detail: the timeout must exceed `delay + D`, not `delay`.** Validators
enter a round at different times, so the wait must cover the propagation bound
*and* the spread. That is `hbackoff` in §6.8 and the `2Δ` of §6.10.

**Calibrate the claim.** The view formulation is *incomplete*, not *wrong*, and
the contribution is the pair (i)/(ii) — not an impossibility result.

### 7.2 Coverage is an outcome, not an instruction

Independent of §7.1. A validator **cannot execute `SynchronisedOn`**: `Correct`
is `F.byzantineᶜ`, a model-level object, so "reference every correct block
below you" names two things a validator cannot determine — which held blocks
are correct-authored, and whether all of them have arrived (a missing block is
indistinguishable from one never published).

What a validator *can* do is wait a fixed period, build on whatever arrived,
and raise the period when things go badly. Those are `waits`, `prompt` and the
backoff — all executable.

**The backoff signal is the awkward part.** Before GST no period is long
enough, and nothing lets a validator detect that directly; what it observes is
that **commits have stopped**. So the loop that delivers coverage is driven by
liveness failure, the very thing being proved away. That is a feedback loop
rather than a vicious circle, but it means the argument cannot rest on
modelling the loop's dynamics.

**The development sidesteps it, and that is the right move.** What
`synchronisedOn_of_timing` consumes is a *threshold*: the timeout stays above
`D + delay` from some round on. Nothing about shape, rate, or driving signal.
§6.10 Part 3 takes this to its conclusion — with Δ known, a **constant**
timeout of `D₀ + Δ` suffices and the loop disappears entirely.

### 7.3 What the abstraction buys

1. **The consensus argument is purely combinatorial** — round indices and
   `Finset` cardinalities. Under a message-level assumption every statement
   carries instants.
2. **The timing content is confined** to one file and consumed through one
   definition.
3. **The seam admits two independent discharges** (§6.7, §6.8) against one
   unchanged interface, and a third quantitative route (§6.10) above it.
4. **It composes with safety.** `SynchronisedOn` mentions only `U.ids`,
   `U.block` and `refs` — the vocabulary the safety development already speaks.

### 7.4 What it costs

- **No Δ above the seam.** Δ would force views indexed by an instant and every
  statement quantified over instants, for no proof content. The quantitative
  statements recover what is needed *below* the seam (§6.10) without pushing
  time upward.
- **The gain is not logical.** One assumption becomes two; nothing becomes
  unconditional. With no time model the chain must bottom out at delivery.

### 7.5 Related work

[EXPAND] Positioning against:
- DAG-BFT liveness arguments as usually presented (DAG-Rider,
  Narwhal/Bullshark, Mysticeti, Shoal/Sailfish) — where the synchrony
  assumption sits in each.
- Partial synchrony (DLS) and the standard GST/Δ formulation.
- Mechanised consensus: what has been formalised, and at what level of
  abstraction.
- The specific question: *has anyone else stated the synchrony assumption
  structurally on the DAG rather than on message delivery?*

---

## 8. Non-vacuity

Every structure carrying assumptions is exhibited satisfiable by a concrete
model over four validators at `f = 1`. This is a result, not a test: an
unsatisfiable hypothesis makes every theorem above it vacuous.

| Model | Satisfies |
|---|---|
| `Ugrow N` | `Live`, `DeliversQuorum`, `Synchronised` at every horizon `N` |
| `ugrowDelivery` | `Delivery`, and `EventuallyDelivers` for L7a |
| `ugrowHonest` | `Delivery` with a **genuinely partial** view — the Byzantine validator withholds, and a quorum survives |
| `ugrowTiming` | `Timing`, lockstep, with a rated `2 ^ n` backoff |
| `ugrowSkew` | `Timing` with **nonzero drift and delay**, exercising both branches of `driftFrom_of_prompt` |
| `rrSlots` | `Slots`, round-robin, `FairWithin T (f+1)` and `BoundedSpacing 3` |

**Three tightness results**, which is what makes the constants meaningful:

- `ugrow_not_populated_succ` — the horizon is exact: `¬ Populated (Ugrow N) (N+1)`,
  so the family reaches `N` and stops.
- `ugrowSkew` sits on the `2Δ` boundary. Round-`0` spread `2`, `delay = 2`,
  `timeout = 4`: `D₀ = delay` and `2·delay = timeout`, so **every inequality in
  `directCommit_of_wait_two_delay` holds with equality**. The constant `2` is
  exact, not a safe over-estimate.
- `rrSlots_fairWithin` gives window `f + 1 = 2`, and `f + 1` is forced: the
  validators outside `T` may be consecutive in the rotation.

**One negative fact worth stating.** A model exhibiting *round spread* — correct
validators far apart in round number — while still committing is impossible at
`f = 1`, because `|Correct| = 3 = 2f+1` exactly, so every correct validator is
needed for a quorum and none can lag. It needs `f ≥ 2`. This is §4.4's combined
budget as a concrete obstruction.

---

## 9. Limitations

**The bounds Q3 and Q4 called for are proved** (§6.10). What remains open:

- **The backoff loop.** `Rated` and the threshold condition are assumed, not
  derived from the feedback mechanism of §7.2. And `Timing.timeout : ℕ → ℕ` is
  indexed by round, **common to `T`**, so a per-validator backoff — validators
  raising at different moments — cannot be stated at all.
- **Wall-clock latency.** `Delay(Δ)` is a duration, but total time to commit is
  not: converting "`3k + 8` rounds, each at least `2Δ`" into elapsed time needs
  a lemma accumulating `prompt` across rounds, which is not present.
  `le_built` relates rounds to time in one direction only (`n ≤ built v n`).
- **Byzantine leaders.** §6.10 bounds the wait for the next `T`-leader rather
  than bounding how distant an indirect anchor can be when the leader is
  Byzantine.
- **Leader predictability**, and so targeted DoS, is unmodelled: `Slots.leader`
  is an arbitrary function, and `FairWithin` constrains *when* good leaders
  appear, not whether an adversary can see them coming.
- **Block-level total order** needs a tie-break within a flush (§5.6).
- **T4/T5 (certified DAGs)** are out of scope by design.

**One sentence that must appear:** none of these affects whether the stated
theorems are *true* — only how much they *say*.

---

## 10. Artifact

- Lean 4 (v4.32.2) + Mathlib. `lake build`: 0 errors, 0 warnings, 8673 jobs.
- **Axiom audit.** Every headline result — `reaches_of_quorum_support` (T3),
  `exists_common_correct_ancestor` (T3c), `decided_agree` (M6),
  `commitSeq_agree`, `outputAt_agree`, `no_stall` (L1), `commits_recur_on`
  (L6), `exists_synchronisedOn_of_backoff` (L7b), `ugrow_commits_by_round`,
  `ugrowSkew_directCommit_of_wait` — depends on exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, no custom axiom, no
  `native_decide`. Reproduce the `#print axioms` block.

| File | Contents |
|---|---|
| `Validators.lean` | fault model, T0 |
| `Block.lean` | `Block`, `ValidWrt`, T0′ |
| `BlockDag.lean` | `BlockUniverse`, `View`, T1 |
| `CausalHistory.lean` | `Reaches`, T2, T6a |
| `Support.lean` | counting vocabulary, hitting and propagation |
| `Persistence.lean` | T3 |
| `CommonCore.lean` | T3a, T3c |
| `Mysticeti.lean` | the commit rule, M1–M6, the ledger |
| `Liveness.lean` | L0–L6, L7a |
| `Timing.lean` | L7b |
| `Quantitative.lean` | the quantitative results (§6.10); imported by nothing |
| `LeanDagTest/*` | the models of §8 |

- Design records: `spec.md` (safety), `liveness.md` (liveness). These carry the
  design rationale and the settled/open question log; the report draws its
  statements from the source, not from them.

---

## Appendix A — statement index

Label → Lean identifier → file, for safety (T/M/C) and liveness (L0–L7, and
§6.10). [EXPAND — `spec.md` §7 already carries the safety table; the liveness
half needs writing.]
