# lean-dag — Report outline

A machine-checked development of block-DAG consensus (Mysticeti-style), in
Lean 4 + Mathlib. This outline fixes the report's structure, its definitions,
its assumptions, and the statements it will present. Everything quoted below
is the **actual Lean**, copied from the source — the report should not
paraphrase a statement it has not checked.

**Scope discipline.** The report presents *definitions and theorem
statements*. Proofs stay in the repository; the report says what is proved,
what it rests on, and why the statement is the right one. Where a proof
technique is the point (M6's induction, T3's single use of quorum
intersection) it is described in a sentence, not reproduced.

> **Status.** Draft outline. Sections marked **[EXPAND]** are stubs for
> George to fill. Sections marked **[CHECK]** contain a claim I believe but
> which is not itself formalised.

---

## 0. Front matter

- **Title.** Something that leads with the contribution, not the tool. The
  contribution is the *assumption*, not the mechanisation.
  - Candidate: *Eventual DAG Synchrony: a machine-checked liveness argument
    for DAG-based consensus*
  - Candidate: *Liveness without messages: DAG-level synchrony, formalised*
- **Abstract.** [EXPAND] Must contain, in order: (i) DAG BFT is widely
  deployed but its liveness arguments are stated per-message; (ii) we propose
  *eventual DAG synchrony*, a structural assumption on the DAG itself;
  (iii) we mechanise safety and liveness for a Mysticeti-style rule on top of
  it; (iv) we discharge the DAG-level assumption from GST + Δ + backoff, so
  it is a convenience, not a strengthening; (v) the seam is validated by two
  independent lower models.
- **Contributions list.** See §1.3.

---

## 1. Introduction

### 1.1 The setting

- DAG-based BFT: validators broadcast round-indexed blocks referencing a
  quorum of the round below; consensus is then a *deterministic read* of the
  DAG rather than a separate voting protocol.
- Uncertified variant (Mysticeti): no explicit certificate round — the
  certificate is *found* in the DAG two rounds up. This is what makes the
  commit rule combinatorial and the whole development possible without a
  cryptographic layer.

### 1.2 The problem with per-message synchrony

The framing to lead with, from the original design notes:

> Traditional proofs of liveness assume some synchrony on a message per
> message basis. Something like after GST messages between honest parties
> arrive within a bound Δ. This is awkward as it requires us to think of the
> mechanics of how the DAG is transmitted in terms of messages.

- A message-level assumption forces the *whole* proof to carry a time model:
  every statement quantified over instants, every lemma re-deriving that
  enough arrived.
- But the commit rule never mentions time. It counts references. The mismatch
  is real work with no proof content.

### 1.3 Contributions

1. **Eventual DAG synchrony**, stated structurally (`SynchronisedOn`): after
   round `R`, every correct block references every correct block of the round
   below. No clock, no messages, no Δ.
2. A **fully machine-checked safety development** (agreement, no retraction)
   that assumes *nothing* about the network — not even eventual delivery.
3. A **machine-checked liveness development** on top of the DAG-level
   assumption, in which no theorem above the seam mentions time.
4. **The seam is discharged, twice.** Eventual DAG synchrony is derived from a
   delivery model (§6.7) and independently from GST + Δ + adaptive backoff
   (§6.8). It is therefore not a new axiom.
5. **A negative result about the natural view-based formulation** (§7.1): the
   assumption cannot be stated on views, because references are frozen at
   build time. This is the sharpest technical finding and should be
   foregrounded.
6. **Satisfiability witnesses** for every liveness definition, which caught
   four definitions that were vacuous as first written (§8).

### 1.4 What is not claimed

- No quantitative bound: no `R − GST` bound, no commit latency, no throughput
  rate. Δ is deliberately absent above the timing layer. [→ §9, Q3]
- The block-level total order needs a tie-break within a flush that the
  development declines to assume; only the *committed-leader sequence* and the
  *ledger set* are ordered/agreed. [→ §5.6]
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

- **Assumption A1.** Exactly `3f+1` validators.
- **Assumption A2.** At most `f` are Byzantine.
- Quorum = `2f+1`. Derived: `card_correct : 2 * F.f + 1 ≤ Correct.card`.
- **`Correct` is a purely negative condition** — *does not equivocate*. It is
  satisfied by a validator that crashes at round 0. That is deliberate: it is
  what makes every safety result hold for crashed validators too, and it is
  exactly why liveness needs positive rules added (§6.1).

### 2.2 Blocks

```lean
structure Block (Validator BlockId Payload : Type*) where
  round : ℕ
  creator : Validator
  refs : Finset BlockId
  payload : Payload
```

- Blocks are **id-addressed**; `refs : Finset BlockId`, not `Finset Block`.
  [EXPAND — why: it is what lets a view and the universe share `U.block`, so
  two validators can disagree about *which* blocks they hold and never about
  *what an id denotes*.]
- `Payload` is opaque and inert throughout.

### 2.3 Validity

```lean
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  quorum : 0 < b.round → 2 * F.f + 1 ≤ (creators blk b).card
```

- **Assumption A3 (predecessor).** Stated *additively* — `round + 1 = b.round`,
  not `round = b.round - 1`. Avoids ℕ-subtraction, and makes genesis
  *derivable*: at round 0 the equation is unsatisfiable, so `refs = ∅` follows
  rather than being a second case.
- **Assumption A4 (distinct creators).** Load-bearing in exactly one place —
  M5′ (§5.4). Worth saying so.
- **Assumption A5 (quorum).** Stated on the **creator set**, not on
  `refs.card`. This is the faithful reading of "2f+1 blocks from the previous
  round": the protocol means 2f+1 *validators*.

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

- **Assumption A6 (completeness).** Every referenced block exists.
- **Assumption A7 (non-equivocation).** **Stated at the universe level, not
  per-DAG.** Per-DAG would be too weak: two DAGs could each satisfy "at most
  one block per correct validator per round" while holding *different* such
  blocks — which is a correct validator equivocating, with both DAGs looking
  well-formed. [EXPAND — this is a modelling point worth a paragraph.]

```lean
structure View (Validator BlockId Payload : Type*) … (U : BlockUniverse …) where
  ids : Finset BlockId
  subset_ids : ids ⊆ U.ids
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids
```

- A view is a **downward-closed subset** sharing `U.block`. Validity and
  non-equivocation are inherited for free.
- **`ids` is a `Finset`.** Every universe is finite. Not incidental — it is
  what makes `authorsAt` have a cardinality at all, and every quorum argument
  counts one. It is also what forces the horizon in §6.3, and it is where four
  vacuous definitions came from (§8).

### 2.5 Causal history

```lean
def RefStep (U) (i j : BlockId) : Prop := j ∈ (U.block i).refs
def Reaches (U) : BlockId → BlockId → Prop := Relation.ReflTransGen (RefStep U)
```

### 2.6 Derived counting vocabulary

| | |
|---|---|
| `blocksAt U n` | ids in `U` at round `n` |
| `authorsAt U n` | their creators |
| `creatorsOf U.block s` | creators of an arbitrary id-set |
| `supporters U b n` | round-`n` authors referencing `b` |
| `blames U L n` | round-`n` correct authors *not* referencing `L` |

**Note for the report.** `creatorsOf` is defined on an arbitrary `Finset
BlockId`, not on a block's refs — T3's hypothesis, the commit rule and T0′ all
quantify over id-sets that are nobody's references. Sets that are not refs
carry no distinctness invariant, which is why the quorum hypotheses are always
on the creator set (a Byzantine author could otherwise pad with equivocating
blocks).

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
for `L` when its own references happen to contain a quorum of `L`'s voters.
This is the whole of the "uncertified DAG" idea and deserves a figure.

> **[FIGURE 1]** Three rounds: `L` at `r`; voters at `r+1` referencing `L`;
> a certificate at `r+2` whose refs contain a quorum of those voters.

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

- **`CertifiedIn` is universe-level, deliberately.** T6a (§5.1) shows the
  view-restricted computation agrees, so nothing is lost — and it is what
  makes L2 (§6.5) true. A view-relative indirect check would make the
  `indirectSkip` premise *anti*-monotone, and growing a view could flip a skip
  into a commit. [EXPAND — this is a good "the definition earns its shape"
  paragraph.]

### 3.4 The slot schedule

```lean
class Slots (Validator : Type*) where
  slotRound : ℕ → ℕ
  leader : ℕ → Validator
  spacing : ∀ k, slotRound k + 3 ≤ slotRound (k + 1)

def IsLeaderBlock (U) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k
```

- **Assumption A8 (spacing ≥ 3).** *A safety parameter, not a throughput one.*
  It is exactly what puts every later anchor at round `≥ r+3`, which is what
  M4's commit half needs (§5.3). Say this plainly — it is the kind of constant
  that looks arbitrary and is not.
- `IsLeaderBlock` is a predicate over *candidates*, not a selection. A
  Byzantine leader may have several; a correct one has at most one by T1. This
  choice pays for itself in L5 (§6.6), where the absent-leader case closes
  vacuously.

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

Three modelling choices to defend in the report:

1. **A relation, not a function.** A `decide` function recurses upward in slot
   index with no a-priori bound, needing fuel or partiality for nothing —
   none of this needs to compute.
2. **"Nearest anchor" is stated positively.** The naive reading — *no slot
   strictly between is committed* — is a negative premise an inductive
   definition cannot carry. Stated as *every slot strictly between is decided
   `none`*, which is equivalent (the sweep decides every slot it passes) and
   keeps every recursive occurrence positive. **This is not bookkeeping:** it
   is precisely what supplies the sub-derivation M6's hardest case needs
   (§5.5).
3. **View-relative direct rules, universe-level indirect test.** §3.3.

---

## 4. Assumption inventory

The report should carry **one table** listing every assumption, its kind, and
which results consume it. Draft:

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

**The headline of this table: there is no network assumption.** Safety —
agreement, uniqueness, no retraction — holds under arbitrary asynchrony,
arbitrary message loss, and arbitrary view divergence. This should be stated
as a result, not left for the reader to notice.

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

B5 is then **discharged**, two ways:

| | Discharging assumptions | Kind | Result |
|---|---|---|---|
| Route A | `EventuallyDelivers` (+ B4) | network | `synchronised_of_delivery` |
| Route B | `Timing.covers` (GST + Δ) | network | `synchronisedOn_of_timing` |
| | `Timing.waits`, `Timing.prompt` | protocol | |
| | backoff monotone + unbounded | protocol | `exists_synchronisedOn_of_backoff` |

### 4.3 The combined fault budget

B7 deserves its own paragraph. L4 counts to `2f+1` and never higher, so it
needs a *quorum of reliable* validators, not every correct one. Demanding all
of `Correct` makes the theorem lapse when one correct validator misses one
round — a GC pause, a restart — although the protocol still commits. Writing
it as `T ⊆ Correct` with `2f+1 ≤ T.card` yields the real budget:

> `actual_byzantine + slow_correct ≤ f`

The `T := Correct` corollaries recover the textbook statements.

---

## 5. Safety

Present in dependency order, not discovery order. Each theorem gets: the Lean
statement, one sentence on what it says, one sentence on why it is stated that
way, and (where it is the point) one sentence on the proof.

### 5.1 Foundations

**T0 — quorum intersection.**
```lean
theorem exists_correct_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : 2 * F.f + 1 ≤ Q₁.card) (h₂ : 2 * F.f + 1 ≤ Q₂.card) :
    ∃ v ∈ Q₁ ∩ Q₂, v ∈ (Correct : Finset Validator)
```

**T0′ — the same at the block level** (`exists_correct_mem_creators_inter`):
two id-sets whose *creator sets* are quorums share a correct author.

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

**T0 + T1 composed** (`exists_common_mem_of_quorums`) — two quorum-backed sets
of round-`n` blocks share a *block*. The recurring "peel off one certification
layer" step.

**T2 — causal history runs downward** (`round_le_of_reaches`).

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

Once a quorum backs a block, it can never be forgotten. Two points the report
should make:

- **The bound `r+2` is tight**, with a four-validator counterexample at
  `r+1`. [EXPAND — reproduce it; it is short and it makes the mechanism
  visible.] Quorum intersection needs *two* ref-quorums to compare, and `r+2`
  is the first round that has them.
- **Quorum intersection is used exactly once**, in the base case. Height above
  that is carried by transitivity alone.

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
  certificate anywhere in the universe**, not merely none in some view. The
  counting: with `2f+1` blamers and correct validators unable to sit on both
  sides, supporters number at most `2f`.
- **M1** `not_directCommit_of_directSkip` — immediate from M3.
- **M2** `exists_certificate_reaches_of_directCommit` — a committed block's
  certificate is unavoidable from round `r+3` on. **The bound is tight**
  (a round-`(r+2)` block that is not itself a certificate reaches none), and
  it is why A8 is `+3`.
- **M4** `indirect_agrees_with_direct` — where the direct rule decides, the
  indirect rule agrees. **Note the asymmetry**: commit needs the anchor at
  `r+3` (the certificate must be *reachable*); skip needs nothing at all
  (there is no certificate anywhere to reach).

### 5.4 Uniqueness

**M5′ — certificate uniqueness.**
```lean
theorem eq_of_certificates_nonempty {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : (certificates U L₁ r).Nonempty) (h₂ : (certificates U L₂ r).Nonempty)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) : L₁ = L₂
```
Stronger than M5 and the form the indirect rule needs — the indirect rule
commits on a *single* certificate in reach, not a quorum of them. The proof
needs no relationship between the two certificates: each names `2f+1` distinct
voters, the voter sets intersect in a correct `w` (T0′), `w`'s single
round-`(r+1)` block votes for both (T1), and **distinctness** forbids one block
referencing two round-`r` blocks by one author. *This is the one place A4 is
load-bearing.*

**M5** `eq_of_directCommit_of_creator_eq` — now a corollary.

### 5.5 Agreement

**M6.**
```lean
theorem decided_agree {V₁ V₂ : View …} {k : ℕ} {v₁ v₂ : Option BlockId}
    (h₁ : Decided U V₁ k v₁) (h₂ : Decided U V₂ k v₂) : v₁ = v₂
```
No two validators reach conflicting decisions for a slot, **whatever views
they hold and whichever routes they took**. As with T5 this is
*no-conflicting-decision*: a validator that has not yet decided is not in
disagreement.

Structural induction on the first derivation. Of sixteen constructor pairings,
fifteen close outright. The one real case is *indirect commit against indirect
skip*, settled by comparing the two anchors — and it is where the positive
"nearest anchor" formulation (§3.5) pays for itself: the negative reading
carries no sub-derivation and the induction has nothing to stand on.

> **[FIGURE 2]** The hard case: two validators, two anchors, trichotomy on
> `j` vs `j₂`.

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

**No retraction, stated without an order on ids.** Together these say: a
block, once written, stays written, in the same place. Ordering *within* one
flush needs a tie-break the development deliberately does not assume — but
**whether** and **when** a block is output needs no order at all, and that is
what retraction would violate. Be explicit that this is a deliberate stopping
point, not an omission.

---

## 6. Liveness

### 6.0 Why `Correct` is not enough

`Correct` is negative; every liveness statement is vacuous without positive
rules. Three primitives must be added, and their *kinds* differ — this
taxonomy is worth foregrounding:

- **(a) Correct validators produce blocks** — protocol.
- **(b) Correct blocks cover the correct blocks below them** — an **outcome**
  the protocol produces but cannot name (§7.2).
- **(c) Correct leaders recur** — schedule.

(a) and (b) pull against each other: (a) says build as soon as you can, (b)
says do not.

### 6.1 L0 — the DAG is dense below its frontier

```lean
theorem card_authorsAt_of_lt {r n : ℕ} (hn : n < r) {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    2 * F.f + 1 ≤ (authorsAt U n).card
```
**No assumptions whatever** — validity alone. The interesting content is not
that the DAG grows but that it **cannot grow tall and thin**: a single block
high up forces a quorum of authors at every round beneath it.

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

- `held` is what the static model lacked. **Note what it does not contain: a
  clock.** With no time model, "waited longer" can only show up as a larger
  `held` — which is exactly the trace a timeout leaves.
- `DeliversQuorum` is stated **conditionally** (existence first, holding
  second). Unconditionally it would assert the very block production L1 sets
  out to prove.
- It carries **no round bound**: this is what holds *before* GST too.

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

**The horizon `N` is not decoration, and the report should say why with the
counterexample.** `U.ids` is a `Finset`. The first draft of `Live` demanded a
block at every round — infinitely many distinct blocks in a finite set — so
**no universe satisfied it** and L1, though proved, said nothing. This was
found by trying to build a witness model, and it is checkable:

```lean
theorem not_live (U : BlockUniverse Validator BlockId Payload) : ¬ Live⁰ U
```

Three consequences to present:

1. **`N` is a demand, not a bound.** `Live U D N` requires blocks all the way
   to `N`, so a larger `N` is a **stronger** hypothesis satisfied by **fewer**
   universes. Coverage of every DAG comes from quantifying over `N`, never
   from choosing it large.
2. **Two independent axes.** `N` is *extent*; `R` is *quality*. All four
   combinations are real — reproduce the 2×2 table from `liveness.md` §4.4.
3. **Unboundedness moves to the family.** "The ledger grows without bound" is
   not "one DAG commits infinitely often" (no `Finset` can) but "no slot is
   the last one a DAG can be grown far enough to commit".

L1 is the only result where the horizon does real work; L4 never mentions `N`.

### 6.4 Eventual DAG synchrony — the seam

```lean
def SynchronisedOn (U) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ T →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ T → a ∈ (U.block b).refs
```

**This is the paper's central definition.** Everything to say about it is in
§7. Two structural notes here:

- **Honest-to-honest only**, on *both* sides. Nothing may be assumed about
  Byzantine blocks existing (a Byzantine validator may publish nothing, or
  publish and reveal selectively) and nothing needs to be (L4 counts only
  correct certificates, and there are `2f+1` correct validators). Getting this
  wrong in the *strong* direction — assuming all blocks are referenced — would
  be assuming Byzantine validators behave.
- **Well-formedness survives the restriction**: a correct block referencing
  every correct block below already names `≥ 2f+1` distinct creators, so A5 is
  met with no Byzantine reference.
- Antitone in `T` (`SynchronisedOn.mono`), which is what lets witnesses proved
  at `Correct` feed the quorum-relative L4.

### 6.5 L2, L3 — decisions are monotone, and propagate

```lean
theorem decided_mono (hsub : V.ids ⊆ V'.ids) (h : Decided U V k v) : Decided U V' k v

def View.full (U) : View Validator BlockId Payload U   -- ids := U.ids

theorem decided_full (h : Decided U V k v) : Decided U (View.full U) k v
```

- L2 says a validator **never revises** a decision as its view grows. The
  safety results say decisions do not *conflict*; this says they do not
  *change*. Worth distinguishing explicitly.
- L2 works only because `CertifiedIn` is universe-level (§3.3).
- L3 is the notes' first claim — *after GST, if one correct validator commits
  all will commit* — with the time content removed. `View.full` is every
  correct validator's eventual view, so this **is** "all correct validators
  eventually reach the same decision". It also fixes what `U` means: not every
  block anyone ever wrote, but every block some correct validator ever held. A
  Byzantine block revealed to nobody is simply not in the universe.

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

theorem decided_of_leader_mem … :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L)
```

**Two layers of coverage and nothing else.** Every correct round-`(r+1)` block
references `L` by coverage; every correct round-`(r+2)` block references all of
*those*, so its votes for `L` come from a quorum and it certifies; there are
`2f+1` correct validators, so the certificates themselves form a quorum.

**No horizon, no growth, no limit universe.** The hypotheses are three local
`Populated` facts. This is why the horizon question could be settled without
touching the only real proof in the plan.

**L5 — an absent leader is skipped.**
```lean
theorem decided_none_of_leader_absent {V : View …}
    (h : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k) :
    Decided U V k none
```
Nearly free, and it vindicates the §3.4 decision: `Decided.directSkip`'s
premise is `∀ L, IsLeaderBlock U k L → …`, which holds **vacuously** when the
leader published nothing. A formulation that selected "the" leader block would
have had nothing to select.

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

**The quantifier order is the whole content, and this belongs in the report.**
The tempting form — *given `Live U D N`, for every `k` there is a committing
`k' ≥ k` with `slotRound k' + 2 ≤ N`* — is **not provable**: fairness promises
a correct leader *somewhere* beyond `k`, and that slot may lie past the
horizon. Fixing `U` and `N` first caps how far fairness may reach. Stated as
above, `k'` depends only on the **schedule**, and the DAG grows to it second.

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

### 6.8 L7b — the seam discharged from GST and backoff

The timing layer. Present the structure, then the three theorems.

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
- `waits` (lower bound) and `prompt` (upper bound) are the two protocol build
  rules. `prompt` is what makes drift controllable.
- `latest` is *attained* (`latest_mem`), not merely an upper bound — otherwise
  it carries no information.
- `Timing` carries a horizon for **exactly** the reason `Live` does: `blk` at
  every round would force infinitely many blocks into a `Finset`. Finding the
  same flaw twice is itself worth reporting (§8).

**Drift is derived, not assumed.**
```lean
def Timing.DriftFrom (n₀ D : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n, n₀ ≤ n → n ≤ N → tm.built w n ≤ tm.built v n + D

theorem Timing.driftFrom_of_prompt {n₀ : ℕ}
    (hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D)
    (hto : ∀ n, n₀ ≤ n → tm.delay ≤ tm.timeout n) :
    tm.DriftFrom n₀ D
```
A two-case split on `prompt`'s `max`: **timeout-limited** (everyone advanced
by the same `timeout n`, so the spread is unchanged) or **delivery-limited**
(finished by `latest n + delay`, and `latest` is attained). **Note what this
does not show: that drift shrinks.** It does not — every clock advances by the
same timeout. *Bounded* is all that is needed. [CHECK — an earlier draft
argued drift is *compressed* to 2Δ; that is wrong, and the correction is worth
a footnote.]

**The seam, discharged.**
```lean
theorem Timing.synchronisedOn_of_timing (hT : T ⊆ Correct)
    (hD : tm.DriftFrom R D) (hgst : tm.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + tm.delay ≤ tm.timeout n) :
    SynchronisedOn U T R
```
Four inequalities chained: drift, backoff, waiting, hence
`built w n + delay ≤ built v (n+1)` — exactly what `covers` wants.
Non-equivocation does the rest: `SynchronisedOn` quantifies over *every*
`T`-authored block and T1 identifies each with the `blk` the structure names.
*That is why `T ⊆ Correct` is needed here* — a Byzantine author could have
several blocks in a round and `blk` names only one.

**The headline.**
```lean
theorem exists_synchronisedOn_of_backoff (tm : Timing U T N) (hT : T ⊆ Correct)
    (hmono : Monotone tm.timeout) (hub : ∀ m, ∃ n, m ≤ tm.timeout n)
    {n₀ : ℕ} (hdel : ∀ n, n₀ ≤ n → tm.delay ≤ tm.timeout n)
    (hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D) :
    ∃ R, SynchronisedOn U T R
```

**The only property of the backoff used is that it grows without bound** — not
its shape, not its rate, and not the signal driving it. An implementation is
free to choose how it grows. What it is **not** free to do is *cap* the
timeout: a capped backoff satisfies neither hypothesis, and the system it
describes can be permanently stuck. That is a deployable conclusion and should
be stated as one.

### 6.9 The liveness stack, assembled

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
>   L7b  Timing: GST + Δ + waits + prompt + unbounded backoff
> ```

Say plainly: **nothing above the seam mentions time, and nothing below it
mentions certificates.**

---

## 7. Eventual DAG synchrony — the argument

This is the section the paper exists for. It should be able to stand alone.

### 7.1 The natural formulation does not work

The original proposal stated it on **views**:

> after GST, if a correct validator has a view `V₁`, then within Δ all correct
> validators' views will contain `V₁`.

This is appealing — `View` is already first-class, `V₁ ⊆ V₂` is already
meaningful, every safety result is already view-relative — and it **does**
give L3 directly: the common view *is* `View.full`.

**But it does not give coverage, and cannot.**

> **A block's references are frozen when it is built.** A correct validator
> building at round `n+1` waits for `2f+1` round-`n` blocks; the arrival of
> the `2f+1`st says nothing about the rest having arrived. Convergence of
> *views* does not retroactively enlarge *blocks*.

So the assumption has to be stated on `refs`, not on views. **This is a
genuine negative finding and should be presented as one** — it is the reason
the definition looks the way it does, and it is not obvious in advance.

### 7.2 Coverage is an outcome, not an instruction

The second thing the report must be honest about. A validator **cannot execute
`SynchronisedOn`**: it cannot tell which of its peers are correct, so "wait
for the correct blocks" is not a rule it can follow. What it can do is:

- wait on a **timeout** and build with whatever arrived;
- **raise** that timeout when commits stop arriving.

Before GST no period is long enough, and nothing lets a validator detect that
directly — what it observes is that **commits have stopped**. So the feedback
loop that delivers coverage is driven by *liveness failure*, the very thing
being proved away. `SynchronisedOn R` is the **outcome** of that loop once the
network settles.

§6.8 is what makes this rigorous rather than a story: `waits` and `prompt` are
rules a validator *can* follow, `covers` is the network, and coverage is the
theorem.

### 7.3 What the abstraction buys

1. **The consensus argument is purely combinatorial.** Round indices and
   `Finset` cardinalities. Compare: under a message-level assumption every
   statement carries instants.
2. **The timing content is quarantined** in one file, consumed through one
   definition.
3. **The seam is validated by two independent lower models** (§6.7, §6.8),
   built at different times against an unchanged interface. Nothing above
   `SynchronisedOn` changed when the timing layer was slotted in underneath.
   [CHECK — this is a methodological claim about the development history; it
   is true of this repository and the git history supports it, but it is
   evidence, not proof.]
4. **It composes with safety.** `SynchronisedOn` mentions only `U.ids`,
   `U.block` and `refs` — the same vocabulary the safety development already
   speaks.

### 7.4 What it costs

- **No Δ above the seam, so no quantitative claim.** No bound on `R − GST`, no
  commit latency, no throughput. Δ would force views indexed by an instant and
  every statement quantified over instants — for no proof content, since the
  theorems are *"all will commit"* and *"never gets stuck"*.
- **The gain is not logical.** One assumption becomes two; nothing becomes
  unconditional. With no time model the chain must bottom out at delivery.
  Say this rather than let a reader discover it.

### 7.5 Related work

[EXPAND] Positioning against:
- DAG-BFT liveness arguments as usually presented (DAG-Rider, Narwhal/Bullshark,
  Mysticeti, Shoal/Sailfish) — where the synchrony assumption sits in each.
- Partial synchrony (DLS) and the standard GST/Δ formulation.
- Mechanised consensus: what has been formalised and at what level of
  abstraction.
- The specific question: *has anyone else stated the synchrony assumption
  structurally on the DAG rather than on message delivery?*

---

## 8. Method: witness-first, and what it caught

A short methodological section, and an honest one. **Rule: a definition gets a
satisfiability witness before anything is proved from it.**

Witness models over a concrete 4-validator instance (`f = 1`):

| Model | What it witnesses |
|---|---|
| `Ugrow N` | `Live`, `DeliversQuorum`, `Synchronised` at every horizon |
| `ugrow_not_populated_succ` | the horizon is **tight** — nothing at `N+1` |
| `ugrowTiming` | `Timing`, in lockstep |
| `ugrowHonest` | a **genuinely partial view** — Byzantine validator withholds |
| `ugrowSkew` | **nonzero drift and delay**, both `driftFrom_of_prompt` branches live |

**Four defects the rule caught**, each of which would have produced vacuous or
false theorems:

1. `Live` was **unsatisfiable** — a `Finset` cannot hold a block at every
   round. Confirmed by proving `¬ Live⁰ U`.
2. `Timing` had the **identical** flaw, found the same way.
3. `Synchronised` had **never been defined in Lean at all** — it existed only
   in the design notes, and was discovered missing while writing a witness for
   it.
4. L6 as first stated was **false**; the fix was quantifier reordering (§6.6).

Two further points worth reporting:

- A **degenerate witness hides branches.** `ugrowTiming` has `delay = 0` and
  zero drift, so S6's delivery-limited branch was unreachable. `ugrowSkew` was
  built to reach it, and its constants are forced: `D + delay ≤ timeout` needs
  `timeout ≥ 4`; the delivery-limited branch needs `timeout ≤ 4`. **The window
  is a single point.** A first attempt at `timeout = 3` failed — which is
  exactly the check a degenerate witness cannot perform.
- One exhibit turned out to be **impossible**, informatively: a round-spread
  exhibit at `f = 1` cannot exist, because `|Correct| = 3 = 2f+1` exactly, so
  every correct validator is needed for a quorum and none can lag. A spread
  exhibit that still commits needs `f ≥ 2`. That is §4.3's combined budget
  appearing as a concrete obstruction rather than an inequality.

---

## 9. Limitations and open questions

State these as open, not solved.

- **Q3 — no quantitative version.** No bound on `R − GST`, no proof that the
  adaptive timeout converges in bounded time, no commit latency. Adding these
  brings back the time model above the seam and should be scoped separately.
- **Q4 — `FairScheduleOn` buys liveness but no rate.** The `∃ k' ≥ k` form
  says a correct leader recurs, not how often. Round-robin over `3f+1` would
  give `2f+1` of every `3f+1`. Leader predictability (and so targeted DoS) is
  unmodelled.
- **Q6 — presentational.** Whether L1 should hold from round 0 or only
  after `R`.
- **T4/T5 (certified DAGs)** are deferred by design, not omitted by accident.
- **Block-level total order** needs a tie-break within a flush (§5.6).

**One sentence that must appear:** none of the open questions affects whether
the stated theorems are *true* — only how much they *say*.

---

## 10. Artifact

- Lean 4 (v4.32.2) + Mathlib. `lake build`: 0 errors, 0 warnings, 8671 jobs.
- **Axiom audit, checked.** Every headline result — `reaches_of_quorum_support`
  (T3), `exists_common_correct_ancestor` (T3c), `decided_agree` (M6),
  `commitSeq_agree`, `outputAt_agree`, `no_stall` (L1), `commits_recur_on`
  (L6), `exists_synchronisedOn_of_backoff` (L7b) — depends on exactly
  `[propext, Classical.choice, Quot.sound]`. No `sorry`, no custom axiom, no
  `native_decide`. Reproduce the `#print axioms` block in the report.
- File map:

| File | Contents |
|---|---|
| `Validators.lean` | fault model, T0 |
| `Block.lean` | `Block`, `ValidWrt`, T0′ |
| `BlockDag.lean` | `BlockUniverse`, `View`, T1 |
| `CausalHistory.lean` | `Reaches`, T2, T6a |
| `Support.lean` | counting vocabulary, hitting/propagation |
| `Persistence.lean` | T3 |
| `CommonCore.lean` | T3a, T3c |
| `Mysticeti.lean` | the commit rule, M1–M6, the ledger |
| `Liveness.lean` | L0–L6, L7a |
| `Timing.lean` | L7b — logically the bottom of the stack, written last |
| `LeanDagTest/Growth.lean`, `Partial.lean`, `Model.lean` | witnesses |

- Design records: `spec.md` (safety, settled), `liveness.md` (liveness,
  including the settled questions S1–S7 and the open Q3/Q4/Q6).

---

## Appendix A — statement index

Label → Lean identifier → file. [EXPAND — merge `spec.md` §7's table with a
new liveness table; both exist and are current.]

## Appendix B — the four vacuous drafts

[EXPAND — the `¬ Live⁰` proof in full, and the L6 quantifier counterexample.
Short, concrete, and more convincing than the prose in §8.]
