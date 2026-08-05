# lean-dag — Equivocation, growth, and denial of service

Design notes for theorems about how the block DAG behaves when Byzantine
validators equivocate. Separate from `spec.md` and `liveness.md` because the
subject needs a new validity condition and a new measure — size — and because
the central theorem is not yet proved on paper, let alone in Lean. Things
graduate into `spec.md` once they settle.

**The question is not safety or liveness.** Both already hold under
equivocation: `no_equivocation` constrains correct validators only, and every
safety and liveness result in the development is stated against a universe in
which Byzantine validators may publish as many blocks per round as they like.
What is *not* addressed anywhere is **denial of service**: Byzantine
validators flood each round with blocks, and correct validators must store,
validate and exchange a view that grows without bound — until it exceeds
their network or storage capacity. Nothing currently rules this out, and the
model is expressive enough to say so.

The measure is already in place. §4.2 of `liveness.md` fixes `U` as *every
block some correct validator ever held* — not every block anyone ever wrote.
So `|U.ids|` **is** the storage burden imposed on the correct population, and
`|V.ids|` is one validator's share of it. A block a Byzantine validator
reveals to nobody is not in `U` and costs nothing.

> **Status.** Nothing here is implemented. §3, §4 and §6–§9 are proofs on
> paper that reuse existing machinery and should be routine in Lean. §10 is
> the hard one: it is stated as a conjecture, with the ingredients a proof
> would need and a candidate counterexample that none of them yet rules out.
> §12 lists what has to be decided first, §13 what is already settled.

## 1. What the existing development already gives

Worth listing, because most of what follows is assembled from it rather than
built:

| | |
|---|---|
| **T0′** `exists_correct_mem_creators_inter` | two reference quorums share a *correct* author |
| **T1** `eq_of_creator_eq` | a correct author has one block per round |
| **T2** `round_le_of_reaches` | causal history runs downward, one round per step |
| **T3** `reaches_of_quorum_support` | a quorum-backed block is in every later history |
| **T3c** `exists_common_correct_ancestor` | across three rounds, a common correct ancestor |
| **T6a** `View.exists_reaches_iff` | history questions are view-independent |
| **L0** `card_authorsAt_of_lt` | every round below a block has `2f+1` authors |
| `card_inter_correct_of_quorum` | a quorum of creators contains `f+1` correct ones |
| **`liveness.md` S5** | `PopulatedOn` / `SynchronisedOn` / L4 / L6 are parameterized by a validator set `T` |
| **`spec.md` §3.2** `distinct_creators` | one block never references two blocks by one author |

Three of these do more than they were written for. **`liveness.md`'s S5** is
what lets every liveness result be re-read as *"holds using correct validators
alone"*, which is exactly the regime the DoS condition leaves standing (§8).
(Unqualified `S`-numbers below always refer to §13 of this document.)
**`card_inter_correct_of_quorum`** gives the fact §9 turns on: *every* valid
block, Byzantine ones included, references at least `f+1` correct blocks of
the round below. And **`distinct_creators`** turns out to *force* the
acceptance rule of §3 rather than merely permit it (§8), and to make it
impossible for a block to report an equivocation through its references (§9).

## 2. Two senses of size

**A view has a size.** `V.ids` is a `Finset`; `|V.ids|` is what the validator
stores. Downward closure means a view with maximum round `r` spans rounds
`0…r` inclusive.

**A block has a history size.** `H(b) := {c | Reaches U b c}` — the full
causal graph defined by the references. `|H(b)|` is what a validator must
fetch and validate in order to accept `b`, and it is the quantity the attack
inflates.

These are different quantities: a validator may be sent blocks it never
references, and may fetch blocks on demand that it does not retain. §3 shows
that under one natural acceptance rule the first is bounded by the second — and
in the ordinary case *equals* it — so that **everything reduces to bounding
`|H(b)|`**, which is §10.

There is a third quantity, **bandwidth**, which is neither: blocks a validator
receives, inspects and discards. Nothing in the model can see it — `U` records
what was *held*, and there is no notion of a message. Every bound below is
about storage, and a flood rejected on arrival remains outside the scope of
all of them.

## 3. From history size to view size

The rule: *a correct validator accepts at most one block per validator at its
latest round, and its view is the causal history of what it accepts.*

```lean
/-- The frontier a validator has accepted: one round, at most one block per author. -/
def Accepted (U) (A : Finset BlockId) (n : ℕ) : Prop :=
  A ⊆ U.ids ∧ (∀ i ∈ A, (U.block i).round = n) ∧
    ∀ i ∈ A, ∀ j ∈ A, (U.block i).creator = (U.block j).creator → i = j

/-- The view an accepted set generates. -/
def View.ofAccepted (U) (A : Finset BlockId) (h : Accepted U A n) : View … U where
  ids := A.biUnion (history U)
  …
```

`A` is the **frontier** — the latest round only. Earlier rounds are not
accepted separately; they enter the view inside the histories, which is what
makes `|A| ≤ 3f+1` rather than `≤ (3f+1)(r+1)`. A cumulative variant, where
every round's acceptances are kept, is equally sound and costs exactly one
factor of `r` in D2.

**Where `A` comes from.** It is not a new object invented for the size bound.
§8 shows the delivery layer needs exactly this set for an unrelated reason —
`Delivery.includes` is unsatisfiable without it — and gives it a home as a
field, `accepted v n`. The view validator `v` stores at round `n` is the one
generated by `accepted v n`, and `accepted_inj` there *is* the injectivity
hypothesis D2 consumes. One object, and §13 S5 records why it cannot be folded
into `held`.

- **D1 — a generated view is a view.** `A.biUnion (history U)` is downward
  closed, because a union of causal histories is.

  Nothing has to be assumed and no closure obligation is discharged by hand:
  `View.ofAccepted` is a definition, and the acceptance rule lands inside the
  existing model rather than beside it.

- **D2 — the bridge.** If `V` is generated by an accepted set `A`, then

  `|V| ≤ (3f+1) · max_{b ∈ A} |H(b)|`.

  `Finset.card_biUnion_le` bounds `|V|` by the sum, and `|A| ≤ 3f+1` because
  `creator` is injective on `A` and there are `3f+1` validators. Ten lines,
  and **unconditional** — no DoS condition, no synchrony, no correctness.

- **D3 — the sharp form.** If the validator references *everything* it has
  accepted, its view is exactly the causal history of the block it is about to
  build: `H(b) = {b} ∪ V`, so `|V| = |H(b)| - 1`.

  The factor `3f+1` disappears — but only when `refs = A`, which the repaired
  `Delivery.includes` (§8) gives exactly when no author in the accepted set is
  exposed.

  **When exposure does drop a reference, the identity fails in the unhelpful
  direction.** The dropped block is still *retained*, so `V ⊋ H(b) \ {b}` and
  `|V| ≥ |H(b)| - 1`, which bounds nothing. D2 is then the operative result,
  and it is unaffected: it counts `A`, not `b.refs`. The principle to hold on
  to is that **exclusion governs what you reference, not what you retain** —
  which is also what makes D4 work.

- **D4 — monotone, if you reference your own previous block.** If `v`'s
  round-`(r+1)` block references `v`'s round-`r` block, then
  `H(b_r) ⊆ H(b_{r+1})`, so the generated views grow: `V_r ⊆ V_{r+1}`.

  This matters because a view defined as *the history of the latest accepted
  blocks* otherwise **forgets** — blocks accepted at round `r` that nothing at
  `r+1` references drop out — and every decision result (L2, L3, M6) is stated
  over growing views. Self-reference, which DAG protocols do anyway, closes the
  ordinary case: the view is monotone and L2 applies unmodified. Without it the
  model would need a notion of a decision recorded outside the view, which it
  does not have.

  **The exposure clause reopens it, and the same principle closes it again.** A
  block dropped because its author became exposed is *not* in the next block's
  history, so a frontier-only view would forget it — and it might be a
  certificate some decision rested on. Retention is the answer: a validator
  keeps what it accepted even after the author is excluded, so `V` grows
  monotonically while `refs` shrink. Nothing is lost by retaining, since D2
  bounds the retained view either way.

**What must not be assumed.** The rule constrains `A`, not `V`. A round-`r`
block by `w` may reference a different half of `v`'s round-`(r-1)` equivocation
than the one this validator accepted, so `V` will hold both. The tempting
shortcut — *"my view has at most `(3f+1)(r+1)` blocks by construction"* — is
therefore **false**, and the whole burden really does sit on §10. What the
rule buys is the reduction, not the bound.

**What it costs.** The rule must retain everything in the accepted
*histories*, not merely the accepted blocks. Retaining one block per author
per round and discarding the rest breaks the correct backbone, not just the
Byzantine fringe: correct `w` references `v`'s block `A`, correct `u` kept only
`B`, and now `u` cannot validate `w`'s block at all. Generated views have this
right by construction, since `A` arrives inside `H(w's block)`.

This also disposes of the fetch-versus-retain tension: what a validator must
fetch to validate `b` is exactly `H(b)`, which is exactly what it retains.
There is no third quantity *for storage* — bandwidth remains outside the model
(§2). See §13 S1.

## 4. Baseline — no equivocation

- **D5 (upper).** If no validator equivocates, a view with maximum round `r`
  holds at most `(3f+1)(r+1)` blocks.

  One block per validator per round, `3f+1` validators, `r+1` rounds. Note the
  `r+1`: the view is downward closed, so round `0` is present and counted.

  In Lean this is the counting criterion detection needs anyway — `creator` is
  injective on a round exactly when nobody equivocates there, so
  `|blocksAt V n| = |authorsAt V n| ≤ 3f+1` — summed over `n ≤ r`.

- **D6 (lower).** A view with a block at round `r` holds at least
  `(2f+1)·r + 1` blocks.

  This is **L0**, not the common core: L0 already gives `2f+1` distinct
  *authors* at every round strictly below `r`, hence at least that many
  blocks, and distinct rounds hold disjoint blocks. The `+1` counts the block
  at round `r` itself. T3c produces a common *ancestor* and says nothing about
  counts, so it is the wrong tool here — and the L0 route needs validity
  alone: no correctness hypothesis, no equivocation hypothesis, no synchrony.

  D6 holds **with or without** equivocation, since equivocation only adds
  blocks.

So without equivocation, `(2f+1)r + 1 ≤ |V| ≤ (3f+1)(r+1)`. Both ends are
attained: the upper when every validator publishes at every round, the lower
when exactly `2f+1` do.

## 5. What equivocation does to history size

Everything here is about `H(b)` for a single valid block `b` at round `r`.
Write `m_s` for the number of distinct blocks of `H(b)` at round `s`.

- **D7 (the top two layers).** `H(b)`'s round-`(r-1)` layer is exactly
  `b.refs`, and carries no equivocation.

  Rounds decrease by exactly one per reference step (T2), so everything in
  `H(b)` at round `r-1` is a direct reference of `b`, and `distinct_creators`
  makes those authors distinct.

  **Stated per block, not per round.** `distinct_creators` constrains one
  block's references; it does *not* say round `r-1` of the DAG is
  equivocation-free. Two different round-`r` blocks may perfectly well
  reference opposite sides of an `r-1` equivocation.

- **D8 (an equivocation is only ever visible at a merge).** A round-`n`
  equivocation appears in no history below round `n+2`, and appears in one
  only at a block that references two branches carrying different halves —
  at round `n+2`, two round-`(n+1)` blocks naming different halves; higher up,
  two sub-branches that already disagree.

  Immediate from D7, and more consequential than it looks: **the reference
  graph cannot carry evidence of an equivocation one round after the fact.** A
  correct validator that has received both halves cannot say so in its next
  block — the two references it would need are exactly what
  `distinct_creators` forbids. §9 is what follows from that.

- **D9 (the layer recurrence).** `m_s ≤ (3f+1) + f · m_{s+1}`.

  Each block of layer `s+1` references `2f+1` distinct creators, of which at
  most `f` are Byzantine. Correct authors contribute at most one block each
  (T1) and are shared across the whole layer; different blocks may name
  *different* Byzantine blocks. So layer `s` holds at most `3f+1`
  correct-authored blocks and at most `f · m_{s+1}` Byzantine-authored ones.

  Unrolled from `m_r = 1` this is `O(f^{r-s})`: **history size can be
  exponential in the number of rounds**. Round `r-2` is the first instance —
  up to `f(2f+1)` Byzantine blocks — as D8 requires.

- **D10 (when the blow-up is possible at all).** D9's exponential needs
  `f ≥ 2`.

  - `f = 1`: the recurrence is `m_s ≤ 4 + m_{s+1}` — **linear**, no attack.
  - A single equivocating validator `Y`, any `f`: each round-`(s+1)` block
    references at most one `Y`-block, so `n_s ≤ m_{s+1} ≤ (3f+1) + n_{s+1}`,
    giving `n_s ≤ (3f+1)(r-s)` and `|H(b)| = O(f·r²)` — **quadratic**, bad but
    not fatal.

  The exponential therefore needs **two or more equivocators amplifying each
  other**. This matters for staging: every model in `LeanDagTest` is `f = 1`
  over `Fin 4`, so none of them can exhibit the attack, and a witness needs
  `f = 2`, `n = 7` (§11).

## 6. The DoS-protection condition

> If a block's history contains an equivocation by validator `X`, then `X`
> may not be used as one of that block's references.

```lean
/-- `X` is exposed in `b`'s history: two distinct blocks by `X`, one round. -/
def ExposedIn (U) (b : BlockId) (X : Validator) : Prop :=
  ∃ i j, Reaches U b i ∧ Reaches U b j ∧ i ≠ j ∧
    (U.block i).creator = X ∧ (U.block j).creator = X ∧
    (U.block i).round = (U.block j).round

def DoSValid (U : BlockUniverse …) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator
```

**It is a predicate on the universe, not a field of `ValidWrt`.** This is the
single most important modelling decision here, and it is what answers *"I
would love to not re-do all the liveness proofs"*. Adding a conjunct to
`ValidWrt` changes the type of every block universe, so every existing proof
would be re-elaborated and every witness in `LeanDagTest` rebuilt. As a
separate predicate, every safety and liveness theorem applies **verbatim and
unmodified**, and the new results simply take `(hdos : DoSValid U)` as an
extra hypothesis. Results are then automatically available in both regimes,
which is the modularity being asked for.

**It is well founded despite appearances.** The condition on `b` constrains
`b.refs` in terms of `H(b)`, and `H(b) = {b} ∪ ⋃_{i ∈ b.refs} H(i)`. Since `b`
is the only block of `H(b)` at its own round (D7), the condition depends only
on the histories of `b`'s references. No circularity.

**And it is constructible, which is a separate question.** As a predicate on a
finished universe the condition is well defined; as a rule a validator must
*satisfy while building*, it looks like a fixed point — adding a reference
enlarges the history, which can expose an author already referenced. It
converges, and the argument is short enough to record here because §8's
liveness claim leans on it:

> Start from everything accepted. Compute the exposed set; drop the references
> naming it; recompute. Dropping references only shrinks `H(b)`, and exposure
> is monotone in the history (D12), so the exposed set only shrinks — the
> iteration never re-exposes what it just dropped and terminates after at most
> `f` rounds, since only Byzantine authors are ever exposed (D15).

The fixed point always retains every correct block, because a correct author is
never exposed. So a correct validator can always build: it keeps at least the
`2f+1` correct references it accepted, which is a quorum.

- **D11 — inflation *is* exposure.** For every block `b` and every validator
  `X`, exactly one of:

  - `H(b)` holds at most one `X`-block per round, so `X` contributes at most
    `r+1` blocks to it and the equivocation gained `X` nothing; or
  - `X` is exposed in `H(b)`, and `b` may not reference `X`.

  This is not a theorem — it is the definition of `ExposedIn` read twice.
  *"`X`'s equivocation inflated `H(b)`"* and *"`X` is exposed in `H(b)`"* are
  the same sentence.

  It is worth stating as a numbered result anyway, because it settles what the
  condition is *for*. The mechanism does not need to **catch** equivocators;
  it needs exclusion to become automatic whenever they do damage, and it is —
  tautologically. In particular, whether correct validators break ties
  deterministically (all accepting the same half, so no merge ever occurs) or
  by first-seen (merges occur, exposure follows) is **not** a security
  parameter: agreeing means nobody is caught *and* nobody is harmed. See §13
  S3.

**It is checkable, and everyone checks it the same way.** Two more
consequences, both one-liners off existing lemmas:

- **D12 (exposure is monotone along history).**
  `Reaches U c b → ExposedIn U b X → ExposedIn U c X`.

  Transitivity of `Reaches`. Exclusion, once earned, is inherited by
  everything above: an excluded validator is excluded forever, downstream.

- **D13 (exposure is view-independent).** For `b` in a view `V`, the exposure
  test computed inside `V` and inside `U` agree — `View.exists_reaches_iff`
  (T6a), the same argument that makes `CertifiedIn` well defined.

  This is what makes the condition a *validity* condition rather than a matter
  of opinion: two correct validators holding different views never disagree
  about whether a block is DoS-valid.

**What it does and does not cover.** The condition constrains *references*, so
it bounds the histories a validator must retain. It says nothing about blocks
merely delivered and never referenced — those are handled by §3's acceptance
rule, which discards them, and by nothing at all if the concern is bandwidth
(§2). The two mechanisms divide the work cleanly: acceptance bounds what a
flood can make you keep, `DoSValid` bounds what a reference can make you fetch.

## 7. Safety

- **D14.** Every safety result holds unchanged under `DoSValid`.

  Not "trivially unaffected" but *literally untouched*: `DoSValid U` is an
  extra hypothesis, and T1–T5, M1–M6 and the `Decided` results never mention
  it. Nothing to prove and nothing to re-check. This is the payoff of §6's
  modelling decision, and the reason for making it.

## 8. Liveness

The claim is that the condition can only ever exclude Byzantine validators, so
liveness survives. That is right, and better supported than it first looks:

- **D15 (exclusion is sound).** `ExposedIn U b X → X ∉ Correct`.

  T1 contraposed: two distinct blocks by one author at one round refute that
  author's correctness. So a correct validator is **never** excluded, by
  anyone, ever — and `|Correct| ≥ 2f+1` means a legal reference quorum
  consisting entirely of correct validators always exists in principle.

- Every liveness result is already stated over a validator set `T`
  (`PopulatedOn`, `SynchronisedOn`, L4, L6 — `liveness.md` S5), and
  `T := Correct` is exactly the instance the condition leaves standing.
  `SynchronisedOn U Correct R` — correct blocks reference correct blocks — is
  consistent with `DoSValid` for the same reason.

### A defect in the delivery layer, independent of all of the above

`Delivery.includes` says a correct validator references **everything it held**:

```
held v n ⊆ (U.block b).refs
```

Combined with `distinct_creators`, this makes `Delivery` **unsatisfiable
whenever a correct validator holds both halves of an equivocation** at a round
it builds on: both held blocks would have to be referenced, and no valid block
may reference two blocks by one author. The existing witnesses hide this —
`ugrowDelivery` sets `held` to *every* round-`n` block, which is consistent
only because `Ugrow` contains no equivocation at all.

So the delivery layer as it stands cannot express the scenario this document is
about. It has to be repaired regardless of whether the DoS condition is
adopted, and the repair is exactly §3's acceptance rule:

> a correct validator references everything it **accepted**, where the accepted
> set holds at most one block per author and excludes exposed authors.

The acceptance rule is therefore not an extra assumption bolted on for storage
reasons. It is **forced by block validity**: a validator holding two blocks by
one author *must* choose one, because it cannot reference both. §3's D3 is the
same statement read from the other side, and §13 S2 records the conclusion.

### The repair

`held` is currently doing two jobs — *what the network delivered* and *what the
validator built on*. Until equivocation nothing forced them apart. Splitting
them is the whole repair:

```lean
accepted     : Validator → ℕ → Finset BlockId
accepted_sub : ∀ v n, accepted v n ⊆ held v n
accepted_inj : ∀ v n, ∀ i ∈ accepted v n, ∀ j ∈ accepted v n,
                 (U.block i).creator = (U.block j).creator → i = j
includes     : ∀ v ∈ Correct, ∀ n, ∀ b ∈ U.ids, creator b = v → round b = n + 1 →
                 ∀ i ∈ accepted v n, ¬ ExposedIn U b (U.block i).creator →
                   i ∈ (U.block b).refs
```

As with `held`, the model says nothing about *how* the choice is made —
first-seen, lowest id, anything. That is the same treatment `held` already
gets: the model never says when the timeout fires, only what was in hand when
it did. By D11 the policy is not a security parameter anyway.

Two decisions inside this are worth recording.

**The subtraction of exposed authors sits in `includes`, not in `accepted`.**
Were `accepted` itself to exclude them, `Delivery` would only be definable
under `DoSValid`, and §6's whole point was that the condition stays an opt-in
predicate existing results never mention. As written, one `Delivery` serves
both regimes: in the vanilla regime the new `includes` is strictly *weaker*
than the old one, and nothing downstream notices, because L7 needs only
correct-to-correct coverage and a correct author is never exposed (D15).

**`held` is not deduplicated**, and must not be. `liveness.md` §4.2 defines `U`
as every block some correct validator held; deduplicating at the delivery layer
would put the second half of an equivocation outside `U` altogether, and every
result in this document would hold vacuously in exactly the case it is about.
See §13 S5.

### What that costs

Two definitions change, and one result weakens:

- `Delivery.includes` — as above. L7 (`synchronised_of_delivery`) changes with
  it, but its proof survives: correct blocks are unique, so a correct validator
  never has to choose between them, and correct-to-correct coverage is
  untouched. `ugrowDelivery` migrates by setting `accepted := held`, whose
  `accepted_inj` obligation `Ugrow` discharges by construction.
- `DeliversQuorum` — *a quorum of authors that exists is eventually held*. L1
  needs a quorum of **admissible** authors. After `R` this is free from
  `EventuallyDelivers`, since all correct blocks arrive and correct validators
  are never excluded. **Before `R` it is not**: a validator may hold a quorum
  of round-`n` blocks some of whose authors it has just excluded, and stall.

So L1 — *no stall, from round 0, with no synchrony at all* — is the one result
the condition genuinely costs, unless `DeliversQuorum` is strengthened to
deliver a **correct** quorum. That is an assumption change rather than a proof
change, but it should be made deliberately (§12 Q1) rather than discovered
halfway through a proof.

## 9. Exclusion after `R`

By D8 an equivocation is visible only where two branches merge, and by D11
that is exactly where it does damage. After `R` the correct population cannot
avoid merging: synchrony manufactures the merge, and D16–D17 turn it into total
exclusion. D18 is a companion — what an author gives up by publishing honestly
— and is included because the *failure* of its hypothesis is the opening §10's
counterexample needs. **No new modelling primitive is needed**; see §13 S3 for
the evidence channel that was considered and rejected.

Throughout, `n ≥ R` and `X` is any validator.

- **D16 (after `R`: agree, or be exposed).** Either the histories of all
  correct round-`n` blocks *jointly* hold at most one `X`-block per round, or
  every correct round-`(n+1)` block is exposed to `X`.

  `SynchronisedOn U Correct R` puts *every* correct round-`n` block into the
  references of *every* correct round-`(n+1)` block, so each of the latter
  contains the union of all the former's histories. If that union holds two
  `X`-blocks at one round, every correct block one round up is exposed.

  So no tie-break policy can help the adversary: correct validators either
  agree about `X` — in which case, by D11, `X` gains nothing — or they
  disagree, and are all exposed one round later.

- **D17 (exclusion is total, and permanent).** If every correct round-`(n+1)`
  block is exposed to `X`, then **no valid block** at any round `≥ n+2` may
  reference `X`, Byzantine blocks included.

  Every valid block references `2f+1` distinct creators, of which at most `f`
  are Byzantine, so at least `f+1` of its references are correct blocks of the
  round below (`card_inter_correct_of_quorum`). At round `n+2` those are
  exposed by hypothesis, so the referencing block is exposed too (D12), and
  `DoSValid` forbids it from naming `X`. The same step carries the exposure up
  one round at a time, so it never lapses.

  Note that no synchrony is used here — only that every block, however
  authored, must lean on `f+1` correct blocks. Synchrony is what produces the
  antecedent (D16), not what propagates it.

- **D18 (pinning).** Suppose at round `j ≥ R` the correct validators that
  accepted an `X`-block all accepted the *same* block `A`, and that **at most
  `f` correct validators accepted none**. Then every valid block at round
  `≥ j+2` holds `A` in its history, and may not reference any other `X`-block
  of round `j`.

  Every valid block leans on `f+1` correct blocks of the round below (D17). To
  avoid holding `A` it would have to draw all `f+1` from correct validators
  that lack it, and by hypothesis there are at most `f` of those. So it holds
  `A`; naming a different round-`j` `X`-block would then expose `X` and be
  forbidden.

  **The counting hypothesis is not cosmetic, and it is what a Byzantine author
  attacks.** `Synchronised` covers correct authors only — deliberately, since a
  Byzantine validator may publish to a strict subset or not at all
  (`liveness.md` §4.3). So `X` avoids being pinned at round `j` simply by
  publishing to at most `|Correct| - f - 1` correct validators. Pinning is
  therefore a fact about Byzantine validators that behave *normally*: publish
  to everyone and you lose the freedom to disagree about that round later.
  Publish selectively, and you keep it — which is the gap §10's counterexample
  exploits.

All three results are conditional on the rounds involved being populated: with
no correct block at round `n+1` there is nothing to expose, and equally no
valid block at `n+2`, so they hold vacuously rather than falsely. L1 supplies
population where it is wanted.

Together: post-`R`, an equivocation is either invisible to the correct
population — in which case, by D11, it inflates nothing those validators hold —
or it is excluded from the entire universe within two rounds of becoming
visible. What this does **not** rule out is a single one-shot reveal per
Byzantine author, of a history built out of sight; see §13 S4.

## 10. The main bound

The target: **under `DoSValid`, `|H(b)|` is polynomial in `r` — ideally
`(3f+1)(r+1) + g(f)`** — rather than exponential as D9 permits. By §3 this is
simultaneously the bound on view size, so it is the whole game.

Easy, and provable now:

- **D19a (clean histories are linear).** If `H(b)` contains no equivocation at
  all, `|H(b)| ≤ (3f+1)(r+1)`. Immediate from D5's counting.

- **D19b (a block is clean about what it references).** If `b` references
  author `X`, then `H(b)` holds at most one `X`-block per round, hence at most
  `r+1` of them. Directly from `DoSValid`, and the sharpest tool available: a
  block referencing `k` Byzantine authors must be consistent about all `k`, so
  its sub-branches cannot disagree about any of them. **The blow-up in `H(b)`
  can only come from authors `b` does not reference** — at most `f` of them,
  fewer if `b` names Byzantine authors at all.

The conjecture:

- **C1.** Under `DoSValid`, `|H(b)| ≤ (3f+1)(r+1) + g(f)` for some `g`
  depending on `f` alone.

  Four ingredients are in hand, and they are close to sufficient without being
  so:

  1. **D11** — inflation and exposure are the same event, so the adversary
     cannot inflate silently.
  2. **D19b** — a block must be consistent about every author it references,
     so a merge of disagreeing branches can only be performed by a block that
     abstains from naming the disputed author, and abstains from then on (D12).
  3. **D18** — after `R`, disagreement about an author's round-`j` block is
     impossible once that block has reached all but `f` of the correct
     validators.
  4. **Bounded dirt** — let `D(b)` be the set of authors exposed in `H(b)`. By
     D15, `D(b) ⊆ Byzantine`, so `|D(b)| ≤ f`; and `D` is monotone up the DAG
     (D12). So along any upward chain, at most `f` blocks are the first to
     dispute a *new* author.

  **Where it still does not close.** Ingredient 4 bounds how many *distinct
  authors* can ever come into dispute — never more than `f` — but not how many
  blocks of an already-disputed author can be gathered. Once `X` is disputed at
  some block, every block above it is disputed about `X` too, and gathering
  further `X`-blocks costs nothing, since gathering requires no cleanliness —
  only *naming* does. Width is what needs bounding, and the only pressure on it
  is that `k` mutually inconsistent branches need `k` blocks by distinct authors
  at each level above them (`distinct_creators` prevents one block from taking
  two) — a per-level factor of `f`, which is exactly D9's, and `f` compounding
  over `r` levels is the exponential we are trying to rule out.

  Ingredient 3 does not help here either: it bites only at rounds where the
  author published to nearly everyone, and an author mounting this attack
  publishes to nobody.

  **The candidate counterexample, sharpened.** `f = 2`, `n = 7`, `X` and `Y`
  Byzantine. Both stay silent toward correct validators — so no round is pinned
  for either (defeating 3) — and build a secret binary tree in which each block
  names one `X`-block and one `Y`-block of the round below. Reveal the root at
  round `r`. What must be checked is whether such a tree can be **valid**: by
  D19b, a block naming both `X` and `Y` must be consistent about both, so its
  two subtrees must agree about both — which appears to collapse the branching
  to nothing. If that is right, the attack needs the merging blocks to *abstain*
  from naming the disputed authors, and then the question is how many distinct
  authors remain available to do the gathering. **This is the crux, and it is
  where the effort should go**: either a family that survives all four
  ingredients, or the argument that no family can.

  Note that a refutation would not be a disaster: it would say the condition
  must be supplemented, and §12 Q2 lists by what. And by D16–D18 the damage is
  in any case confined to **one reveal per Byzantine author** — see §13 S4.
  C1 is exactly the question of how large a single reveal can be.

## 11. Staging and witnesses

The house rule — *a definition gets a witness before anything is proved from
it* — bites hard here, and in an unusual way: the definitions are easy to
satisfy **vacuously**.

- `DoSValid` holds trivially of every `LeanDagTest` model, since none contains
  an equivocation reachable from anything. A witness that shows the condition
  *bites* needs an equivocation, a block excluded because of it, and a block
  that remains valid — otherwise D14, D15 and D16–D18 are all being checked
  against a hypothesis nothing exercises.
- **A biting witness is cheap; the *attack* witness is not.** Exposure and
  exclusion can be exhibited at `f = 1`, `n = 4`, over a model of the kind
  `LeanDagTest` already has: `X` equivocates at round 0, two round-1 blocks name
  different halves, and the round-2 block that names both is exposed and thereby
  forbidden to reference `X`. That covers D11, D12 and D17 and needs no new fault
  instance. What genuinely needs **`f = 2`, `n = 7`** is the *attack*: by D10 the
  exponential does not exist at `f = 1`, so C1 is trivially true there and any
  counterexample search over `Fin 4` is wasted effort.
- `Live` and `DoSValid` must be shown **jointly** satisfiable at every horizon,
  or §8 is vacuous — and this now requires the repaired `Delivery`, so
  `ugrowDelivery` has to be rebuilt around an accepted set rather than around
  *every* round-`n` block.

Suggested order, easiest first:

1. `history` as a `Finset` (§13 S6), `ExposedIn`, D11, D12, D13 — no new
   machinery, all off `Reaches` and T6a.
2. `View.ofAccepted`, D1–D4 — the bridge. Independent of everything else, and
   what makes the later bounds worth having.
3. D5, D6, D19a, D19b — counting; needs the round-partition lemma and L0.
4. D14 — free, by construction of §6.
5. D7, D8 — one line each, and the facts §9 turns on. Then the `f = 1`
   biting witness, so that nothing after this point is checked against a
   hypothesis no model exercises.
6. The repaired `Delivery` (§8, §13 S5), and D15; L1 re-earned or explicitly
   weakened.
7. **D16, D17, D18** — the first results with real content. D17 is the one that
   needs care, since it quantifies over Byzantine blocks too.
8. The `f = 2` model, and the C1 counterexample search against it.
9. C1, or its refutation, or a weakened form.

Steps 1–7 are believed routine. Step 9 is the research.

## 12. Open questions

**Q1 — Should `DeliversQuorum` be strengthened to a correct quorum?** (§8.)
The alternative is to accept that L1 holds only after `R` under `DoSValid`.
`liveness.md` Q6 already asks a version of this for a different reason; the two
answers should agree.

**Q2 — What is the fallback if C1 is false?** If the adversary can sustain
exponential histories under `DoSValid`, the condition has to be strengthened.
The candidates, in increasing order of cost: exclude an author on *first*
exposure anywhere in the view rather than in the history (breaks D13 —
view-dependence, so blocks would no longer be objectively valid); require
histories to be equivocation-free outright (kills liveness: after any
equivocation reaches the backbone, no correct validator could ever build
again); or bound the number of blocks per author per round admitted into a
view, which is a rate limit rather than a validity condition and lands outside
the model. None is attractive, which is a reason to look for the
counterexample early (§10).

**Q3 — Should the condition be *forward-looking* instead?** As stated, a block
may not reference an exposed author. A weaker and possibly sufficient form is
that a block may not reference a *block* whose author is exposed **in that
block's own history** — closer to "do not build on a liar's lies" than "do not
build on a liar". Worth checking whether the weaker form still supports D17,
since it costs strictly less liveness.

**Q4 — Where does it live?** `ExposedIn`, D11, D12, D13 and D15 have no
dependency on the counting results and could sit beside `CausalHistory`; the
size results need L0 and therefore sit above `Liveness`; the bridge (§3) needs
only `View`. That argues for two files, with the DoS condition and the bounds
in the upper one.

## 13. Settled

**S1 — View size versus history size: both, and they compose.** The two are
different quantities (§2), and the temptation is to choose one as *the* target.
The right answer is that the acceptance rule of §3 reduces the first to the
second — `|V| ≤ (3f+1)·max|H(b)|` in general (D2), and `|V| = |H(b)| - 1` for
the block the validator is about to build (D3). So the DoS condition can stay a
statement about **histories**, where it is objectively checkable and
view-independent (D13), while the storage claim is about **views**, where it
belongs; and the bridge between them is ten lines that assume nothing.

The four things that had to be got right along the way are recorded in §3: the
rule constrains the accepted set and not the view; generated views must retain
whole histories rather than one block per author; self-reference is what keeps
them monotone; and **exclusion governs what you reference, not what you
retain** — a validator keeps what it accepted even after the author is
excluded, which is what stops D3's exposure clause from breaking D4, and costs
nothing because D2 bounds the retained view regardless.

**S2 — The acceptance rule is forced, not chosen.** §8: `Delivery.includes` as
currently written is unsatisfiable in the presence of equivocation, because
`distinct_creators` forbids referencing both halves. Any repair must have the
validator choose one block per author, which is the acceptance rule. The
storage argument and the validity argument arrive at the same rule
independently.

**S3 — No evidence channel.** D8 says the reference graph cannot report an
equivocation, and the obvious repair is to carry a reporting relation alongside
the universe — an `Evidence` structure with `reported`, `sound`, `carried` and
`reports` fields, in the way `Delivery` was added. It was considered and
**rejected**:

- D11 removes the motivation. Exposure is not a punishment mechanism that must
  fire reliably; it is the same event as the damage. An equivocator that is
  never exposed is an equivocator that never inflated anything.
- After `R` it is redundant. D16 shows synchrony produces the merge whatever
  the correct validators' tie-break policy, and D17 turns that into total
  exclusion — one round earlier reporting would buy nothing.
- Before `R` it does not work anyway. The adversary sends one half to one set
  of correct validators and the other half to a disjoint set; no single correct
  validator holds both, so there is nothing to report, evidence channel or not.
  Reporting fires only once views converge — and once they converge, D16 fires.
- It costs four fields needing four witnesses, turns D12 from a free lemma into
  an assumption (`carried`), and drags a positive behavioural obligation
  (`reports`) into what is otherwise a pure validity condition.

Revisit only if **accountability** becomes a goal in its own right — proving
misbehaviour to a third party, slashing — which is a different objective from
bounding storage, and would want the evidence in the block payload rather than
beside the universe.

**S4 — What the DoS results can promise, and what they cannot.** Whatever the
fate of C1, D16–D18 give the shape of the guarantee: after `R`, an equivocating
validator is either invisible to the correct population — inflating nothing
they hold — or exposed, and then excluded from the whole universe within two
rounds (D17).

What that leaves is **one reveal per Byzantine author**. An author may build a
history out of sight, at any rounds it likes, and reveal it by getting a single
block accepted. Accepting that block pulls in the whole history, exposes the
author, and is the last block ever accepted from it — but the storage has
already been spent. So the residual damage is bounded by

> `f` × (the largest history a single valid block can have)

and bounding the second factor is precisely **C1**. This is why C1 cannot be
dismissed as an asymptotic nicety, and why it is not a purely pre-GST question:
the reveal can be constructed and delivered after `R` just as well as before.

What is genuinely settled is that the damage is **one-shot per author** rather
than recurring: exclusion is permanent (D12) and total (D17), so there is no
second reveal to defend against.

**S5 — `held` is what arrived; `accepted` is what you build on.** §8. The two
were one field because until equivocation nothing forced them apart. They must
be separate, and the direction matters: `held` stays undeduplicated, because
`liveness.md` §4.2 defines `U` as every block some correct validator held, and
deduplicating at the delivery layer would put the second half of an
equivocation outside `U` — making every result in this document vacuously true
in exactly the case it is about. The choice of *which* block to accept is left
unspecified, as the timeout already is, and by D11 it is not a security
parameter. The subtraction of exposed authors sits in `includes`, not in
`accepted`, so that one `Delivery` serves both the vanilla and the DoS regime.

**S6 — `history` is defined by recursion on the round, not by `filter`.**
Counting needs a `Finset`, and `Reaches` is `ReflTransGen`, so
`U.ids.filter (Reaches U b ·)` needs a `DecidablePred` that is not free.
Well-founded recursion on the round does not work either, since `U.block` is
junk outside `U.ids` and the round need not decrease there. Fuel indexed by the
round is structural and computable:

```lean
def historyUpto (U) : ℕ → BlockId → Finset BlockId
  | 0,   b => {b}
  | n+1, b => insert b ((U.block b).refs.biUnion (historyUpto U n))

def history (U) (b : BlockId) : Finset BlockId := historyUpto U ((U.block b).round + 1) b
```

with one lemma to earn: `b ∈ U.ids → (i ∈ history U b ↔ Reaches U b i)`, off T2
— the round strictly decreases per step, so the fuel is never short. The
alternative, a `Classical.dec` instance, would have blocked `decide` in the
concrete models on which §11 depends.

**S7 — `Delivery` requires self-reference.** D4 needs a correct validator's
block to reference its own previous block. DAG protocols do this anyway, it is
one field, and without it generated views are not monotone, so the view bound
and L2 could not be used together.
