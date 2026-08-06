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

> **Status.** §3–§9 are **proved in Lean**, including the delivery repair;
> §14 is the index, with every result mapped to its name and file, and §11
> steps 1–11 are all closed. §10's conjecture **C1′ is believed false** — the
> attempt, and the one-round gap it fails at, are recorded there — and what
> replaces it, **C2**, is already proved: the condition guarantees a *rate*,
> one block per round per author until exclusion and nothing after, not a
> *size*. Bounding a single reveal is a rate limit at the network layer (§12
> Q1), outside the model by construction. D8a, D15a and the failure of C1′ were
> all found by building things rather than by reasoning about them.

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
when exactly `2f+1` do. **Confirmed**: `Model.lean`'s `U3` holds twelve blocks
over rounds `0…2` against an upper bound of `4 × 3 = 12`, so the `r+1` is not
slack and the `3f+1` is not a rounding.

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

- **D8a (exposure is structural, not accidental).** A validator whose accepted
  set spans both branches of an equivocation exposes its author **in its own
  next block**, since that block's history is the union of the accepted
  histories (D3).

  D8 says the reference graph cannot *report* an equivocation, and it is easy
  to read that as making exposure a matter of luck — two branches happening to
  be referenced together. It is not. A validator accepts one block per author
  and references what it accepted, so if any two authors it accepts sit on
  different branches, the merge is performed by the validator itself as a
  matter of course. Spanning is the default, not the exception: the branches
  are spread across authors, and the acceptance rule takes one block from each.

  Confirmed on the witness (`LeanDagTest/Exposure.lean`): `Umerge`'s round-2
  blocks are exposed to validator 0 precisely because their authors accepted
  `6` and `7`, which disagree. Nothing was arranged to make that happen beyond
  building blocks normally.

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
the condition touches. What that costs is the subject of the rest of this
section, and the answer turned out to be: less than it first appears, and in a
direction that is arguably a feature.

### D15a — exclusion costs fault tolerance, one validator at a time

- **D15a.** For a block `b`, write `k` for the number of authors exposed in
  `H(b)`. Then `b`'s references must come from the other `3f+1 − k`
  validators, so the margin over the quorum is exactly `f − k`. At `k = f` the
  margin is **zero**: the exposed set is then the whole Byzantine set, the
  admissible authors are exactly `Correct`, and `b` must reference **every
  correct block of the round below**.

  Each caught equivocator costs exactly one unit of fault tolerance. It is a
  gradient, not a cliff, and the cliff edge needs the adversary to have spent
  its entire budget *and* been caught at all of it.

  Visible on the witness: `Umerge`'s round-2 blocks reference `{6,7,8}` not by
  choice but because, validator 0 being exposed, `{1,2,3}` is the only set of
  three distinct admissible authors there is.

**This is the intended behaviour, not a defect.** An author you have *proved*
Byzantine — permanently and objectively, by D12 and D13 — is not one you can
build on, so effective redundancy should fall in exact proportion to the
misbehaviour established. A system that has caught its entire fault budget is a
system with no tolerance left, and saying so is the correct report rather than
a failure of the condition. §13 S8 records why this settles the design.

### D15b — the threshold is met by the correct set alone

- **D15b.** If round `n` is populated by the correct validators, their
  round-`n` blocks form an admissible quorum for *every* block, whatever has
  been excluded: there are at least `2f+1` of them (`card_correct` plus
  `Populated`), and by D15 no correct author is ever exposed to anything.

  So exclusion can never make the quorum threshold unreachable. **The threshold
  does not change; the pool it is drawn from does**, and `|Correct| ≥ 2f+1` was
  always exactly the guarantee that the correct pool suffices on its own.

  **The `Populated` hypothesis is not decoration**, and it is what places this
  result: `card_correct` counts correct *validators*, not their blocks, so
  something must say they built. D15b is therefore the **induction step of L1
  under the condition** — round `n` populated, plus delivery, gives round `n+1`
  populated — rather than a standalone claim that building always succeeds.

### What it costs, precisely

D15b has two hypotheses: that round `n` is populated, which L1's induction
carries, and that the builder *holds* those blocks, which is
`EventuallyDelivers` — a post-`R` assumption. So:

- **After `R`: nothing.** `EventuallyDelivers` already puts every correct block
  in every correct validator's hands, which is exactly what D15b consumes. L4
  and L6 are untouched: a correct leader still commits, commits still recur.
- **Before `R`: L1 only.** The adversary controls delivery and can leave a
  validator holding a quorum of *authors* of which some are excluded. So under
  `DoSValid`, **L1 holds from `R` rather than from round 0**.
- **Safety: nothing** (D14, checked mechanically).

**And this needs no new assumption.** `DeliversQuorum` is not strengthened;
post-`R` its job is done by `EventuallyDelivers`, which the model already has.
L1 gains a `R ≤ r` restriction and nothing is invented. That question — should
`DeliversQuorum` be strengthened? — is now settled in the negative; see §13 S8.

One consequence for the repair: `Live.builds` fires on *a quorum of held
creators*, which under the condition is not enough — it must be a quorum of
**admissible** creators. At `T := Correct` that is automatic, and `liveness.md`
S5's parameterization already carries it, so the change stays small.

### Where this leaves the protocol

The chain closes:

> exclusion bites → the correct set still meets `2f+1` (D15b) → blocks keep
> being produced → after `R` a slot with a correct leader commits (L4) and
> commits recur (L6) → that commit is where a reconfiguration could be carried.

The last step is outside the model, and deliberately: there is no
reconfiguration protocol here to formalize. What the results give is that the
system stays live *under the original thresholds* long enough to reach a commit
— which is what a reconfiguration would need in order to take effect. §12 Q3
records the sequel.

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

The conjecture, in the form the target actually wants:

- **C1′.** Under `DoSValid`, for every author `X` and every round `s`, the
  number of `X`-blocks of `H(b)` at round `s` is at most `c(f)`.

  Summing gives `|H(b)| ≤ (3f+1)(r+1) + f·c(f)·(r+1)` — **linear in `r`**,
  which is the whole requirement. Linear growth is not something the condition
  could ever prevent anyway: D6 makes `(2f+1)r + 1` a *lower* bound with no
  equivocation involved. What must be prevented is **compounding** — a fixed
  number of Byzantine blocks per round per Byzantine author is tolerable; a
  number that multiplies down the levels is not.

  This is a better-shaped target than the earlier additive form
  (`(3f+1)(r+1) + g(f)`, `g` depending on `f` alone), and not merely weaker.
  D9's exponential comes from `f` multiplying *down the levels*; C1′ says
  exactly *stop the multiplication*, which is what the available tools attack.

  Four ingredients are in hand, all proved:

  1. **D11** — inflation and exposure are the same event, so the adversary
     cannot inflate silently.
  2. **D19b** — a block must be consistent about every author it references,
     so a merge of disagreeing branches can only be performed by a block that
     abstains from naming the disputed author, and abstains from then on (D12).
  3. **D18** — after `R`, disagreement about an author's round-`j` block is
     impossible once that block has reached all but `f` of the correct
     validators.
  4. **Bounded dirt** — the exposed set is Byzantine (D15) and monotone (D12),
     so at most `f` authors ever come into dispute along any chain.

### The route: intersection inside the correct set

The tool that fits C1′, and which none of the four supplies, is this. Two
blocks that both *name* `X` are both `X`-clean (D19b), and each references at
least `f+1` **correct** blocks of the round below
(`card_inter_correct_of_quorum`). A correct validator has one block per round
(T1), so sharing a correct *creator* means sharing a correct *block*. Hence:

> **The intersection lemma (to prove).** If the correct blocks available at a
> round number at most `2f+1`, then any two `X`-naming blocks of the next round
> share a correct reference `w`, and — both being `X`-clean — they **agree with
> `H(w)` about `X` at every round where `H(w)` names `X` at all**.

This is a strict strengthening of D18: same conclusion, but the hypothesis is
*some shared correct ancestor heard from `X`* rather than *`X` published to all
but `f` correct validators*.

**Its scope is a case split, and the split may be the proof.** The intersection
needs at most `2f+1` correct blocks at the round, i.e. `|byzantine| = f`.

- `|byzantine| = f` — the correct blocks number exactly `2f+1`, every pair of
  namers intersects, and disagreement is pinned wherever the backbone speaks.
- `|byzantine| < f` — namers may reference disjoint correct sets and the
  intersection fails; but D9's branching factor is the *number of Byzantine
  authors*, which has fallen by the same amount.

The adversary cannot have both, and that tension is why every attempt to
construct a counterexample has felt like it was fighting itself.

**Where it is still short.** The agreement holds only at rounds where `H(w)`
*names* `X`. Where `X` is invisible to the shared ancestor, the namers may
differ, and the count is bounded only by the layer above — which is D9's
recurrence again. Two things might close that gap, neither yet checked:

- **`U`-membership.** Every `X`-block of `H(b)` lies in `U`, so some correct
  validator *held* it. If the acceptance policy were strengthened to *accept
  some block from every author you hold a block from*, then holding would imply
  referencing, and an author invisible to the backbone at a round would have no
  block at that round in `U` at all — hence none in any history. Whether that
  survives contact with the specific shared ancestor `w`, whose author may have
  held nothing from `X`, is exactly what needs working out.
- **Induction on layers.** Turning "agreement below" into a per-layer constant
  needs an induction that the current statement does not yet supply.

**The candidate counterexample, sharpened.** `f = 2`, `n = 7`, `X` and `Y`
Byzantine, both silent toward correct validators — so no round is pinned and
no shared ancestor speaks — building a secret binary tree in which each block
names one `X`-block and one `Y`-block of the round below, revealed at round
`r`. What must be checked is whether such a tree can be **valid**: by D19b a
block naming both `X` and `Y` must be consistent about both, so its two
subtrees must agree about both, which appears to collapse that node's branching
entirely. If that is right, branching nodes must *abstain* from naming one of
the two, and take their dirt from the correct backbone instead — which is
shared, and therefore not a source of branching either. **That is the crux, and
it is where the effort should go**: either a family that survives all of it, or
the argument that none can.

### The attempt, and why it fails

The route above was tried, with two extra policies making explicit what the
model had left to prose: `HeldByCorrect` (`U` really is what correct validators
held, §4.2) and `AcceptsSome` (a validator holding a block by some author
accepts *some* block by that author). Together they give what the route needed,
and it is proved: **nothing an author publishes is invisible to the correct
population** — every block in `U` has a correct validator that accepted one of
its author's blocks for that round, and therefore referenced one.

The **backbone lemma** came out of the same attempt and is worth having
independently: after `R`, a correct block's history contains *every* correct
block of every round from `R` up to its own. The induction needs no population
hypothesis, since a correct reference always exists to step through.

**And then it stops, one round short.** A block `c` at round `s` that names an
`X`-block does contain the backbone — but only up to round `s-2`, because
`H(c)` at round `s-1` is *exactly* `c`'s references (D7). The backbone's
`X`-block for round `s-1` is referenced by correct blocks at round `s`, not at
`s-1`, so it is not in `H(c)` and cannot contradict `c`'s choice. Alternates
are therefore **born one round below their namer**, where nothing pins them,
and the number of namers per round is bounded only by the layer above. D9's
recurrence survives intact.

### What we now believe, and the honest reframing

Behind that one-round gap is something structural: **nothing in the model
limits how many blocks a Byzantine validator publishes.** `|H(b)| ≤ |U.ids|`,
and `|U.ids|` is *what correct validators held* — a bandwidth quantity the
model cannot see (§2). So a bound on `|H(b)|` in terms of `r` and `f` alone can
only come from the constraints forcing the branching to collapse, and the
analysis above says they do not.

**C1′ is therefore believed false**, though not refuted: no counterexample
family has been constructed, and §11 step 10 established that constructing one
would need theorems parameterized by depth rather than `decide`.

What replaces it is already proved, and is a **rate** guarantee rather than a
**size** one:

> **C2 — the reframed target.** For every author `X` and every block `b`, either
> `X` contributes at most one block per round to `H(b)` (D11, and D19b when `b`
> references `X`), or `X` is exposed in `H(b)` — in which case `b` does not
> reference `X`, and by D17 nothing from two rounds on does either, ever.

So an author's contribution to any history is one block per round until it is
caught, and nothing afterwards. The only unbounded quantity is what it managed
to publish *before* being caught — **one reveal per Byzantine author** (§13 S4),
`f` of them, each bounded by delivery rather than by the DAG.

That is the guarantee the condition actually provides, and it is complete. The
missing piece is not a theorem but a mechanism: bounding a single reveal is a
**rate limit at the network layer**, which §12 Q1 already identified as living
outside the model. The DoS condition and a rate limit are complementary — the
condition stops an equivocator contributing forever, the rate limit stops it
contributing much at once — and neither substitutes for the other.

### 10.5 Reopened: the exact ceiling, and the self-parent repair

The reframing above answered *rate*; it left *size* — the largest history a
single valid block can carry — unexamined. S4 prices the residual damage by
exactly that quantity, so the question was posed directly: **what is the
biggest `|H(b)|` a round-`r` block can have and stay valid under `DoSValid`?**
Working it through produced three findings, the last of which changed the
model.

**Exponential was never achievable.** D9's recurrence needs each block to name
`f` *fresh* Byzantine blocks per level, compounding downward. But a block that
names authors `X` and `Y` is clean about both over its **entire** history, so
wherever its two sub-branches both contain `X`-blocks at a round, those blocks
must coincide — named branches merge instead of multiplying. Branching in any
author can therefore occur at most **once per round**, time-staggered, never
compounding per level. The intuition that an exponential history must
somewhere hold many equivocating blocks at one round — and is therefore
exposed — is exactly right, and it is D11 read as a size statement.

**But super-linear was achievable — the laundering family.** For `f ≥ 3`,
three roles evade every proved result. A *supply* author `X` maintains many
disjoint full chains, each individually clean. A *carrier* author `Y` emits
one fresh single block per round, referencing the tip of a fresh supply chain
plus correct blocks — clean about `X` (it sees one chain) precisely because
**it carries none of its own author's past**. A *spine* author `Z` chains to
itself and names one carrier per round — clean about `Y` (one carrier per
round) and about `Z` (its own chain), and dirty about `X`, which it simply
never names. Every block is valid and `DoSValid`, and the spine's history
holds `Σ_t t ≈ r²/2` supply blocks. Stacking the pattern gives
`Θ(r^{⌊f/2⌋+1})`; at `f ≤ 2` there is no third author to play spine and the
correct backbone poisons any substitute, so the family needs `f ≥ 3`. **C1′
was therefore false in the model as it stood — constructively**, by a
pencil-and-paper family rather than the never-found `decide` witness, which is
consistent with §11 step 10's finding that no such witness could be checked.

**The family needs exactly one permission: a block that sheds its author's
past.** Real DAG protocols do not grant it — a block includes its author's
previous block. The model now does the same (**S10**): `ValidWrt` has a fourth
field,

```lean
self_parent : 0 < b.round → ∃ i ∈ b.refs, (blk i).creator = b.creator
```

— *some* block by the author, not a unique one, so an equivocator's blocks
form a forest of predecessor chains and the condition does not pretend
otherwise. Strengthening validity only shrinks the set of valid universes, so
**every theorem in the development holds verbatim**; only the witnesses needed
repair (§14).

What the field proves immediately, all in `LeanDag/SelfParent.lean`:

- **D20 (chains reach the ground).** A block's history holds a block by its
  own author at *every* round below it — contiguity, the exact thing carriers
  violated. (`exists_self_ancestor`)
- **D21 (no self-laundering).** Under `DoSValid` no block is exposed to its
  own author: it cites its self-parent, and citing an exposed author is
  forbidden. An author whose equivocation is visible in a history can never
  build on that history again — exclusion by exposure and exclusion from
  *building* become the same fact. (`not_exposedIn_self_creator`)
- **D22 (the self price).** The own-author content of a history is exactly
  `r + 1` blocks — one per round, the chain, nothing else.
  (`card_historyBlocksOf_self`, `card_filter_self_creator`)
- **D23 (the reference price).** Naming another author costs exactly `r`
  blocks: one per round strictly below, the named block's whole chain — no
  more (that would be exposure) and no fewer (D20). D19b's `≤` is now an `=`.
  (`card_historyBlocksOf_of_mem_refs`, `card_filter_creator_of_mem_refs`)
- **D24 (the floor).** Pure validity, no DoS hypothesis: a round-`r` block
  carries at least `(2f+1)·r + 1` blocks — a full disjoint chain per quorum
  author, plus itself. Histories now have a *minimum* size, so the question
  is two-sided: the floor is `Θ(f·r)`, and the target ceiling matches it.
  (`card_history_ge`)

**C1′ is conjectured true again, and the argument is the adoption collapse —
now largely proved** (`LeanDag/Adoption.lean`). The machinery:

- **Chains made countable.** `topsOf U b X` — the `X`-blocks of `H(b)` with
  no `X`-authored child there. Every `X`-block lies on the chain below some
  top (`exists_top_of_mem_history`), and a top's own history holds one
  `X`-block per round (D21 applied to the top), so an author's whole
  contribution is at most `tops × (r+1)`
  (`card_filter_creator_le_card_topsOf`). **The number of tops is the number
  of chains**, and on the witness it is exactly the equivocation made
  visible: validator 0 has two tops in `Umerge`'s merge history — its two
  geneses — where honesty gives one.
- **Unexposed means one chain**
  (`mem_history_of_creator_eq_of_not_exposedIn`): two same-author blocks of
  a history whose author is unexposed there are chain-related. D11's count
  plus D20's contiguity, in pointwise form.
- **The adoption collapse** (`top_eq_of_mem_namer_history`): two tops, one
  inside the history of a block referencing the other, coincide — a namer's
  history has room for only one `X`-chain, and a named `X`-block strictly
  below another acquires an `X`-child there, so it was no top. Hence one
  chain adopts one top, and **distinct tops need distinct namer authors**.

What this proves outright — **the main bound, unique-equivocator regime**
(`card_history_le_of_unique_equivocator`): if at most one author is exposed
in `H(b)` then

> `|H(b)| ≤ (6f+1)(r+1)` — linear in `r`,

with the exposed fiber priced at `tops × rounds ≤ 3f·(r+1)` and every other
fiber a single chain. The hypothesis is *free* at `f ≤ 1`, since exposure is
Byzantine (D15) and the Byzantine set has at most one member — so
**C1′ holds unconditionally at `f = 1`** (`card_history_le_of_f_le_one`),
and with D24 the answer to this section's question is pinned from both
sides: `(2f+1)·r + 1 ≤ |H(b)| ≤ (6f+1)(r+1)`.

**The multi-equivocator case is closed by pedigrees**
(`LeanDag/Pedigree.lean`), and with it **C1′ is proved in general**. With
several exposed authors, exposed chains can name each other's tops and the
flat per-cone count never grounds; what grounds it is *nesting*. An adopted
top lies inside its adopter's history, so iterating "who adopted the
adopter" climbs through strictly higher rounds and strictly nested cones and
must end at `b`, the only unreferenced block. Three facts turn the climb
into a count:

- **Pedigrees exist with fresh authors** (`exists_pedigree`): the adopters'
  authors, together with the top's own, are pairwise distinct — a repeat
  would put the earlier block on the repeated author's single chain
  (D21/D22) and hand it a child, unmaking the top.
- **Pedigrees determine** (`pedigree_deterministic`): each step downward is
  the unique adopted top of that author under that adopter — the adoption
  collapse again — so a top is a *function* of its pedigree's author list.
- **Author lists are few**: duplicate-free over `3f+1` validators, hence at
  most `(3f+2)^(3f+1)` of them.

So `|topsOf U b X| ≤ c(f) := (3f+2)^(3f+1)` (`card_topsOf_le_pow`), which
yields C1′ verbatim — **an author contributes at most `c(f)` blocks per
round to any history** (`card_historyBlocksOf_le`) — and the general bound

> `|H(b)| ≤ (3f+1) · c(f) · (r+1)` — linear in `r`, at every `f`
> (`card_history_le`).

**Tightened.** The raw pedigree count wastes two facts, and anchored
pedigrees (`PedigreeVia`) recover both. *An author with two chains is
exposed* — both chains reach round 0 (D20) and collide there — so at most
one top per unexposed author (`card_topsOf_le_one_of_not_exposedIn`), and
only exposed authors, at most `f` of them, can branch at all. And *a
pedigree can stop at its first unexposed-author adopter*: that adopter is
the unique top of its author, so it anchors the determination as well as `b`
does, and every intermediate author is exposed — `e - 1` choices per slot,
`e := |exposedTo U b| ≤ f`, instead of `3f + 1`. The counts become, all
proved:

- per exposed author: `|topsOf U b X| ≤ (3f+1-e)·e^(e-1)`
  (`card_topsOf_le_of_exposed`);
- per author per round: **`c(f) = 1 + 3f·f^(f-1)`**
  (`card_historyBlocksOf_le'`) — `4` at `f = 1`, `13` at `f = 2`, `82` at
  `f = 3`, where the unanchored count gave `5⁴ = 625`, `8⁷ ≈ 2·10⁶`,
  `11¹⁰ ≈ 2.6·10¹⁰`;
- in total: **`|H(b)| ≤ (3f+1 + 3f^(f+1))·(r+1)`** (`card_history_le'`) —
  at `f = 1` exactly the adoption theorem's `7(r+1)`, at `f = 2` a constant
  of `31` against a D24 floor of `5r+1`.

The residual gap to the plausible `O(f)` truth is the `f^(f-1)` factor: it
counts nested adoption among the exposed authors as if every branching order
were realisable, and whether cone-consistency across a *whole* pedigree
forbids that is the remaining quantitative question (§12) — not an open
safety one. Everything above is constant in `r`, which is all C1′ ever
demanded: no compounding, at any fault budget.

### 10.6 The floor for `c(f)`: polynomial is impossible

The question was whether aggressive use of validity — most
many-equivocation histories cannot exist because their blocks are invalid —
forces `c(f)` down to a polynomial. Working the validity constraints to
the end settles it, in both directions: they cut the count far below
`e^(e-1)`, and they **cannot** cut it below `2^(e-1)`. The plausible-`O(f)`
guess of §12 was wrong.

**The tool validity actually gives — density (D25, proved,
`LeanDag/Density.lean`).** A block's references carry `2f+1` distinct
creators, at most `β := |byzantine|` of them Byzantine; the correct
validators number exactly `3f+1-β`; so a block *misses at most `f`* of the
correct validators of the round below — independent of `β` — and missing is
monotone through any correct reference:

> **D25.** A valid block's history contains a block by all but at most `f`
> of the correct validators, at every round strictly below it.

Cones cannot be selectively blind: a block curates at most `f` misses per
round and swallows everything else, including everything those correct
blocks had swallowed. This is the constraint that "most histories with many
equivocations are invalid" cashes out to — and its budget is exactly `f`,
which is what both directions below exploit.

**The freshness constraint (what validity forbids).** When a chain adopts
tops sequentially, each adoption demands cleanliness about the adopted
author over the *whole accumulated cone* — including every previously
adopted subtree. So a chain may adopt author `a` only while no `a`-chain
sits anywhere in what it has already gathered. This kills the full
`(e-1)`-ary pedigree tree behind the `e^(e-1)` factor: a node cannot adopt
children of authors `a₁, a₂, …` in an order that ever revisits an author
already present in an earlier child's subtree. The orders that survive are
exactly "leaves first, one big subtree last", and the maximal gatherable
structure obeys `G(m) = m + Σ_{d<m} G(d)`, i.e. **`G(m) = 2^m - 1`**.

**The matching construction (why nothing stronger is true).** The `2^m`
is attainable, and the construction passes every proved constraint —
freshness, path-distinctness, D21 own-author cleanliness, quorum, density —
with the correct pool silent (consistent: at `β = f` the correct validators
reference exactly each other). The doubling pattern, with `A₄, A₁`
unexposed scaffolding and `A₂, A₃` exposed (`e = 2`):

- a chain of `A₃` adopts a fresh `A₂`-leaf — legal, its cone is `A₂`-free;
- a chain of `A₄` adopts an `A₂`-leaf, *then* the `A₃`-chain — legal: at
  the second adoption only `A₃`-cleanliness is demanded, and the `A₂`-dirt
  the `A₃`-subtree brings is harmless because nothing names `A₂` afterward;
- an anchor (`A₁`-chain, or `b`) adopts the `A₄`-chain — one clean naming
  of an unexposed author, gathering all four `A₂`-chains.

Every naming block is clean about precisely what it names at the moment it
names it; all accumulated dirt is by authors never named again. Iterating
the pattern doubles one author's chain count per additional exposed helper:
**`2^(e-2)` chains of a single author, with only `e` exposed authors**, in
`O(e)` rounds. Separately, the anchor factor is real even at `f = 1`:
two correct validators can adopt the two halves of an equivocation by
spending their D25 miss-budget on excluding each other —
`LeanDagTest/Density.lean` exhibits two chains of one author inside a
*correct* validator's history at `f = 1`, against the proved ceiling of 3.

**The doubling step is machine-checked** (`LeanDagTest/Doubling.lean`).
The obvious objection — Byzantine validators cannot forge correct blocks
and cannot advance rounds alone — is answered on concrete data. `Udouble`
runs `f = 4` over thirteen validators: the correct nine (`= 2f+1` exactly)
advance rounds referencing only each other, and every Byzantine block
references *seven real correct blocks of the immediately preceding round*,
as `predecessor` and `quorum` force — the structure parasitizes the correct
DAG; it never outruns it, and visibility is one-way until the reveal.
Validator 1 runs four chains, the exposed helper (validator 2) two, each
helper chain carrying a fresh validator-1 chain to a different scaffold.
`decide` confirms all of it: `Udouble` is valid and `DoSValid`, the crux
block names the helper while *clean* about it and lawfully exposed to
validator 1, `topsOf Udouble 41 1 = {1, 13, 14, 15}` — four chains,
`4 = 2^e` against the proved ceiling of `22` — and D25's miss-budget is
honoured throughout (the reveal misses exactly validators 11 and 12 at
round 2). The family is not a thought experiment.

**Where this leaves the bound.** The truth is exponential in the exposed
count:

> `(3f+1-e)·2^(e-1)`-ish achievable  ≤  true `c(f)`  ≤  `(3f+1-e)·e^(e-1)` proved.

Closing to `2^(e-1)` needs "top determined by (anchor, *set* of pedigree
authors)" in place of the proved ordered-list determinism; the freshness
constraint forces much of that (both orders of a two-author pedigree cannot
coexist under one anchor), but the general set-determinism claim resisted
proof and may need refinement. What is **settled** is the shape: `c(f)` is
`2^Θ(e)` — no additional assumption can be avoided to get polynomial,
because the doubling family is valid under all of them. A polynomial bound
therefore requires *changing the model*: a fetch bound (§12 Q1, now
designed as the novelty budget of §10.7), an acceptance policy that
refuses blocks whose histories contain exposures (rejected as S9 for
other reasons), or reconfiguration (Q3).

### 10.7 The novelty budget: the rate limit, designed

§10.6 ends at a fork: inside the model the truth is `2^Θ(e)`, and a
polynomial bound requires changing the model. This section records the
change we believe is right — and, as of `LeanDag/Novelty.lean`, built:
the measure and its laws, the telescope (D26), the view bound (B3) and
the liveness half (C3) are proved, each witnessed on data in
`LeanDagTest/Novelty.lean`. The slogan the whole design keeps returning
to: **legislate novelty, prove size**.

**The shape of the hidden mass.** Per block, the doubling family is
unimpeachable — rounds contiguous, quorums full, every cone clean about
what it names. What is anomalous is where the mass sits *relative to
the observer*: the excess blocks are old — most of `Udouble`'s live at
round 0 — and appear in no block any correct validator has ever held.
The reveal delivers them at once: against the correct view (the 27
correct blocks), `H(41)` carries **fifteen novel blocks**, where a
correct tip whose cone the view already holds carries exactly one. The
signature of the family is **novelty at depth**, and novelty is
relative to an observer: no intrinsic predicate on a block can see it.
That one observation sorts every candidate rule.

**Two intrinsic rules, both broken.** The rules that suggest themselves
legislate cone *shape*, and both convict correct blocks:

- *Cap the chain count* — refuse blocks whose cone holds several chains
  of one author. `Utwin` kills it at `f = 1`: blocks 5 and 6 each
  cleanly adopt one half of an equivocation, and block 8 — a correct
  validator's block — is **forced by quorum** to reference both; only
  three correct peers exist and it needs three distinct creators. Chain
  counts only grow under merges, and the merges are forced, not chosen.
  S9's ghost, now with a machine-checked witness.
- *Cap the history size* — refuse blocks with `|H| > C·(r+1)`. Same
  failure at the boundary: a correct block sitting at the cap,
  quorum-forced to merge two divergent halves, exceeds it through no
  fault of its own.

**The rule.** Each correct validator `v` maintains `V` — the union of
the histories of what it has accepted (the retained view of S1).
Novelty is `|H(t) \ V|`, measured when `t` arrives.

> `v` may use `t` as a reference only if `t`'s novelty at acceptance
> was at most `κ`. A block over budget is **deferred, never rejected**;
> among eligible candidates, prefer minimum novelty.

Two properties carry the design. *Novelty is antitone in the view*:
`|H(t) \ V|` only shrinks as `V` grows, so deferral is a rate limiter,
not a verdict — a deferred block becomes eligible the moment enough of
its cone arrives by any route, and no correct validator is ever
permanently wrong about a block. And the budget charges at the one
gate the adversary cannot route around: to enter correct cones at all,
a Byzantine block needs a correct referencer (S4's reveal), and the
referencer now pays at most `κ` of fetch for it.

**What it buys.** The acceptance rule admits at most one block per
author per round (S2): at most `f` Byzantine acceptances at `κ` each,
at most `2f+1` correct ones at `Κ` each (the larger threshold, next
paragraph), so a correct view grows by at most `(2f+1)·Κ + f·κ` blocks
per round — and through the D3 bridge the history of `v`'s own next
block obeys the same bound: **linear in `r`, quadratic in `f`** for
constant `κ`, the shape §10.6 proves unreachable inside the bare
model. The doubling family is not forbidden; it is **repriced**. A
`2^e` cone can no longer arrive in one reveal: it must trickle through
`κ`-sized acceptances, at most `f` Byzantine authors eligible per
round, so placing it takes on the order of `2^e/(f²κ)` rounds instead
of `O(e)` — exponential time to place exponential mass, while correct
histories grow linearly throughout. This composes with, and does not
replace, the DAG-side condition: exclusion makes the damage one-shot
per author (S4); the budget makes the shot small.

**The contagion attack, and hysteresis.** The liveness danger has one
shape. The adversary trickles its cone to a *single* correct `v` until
`v`'s check passes; `v` references the Byzantine block; the other
correct validators have not fetched that cone, defer `v`'s next block,
and `v` drops out of their quorums — `2f` participants remain and the
DAG stops. A single threshold serving both *what I reference* and
*what I count toward quorum* is self-poisoning. The repair is the
standard two-threshold amplification (the `f+1`/`2f+1` echo pattern):

- `κ` — what you will newly fetch to make something **your own
  reference**;
- `Κ ≥ f·κ + 3f+1` — what you will fetch to **count a peer's block
  toward quorum**: a correct peer's tip carries at most its own
  per-round budgeted Byzantine excess (`f·κ`) plus one round of normal
  production, so after `R` every correct block passes every correct
  validator's `Κ`-check, and only genuinely hidden mass is deferred.
  (The Lean development sharpened this accounting — the exact
  requirement is gap-based; see C3 below.)

Two proved facts make the repair safe rather than hopeful: the correct
set alone meets the quorum (D15b) — Byzantine blocks are never
*needed* — and D25's density is what keeps correct views overlapping
enough for the correct-to-correct gap to be one round of production
rather than an assumption.

**Timeouts.** Nothing new in kind. The round timer counts only
`Κ`-eligible blocks toward `2f+1`; a deferred block never stalls it,
and after `R` the correct tips alone satisfy it. The fetch timer pulls
unknown ancestors up to the applicable budget and defers past it;
re-checking a deferred block is event-driven and monotone, since
novelty only shrinks. Commit and leader timers are untouched — the
mechanism sits entirely below the commit rule, shaping only the
reference graph.

**Why this is expressible, despite Q1.** Q1 records that the rate
limit cannot be a validity condition and that the model has no notion
of a message. Both stand, and neither blocks the design: novelty is
`history \ view` — two objects the model already has — and the
schedule it needs already exists: `Delivery.accepted` is indexed by
round. The budget is one predicate over a `Delivery`, living exactly
where S1 put the storage story — at the acceptance layer, never in
`ValidWrt` — so validity stays objective (D13 untouched) and every
existing theorem survives verbatim. What is proved on top
(`LeanDag/Novelty.lean`) is new:

- **B3** (`card_viewUpto_le`) — under the budget a correct validator's
  view is linear in the round:
  `|V_v(n)| ≤ (3f+1) + (|Correct|·Κ + f·κ)·n`, whose increment at
  `β = f` is the `(2f+1)·Κ + f·κ` above; through the D3 bridge the
  history of `v`'s own next block obeys the same bound plus one
  (`card_history_le_of_noveltyBudget`).
- **D26, the telescope** (`card_history_le_of_stepNovelty`) — the
  pure-DAG form, no delivery model: if each block of a correct author
  adds at most `κ'` over its self-parent (`StepNovelty`), then
  `|H(b)| ≤ κ'·r + 1`, by S10's descent. Tight on `Udouble`:
  the correct chains step by exactly `2f+1 = 9` and `|H(30)| = 9·2+1`.
- **C3** — the liveness half, in two rounds of sharpening. First the
  gap form: after `R`, the novelty of a correct block at any correct
  validator is at most **one plus the view gap** toward its author
  (`card_novelty_le_viewGap_add_one`), and the gap grows by at most
  `f·κ` per round (`card_viewGap_le`) — the adversary's hidden mass
  appears in neither term, which already kills the contagion attack.
  Then the drift died too: **the gap collapses** (C3′,
  `card_viewGap_succ_le_of_block`). The repair this section first
  thought it had to design already exists inside `Delivery`:
  `includes` puts every round's acceptances among the next block's
  references, and the self-parent chain (S10) carries every earlier
  round forward — so a correct validator's block is, in its cone, a
  **complete record of everything its author ever accepted**
  (`viewUpto_subset_history`). One such block delivered post-`R`
  erases the whole standing gap; what remains is one round of
  Byzantine budget: `gap ≤ f·κ`, constant. Hence **C3″**
  (`card_novelty_le_of_byzBudget`): a validator enforcing only the
  Byzantine clause (`ByzBudget`, the rule it can actually run) never
  meets a correct block costing more than `Κ = f·κ + 1` — the correct
  clause of the budget is **derived, not assumed**, with a better
  constant than the designed `f·κ + 3f+1`. (The one hypothesis beyond
  `Delivery`: `RefsAccepted`, `refs ⊆ accepted` — the converse of
  `includes`, D3's ordinary case.)
- **The capstone** (`no_stall_and_card_viewUpto_le`). One set of
  hypotheses — `Live`, `DeliversQuorum`, `EventuallyDelivers`,
  `ByzBudget κ`, `RefsAccepted` — yields liveness and storage
  **simultaneously**: no correct validator ever stalls, and after `R`
  no correct view grows faster than `|Correct|·(f·κ+1) + f·κ` per
  round (B3′, `card_viewUpto_le_of_byzBudget`). The two conclusions do
  not compete: liveness never needs a Byzantine block (D15b, and the
  post-`R` quorum is derivable from the correct set alone), and by C3″
  the enforced rule never defers a correct one.
- **B4 — and then the base falls too** (`card_viewUpto_le_of_refsAccepted`,
  capstone form `no_stall_and_card_viewUpto_le'`). The pre-`R` view the
  capstone measured from is itself linear, for a reason needing **no
  synchrony at all**: every Byzantine block in any correct view entered
  through *some* correct validator's budgeted acceptance — a direct
  acceptance is priced `≤ κ`, and a block arriving inside a correct
  block's cone was already in that block's author's earlier view
  (`RefsAccepted`), hence already in the pool. So the global Byzantine
  pool (`byzPool`, `card_byzPool_le`) grows by at most `|Correct|·f·κ`
  per round from round 0, the correct part counts itself at one block
  per author per round (`no_equivocation`), and
  `|V_v(n)| ≤ |Correct|·(n+1) + |Correct|·f·(1 + n·κ)` holds under full
  asynchrony — `EventuallyDelivers` appears nowhere. DoS resistance is
  not a post-GST property.

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
  exponential does not exist at `f = 1`, so C1′ is trivially true there and any
  counterexample search over `Fin 4` is wasted effort.
- `Live` and `DoSValid` must be shown **jointly** satisfiable at every horizon,
  or §8 is vacuous — and this now requires the repaired `Delivery`, so
  `ugrowDelivery` has to be rebuilt around an accepted set rather than around
  *every* round-`n` block.

Suggested order, easiest first:

1. ~~`history` as a `Finset` (§13 S6), `ExposedIn`, D11, D12, D13.~~ **Done**
   (`LeanDag/History.lean`, `LeanDag/Exposure.lean`). The `f = 1` biting
   witness came with it rather than at step 5: it was ~50 lines, and the
   contrast between `U6` (an equivocation nobody built on, so nothing exposed)
   and `Umerge` (the branches merged, so exposure and exclusion) turned out to
   be the clearest way to exhibit D8 and D8a at once.
2. ~~`View.ofAccepted`, D1–D4 — the bridge.~~ **Done**
   (`LeanDag/Acceptance.lean`). On the witness the D2 bound reads 11 ≤ 36: the
   accepted histories overlap almost entirely, since the round-2 blocks share
   their round-1 references. That slack is the correct backbone of §10's
   candidate proof A, showing up as a number.
3. ~~D5, D6, D19a, D19b — counting.~~ **Done** (`LeanDag/Counting.lean`). The
   design point below was the right call: `card_le_of_equivFree` is proved once
   over an arbitrary `Finset` and instantiated at a view (D5) and at a history
   (D19a), and on `Umerge` those sets genuinely disagree. Both bounds turn out
   to be **attained** on the witnesses — `U3` meets D5 exactly, and validator 1
   meets D19b exactly with three blocks in `H(9)`, one per round.

   **A design point discovered at step 2.** "No equivocation" is a property of
   a *set of blocks*, and the set differs by result: D5 wants it of `V.ids`,
   D19a of `H(b)`. These do not coincide — a view generated by an accepted set
   can hold both halves of an equivocation with *neither accepted block*
   exposed, which is precisely D8a seen from below. So the counting lemma
   should be proved once for an arbitrary `Finset BlockId` on which `creator`
   is injective per round, and applied twice, rather than stated for views and
   re-proved for histories.
4. ~~D14 — free, by construction of §6.~~ **Done**
   (`LeanDagTest/SafetyUnderDoS.lean`). Being free, the claim is also easy to
   make hollow, so it is pinned down rather than asserted: T1, T2, T3, M3, M5′,
   M6 and L2 are each restated with `DoSValid U` in scope and discharged by the
   *existing* theorem, hypothesis unused. If the condition ever migrated into
   `ValidWrt`, or a safety result grew a dependency on it, those stop
   elaborating. It says nothing about whether the hypotheses stay satisfiable.
5. ~~D7, D8.~~ **Done** (`LeanDag/Exposure.lean`; the witness landed at step 1).
   D8 needed two facts about the top of a history — nothing sits at a block's
   own round but the block, and the layer one below is *exactly* the reference
   set — and then falls out: an equivocation pair is at least two rounds down,
   because the top layer holds only `b` and the next holds only `b`'s
   references, whose authors are distinct.
6. ~~The exclusion results, and the delivery repair.~~ **Done**
   (`LeanDag/Exclusion.lean`, `LeanDagTest/Exclusion.lean`, and the edit to
   `LeanDag/Liveness.lean`). Recorded as originally planned:
   - **6a** — D15, D15a and D15b, plus the `Uexcl` witness. All additive:
     nothing here edits an existing file.
     - **D15** (`ExposedIn U b X → X ∉ Correct`) is five lines off T1, and
       everything else rests on it.
     - **D15a** in its gradient form: the admissible authors number `3f+1 − k`,
       so the margin is `f − k`, and at `k = f` a block's references are
       exactly `Correct`.
     - **D15b**: given `Populated U n`, the correct round-`n` blocks are an
       admissible quorum for every block. Needs `card_correct` and
       `correctBlocksAt`, the latter from `CommonCore` — which `Counting` does
       not currently import, so this is also the first result to need that edge
       in the import graph.
     - **`Uexcl N`** — the witness that closes §8's chain end to end: validator
       0 equivocates at round 0, the branches merge at round 2, it is excluded
       from then on, and validators 1–3 keep building on one another to any
       horizon, with `DoSValid` throughout and **L4 firing after the exclusion
       has taken hold**. At `f = 1`, `n = 4` this is the tightest possible case
       — `|Correct| = 3 = 2f+1` exactly, so the DAG runs at zero margin from
       round 2 and still commits.

       One wrinkle found in review: `Live` needs a `Delivery`, and the
       unrepaired `Delivery.includes` is unsatisfiable when a correct validator
       *holds* both halves (§8). `Uexcl` can dodge this by setting `held` to
       the correct blocks alone — legal, and enough to make the witness go
       through before 6b — but that `held` is not what a real validator holds,
       since it does receive the Byzantine blocks. So 6a's witness is honest
       about the DAG and artificial about delivery; **6b is what makes the
       delivery side honest too**, and the witness should be revisited then.
   - **6b** — the repaired `Delivery`, and where the quorum comes from.

     **The repair was smaller than feared.** `Delivery` gained four fields
     (`accepted`, `accepted_sub`, `accepted_inj`, `accepts_correct`) and
     `includes` now references what was *accepted*; `DeliversQuorum` and
     `Live.builds` moved from `held` to `accepted`. **No proof in `Liveness`,
     `Timing` or `Quantitative` needed changing** — only the two `Delivery`
     witnesses, which set `accepted := held` and discharge `accepted_inj` from
     `Ugrow`'s one-block-per-validator-per-round structure. L7 is the single
     place the shape of the argument changed, and `accepts_correct` is exactly
     what it needed.

     **One design point came out differently from S5.** The exposure
     subtraction is *not* in `includes`: `Delivery` mentions the DoS vocabulary
     nowhere, so `Liveness` needs no import from `Exposure` and stays
     regime-neutral. The condition enters instead as a **policy on a delivery**
     (`DoSAccepting`), stated in `Exclusion.lean` where it belongs. That is
     better than what S5 proposed and the reason is recorded there.

     **And `DeliversQuorum` turned out to be derivable after `R`**
     (`card_creators_accepted_of_eventuallyDelivers`): `EventuallyDelivers`
     delivers the correct blocks, `accepts_correct` accepts them, and a
     populated round supplies `2f+1`. So the plan's Q1 is settled in Lean and
     not merely on paper — the quorum is a consequence from `R` on, and its
     unavailability before `R` is precisely the cost.
7. ~~**D16, D17, D18 — exclusion after `R`** (§9).~~ **Done**
   (`LeanDag/Exclusion.lean`). Everything they needed was already
   proved: `SynchronisedOn` and the repaired `Delivery`, D12 (permanence), D15
   (soundness), and `card_inter_correct_of_quorum` for the `f+1`-correct-
   references step. D17 is the one needing care, since it quantifies over
   Byzantine blocks too — that is what makes exclusion *total* rather than a
   convention among the well-behaved. All three are conditional on the rounds
   being populated, and hold vacuously otherwise.

8. ~~**D8a — exposure is structural.**~~ **Done**. One correction the
   formalization forced: the two accepted blocks span the branches through
   their *histories*, and have **different authors** — `accepted_inj` forbids
   accepting both halves directly, so the equivocation is never in the accepted
   set itself. Stated the other way the result would have been vacuous.

9. ~~**The intersection lemma** (§10).~~ **Done**, in two pieces —
   `exists_shared_correct_ref` and `eq_of_both_name_of_shared`. It was quorum intersection taken **inside**
   the correct set, plus D19b for cleanliness and T1 to turn a shared creator
   into a shared block. It has a payoff independent of C1′ — it strengthens D18
   by replacing *published to all but `f`* with *some shared ancestor heard from
   `X`*.

10. ~~**The `f = 2`, `n = 7` model.**~~ **Done** (`LeanDagTest/TwoFaults.lean`).
    `Ufault` has both Byzantine validators equivocating at round 0 and both
    exposed together at the merge, so the fault budget is fully spent and
    caught and D15a bites at the bound.

    **And it answered the cost question, in the unwelcome direction.** The
    model settles by `decide` in about 17 seconds — but `DoSValid` **exceeded
    the default recursion depth** and needed `maxRecDepth 8000`, at 24 blocks
    over `Fin 7` with histories of at most 15. Since a C1′ counterexample is by
    definition a history that grows exponentially, and `ExposedIn` is quadratic
    in that quantity while `DoSValid` runs it per block and reference, the
    checking cost grows as roughly the *fourth power* of what is being
    exhibited — from a starting point already over budget. **Step 11 should not
    plan to `decide` its way to a refutation**: a counterexample family will
    need its validity and its `DoSValid` proved as theorems parameterized by
    depth, in the manner of `Ugrow` rather than of `Umerge`.

11. **C1′ — attempted, and it does not close.** The `AcceptsSome` route was
    tried; it yields the backbone lemma and `exists_accepted_of_mem_ids`, both
    kept, and then stops one round short (§10). C1′ is now believed false, and
    **C2** — the rate guarantee it is replaced by — is already proved. What
    remains is not a theorem but a mechanism, and it lives outside the model:
    see §12 Q1.

Steps 1–10 are **done**, and step 11 is closed with a negative answer and a
reframing rather than a proof.

## 12. Open questions

**Q1 — The rate limit, now the live question.** §10 concludes that C1′ is
believed false and that what the condition guarantees is a *rate* (C2), not a
*size*. Bounding a single reveal is therefore the remaining work, and it is a
**rate limit at the network layer** — how many blocks per author per round a
correct validator will hold at all. That is not a validity condition and cannot
be one: it is about what you accept from the wire, not about what makes a block
well-formed, and the model has no notion of a message (§2).

The two alternatives that stay inside the model were considered and are worse:
excluding an author on *first exposure anywhere in the view* rather than in the
history breaks D13 — validity would become view-dependent, and blocks would no
longer be objectively well-formed; and requiring histories to be
equivocation-free outright is **fatal**, since by D8a every correct block
acquires an equivocation in its history and the DAG stops (§13 S9).

So the rate limit is not a fallback but the intended division of labour. The
DoS condition stops an equivocator contributing *forever*; a rate limit stops
it contributing *much at once*. Neither substitutes for the other, and only the
first is a property of the DAG.

*Status:* **designed and built.** The rate limit is the **novelty budget**
of §10.7, and the observation that unblocked it is that no message type is
needed after all: novelty is `history \ view`, both existing objects, and
the schedule it wants is `Delivery.accepted`, already indexed by round.
`LeanDag/Novelty.lean` proves the staged statements — B3, the telescope
(D26), C3 — and then more: the gap **collapses** (C3′ — the DAG is its own
repair channel, no cone-sharing protocol needed), the hysteresis threshold
is the derived constant `f·κ + 1` (C3″), and the capstone
`no_stall_and_card_viewUpto_le` yields liveness and linear storage from
one set of hypotheses — and B4 removes even the synchrony: storage is
linear from round 0 under full asynchrony
(`no_stall_and_card_viewUpto_le'`). What remains of Q1 is exactly one
thing: the wire-level cap on `held`, which the model deliberately does
not see.

**Q2 — Where does it live?** Settled for what is built, open for the rest.
`LeanDag/History.lean` (the `Finset` history) and `LeanDag/Exposure.lean`
(`ExposedIn`, `DoSValid`, D11–D13) sit directly above `CausalHistory`;
`LeanDag/Acceptance.lean` (§3) needs only those and `View`. The counting
results need L0 and so must sit above `Liveness` — which is the one remaining
placement decision, and it means the file holding D5, D6 and D19a/b cannot be
the file holding D11–D13.

**Q3 — Reconfiguration, the sequel.** Once `k` validators are objectively and
permanently excluded, the system runs as a `(3f+1−k)`-validator committee while
still using quorums sized for `f` faults — tolerating `f−k` but paying for `f`
(D15a). The principled response is to shrink the committee and recompute `f`,
which restores the margin.

The model cannot say this: `Faults` fixes `3f+1` and `f` globally, and
`ValidWrt.quorum` hard-codes `2f+1`. Nor should it yet — there is no
reconfiguration protocol here to formalize. What §8 establishes is the
precondition for one: the system stays live under the *original* thresholds
long enough to reach a commit, and a commit is what a reconfiguration would
need to take effect. Formalizing the handover is a separate piece of work, and
it would want `Faults` parameterized by a committee rather than fixed.

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
fate of C1′, D16–D18 give the shape of the guarantee: after `R`, an equivocating
validator is either invisible to the correct population — inflating nothing
they hold — or exposed, and then excluded from the whole universe within two
rounds (D17).

What that leaves is **one reveal per Byzantine author**. An author may build a
history out of sight, at any rounds it likes, and reveal it by getting a single
block accepted. Accepting that block pulls in the whole history, exposes the
author, and is the last block ever accepted from it — but the storage has
already been spent. So the residual damage is bounded by

> `f` × (the largest history a single valid block can have)

and bounding the second factor is precisely **C1′**. This is why C1′ cannot be
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

**Confirmed in practice.** `history Umerge 9`, `DoSValid Umerge` and
`∀ b ∈ ids, ∀ X, ExposedIn Umerge b X → X = 0` all settle by `decide` on the
step-1 witness. One friction cost worth knowing: peeling a single layer off a
history is not `rfl`, because the recursion hands out `round b` steps while
each reference wants `round + 1` of its own. `mem_history_succ_iff` reconciles
them once, and the layer arguments of §5 and §10 should go through it rather
than unfolding `historyUpto` by hand.

**S7 — `Delivery` requires self-reference.** D4 needs a correct validator's
block to reference its own previous block. DAG protocols do this anyway, it is
one field, and without it generated views are not monotone, so the view bound
and L2 could not be used together.

**S8 — Exclusion is by author, and the cost is the point.** The condition
excludes an *author* exposed in a block's history, and D15a's consequence —
each caught equivocator costs one unit of fault tolerance, until at `k = f` a
block must reference every correct block — is **accepted as intended
behaviour** rather than engineered around.

The reasoning:

- An author proved Byzantine, permanently and objectively (D12, D13), is not
  one anybody should build on. Redundancy falling in proportion to established
  misbehaviour is the correct report, not a malfunction.
- **Liveness under the original thresholds survives** (D15b): the correct set
  alone always meets `2f+1`, so exclusion can never make the quorum
  unreachable. What the adversary can do is force the *pool* down to exactly
  the correct set — which is what `|Correct| ≥ 2f+1` was always for.
- The cost is confined to **L1 before `R`**, and it needs no new assumption to
  absorb: after `R`, `EventuallyDelivers` supplies D15b's hypothesis, so L1
  simply holds from `R` instead of from round 0. `DeliversQuorum` is left
  alone.
- Commits are post-`R` anyway, so the guarantee that matters — stay live long
  enough to commit — is untouched. The residual discomfort is not about the
  condition but about the *committee* not shrinking to match, which is Q3 and
  is out of scope until there is a reconfiguration protocol to formalize.

`liveness.md` Q6 asks whether L1 should hold from round 0 or only after `R`, for
reasons unconnected to any of this. Under the condition the answer is forced —
only after `R` — so the two questions now have one answer.

**S9 — The forward-looking variants, rejected.** Excluding *lies* rather than
*liars* was the obvious way to keep the margin. Two readings, both rejected,
recorded so they are not revisited from scratch:

- *"A block may not reference a block whose history exposes anyone."*
  **Fatal, and D8a proves it.** Every correct validator's accepted set normally
  spans both branches of an equivocation, so its next block's history exposes
  the author — and every correct block becomes unreferenceable. The DAG stops.
  This is also why §12 Q1's "equivocation-free histories" candidate is not a
  fallback.
- *"A block may not reference `i` when a twin of `i` — same author, same round
  — is in the referencing block's history."* Survivable, and it does keep the
  margin, but it **loses D12 and D17**: exclusion is no longer permanent or
  total, only per-round, so §9 collapses. In storage terms it turns S4's *one
  reveal per author* into *one reveal per author per round*, costing a factor
  of `r`. Trading the whole post-`R` exclusion story for a margin that D15b
  shows is not needed is a bad exchange.

**S10 — The self-parent condition.** `ValidWrt` requires every non-genesis
block to reference *some* block by its own creator (§10.5). Adopted because
the laundering family — the constructive refutation of C1′ in the weaker
model — runs entirely on blocks that shed their author's past, which real
DAG protocols already forbid; the model was more permissive than the thing it
models. Three consequences of how it is stated:

- *"Some", not "the".* An equivocator's blocks form a forest of predecessor
  chains. Forcing uniqueness would be a non-equivocation assumption in
  disguise, and is not needed: every collapse argument runs on the namer's
  cleanliness, not the equivocator's honesty.
- It is a **strengthening**, so every existing theorem holds verbatim; only
  witnesses needed repair. The repair also surfaced a small semantic shift:
  an author now always votes for its own block, so `supporters` is never
  empty — a directly-skipped block has its author's self-vote and nothing
  else, which changes three counted examples and no theorem.
- S7 (`Delivery` self-reference, for correct validators) is subsumed for
  validity purposes: what S7 asked of correct behaviour, S10 now demands of
  every valid block. S7 keeps its role on the delivery side.

**S11 — The novelty budget lives at the acceptance layer, and `Κ` is a
theorem.** §10.7, built in `LeanDag/Novelty.lean`. Three decisions, made
together:

- The rule is **observer-relative** — `novelty U V b := history U b \ V` —
  because the doubling family has no intrinsic signature: rules on cone
  shape convict correct blocks under forced merges (`Utwin`, §10.7), while
  novelty charges only delivery work, and charges it once.
- It is a **predicate over `Delivery`** (`NoveltyBudget`), not a new
  structure and not a validity condition: `Delivery.accepted` already
  carries the round-indexed schedule, validity stays objective (D13), and
  every existing theorem survives verbatim — the S5 precedent.
- **Deferral, never rejection**, because novelty is antitone in the view
  (`novelty_anti`): a deferred block only gets cheaper, so the rule is a
  rate limiter that cannot become a permanently wrong verdict. And the
  hysteresis threshold `Κ` for counting peers' blocks is not a parameter
  to guess but a theorem to cite — C3″ derives it outright: `Κ = f·κ + 1`,
  **constant**, from the enforceable Byzantine clause alone, because a
  correct block's cone is a complete record of its author's acceptances
  (`viewUpto_subset_history`) and so collapses the gap on delivery.

One modelling hypothesis appears on the C3 side only: `RefsAccepted` —
`refs ⊆ accepted`, the converse of `includes`, D3's ordinary case: a
correct validator references only what it accepted. It becomes a candidate
`Delivery` field if it earns more use.

## 14. What is proved

Every result of §3–§7, with its Lean name. `History`, `Exposure`, `Acceptance`,
`Counting` and `SelfParent` are `LeanDag/`; the witnesses are `LeanDagTest/`.
The whole development builds with no `sorry` and the usual three axioms.

### Proved

| | | | |
|---|---|---|---|
| **D1** | a generated view is a view | `View.ofAccepted` | `Acceptance` |
| **D2** | the bridge, `\|V\| ≤ (3f+1)·max\|H(b)\|` | `View.card_ofAccepted_le` | `Acceptance` |
| **D3** | the sharp form, `\|V\| + 1 = \|H(b)\|` | `View.card_ofAccepted_add_one` | `Acceptance` |
| **D4** | generated views grow | `View.ofAccepted_subset`, `…_of_refs`, `…_mono` | `Acceptance` |
| **D5** | no equivocation: `\|V\| ≤ (3f+1)(r+1)` | `View.card_le_of_equivFree` | `Counting` |
| **D6** | the lower bound, `(2f+1)r + 1 ≤ \|U.ids\|` | `card_ids_ge_of_round` | `Counting` |
| **D7** | a block's references carry distinct authors | `eq_of_mem_refs_of_creator_eq` | `Exposure` |
| **D8** | an equivocation is visible only two rounds up | `round_add_two_le_of_equivPair` | `Exposure` |
| **D11** | inflation *is* exposure | `not_exposedIn_iff_card_le_one`, `card_le_one_or_not_mem_refs` | `Exposure` |
| **D12** | exposure is permanent | `ExposedIn.mono`, `ExposedIn.of_mem_refs` | `Exposure` |
| **D13** | exposure is view-independent | `exposedIn_iff_of_view` | `Exposure` |
| **D14** | safety is untouched | *(inert-hypothesis checks)* | `LeanDagTest/SafetyUnderDoS` |
| **D19a** | a clean history is linear | `card_history_le_of_not_exposed` | `Counting` |
| **D19b** | a block is clean about what it references | `card_filter_creator_le_of_mem_refs` | `Counting` |
| **D8a** | exposure is structural, not accidental | `exposedIn_of_accepted_span` | `Exclusion` |
| **D16** | after `R`, agree or be exposed | `exposedIn_of_correct_disagree` | `Exclusion` |
| **D17** | exclusion is total and permanent | `exposedIn_of_correct_exposed`, `not_mem_creators_refs_of_correct_exposed` | `Exclusion` |
| **D18** | pinning | `mem_history_of_pinned` | `Exclusion` |
| — | the intersection lemma (§10's route) | `exists_shared_correct_ref`, `eq_of_both_name_of_shared` | `Exclusion` |
| — | the backbone lemma | `mem_history_of_correct` | `Exclusion` |
| — | nothing published is invisible to the correct | `exists_accepted_of_mem_ids` | `Exclusion` |
| **C2** | the rate guarantee, which replaces C1′ | D11 + D19b + D17, already proved | — |
| **D15** | exclusion is sound | `ExposedIn.not_correct` | `Exposure` |
| **D15a** | the margin is `f − k`, and zero at the bound | `card_creators_refs_add_card_exposedTo_le`, `creators_refs_eq_correct` | `Exposure` |
| **D15b** | the correct set alone meets the threshold | `correctBlocksAt_admissible_quorum` | `Exclusion` |
| — | the condition is implementable | `not_exposedIn_refs_of_policy` | `Exclusion` |
| — | the quorum is derivable after `R` | `card_creators_accepted_of_eventuallyDelivers` | `Exclusion` |
| **D20** | chains reach the ground | `exists_self_ancestor` | `SelfParent` |
| **D21** | no self-laundering | `not_exposedIn_self_creator` | `SelfParent` |
| **D22** | the self price: exactly `r + 1` | `card_historyBlocksOf_self`, `card_filter_self_creator` | `SelfParent` |
| **D23** | the reference price: exactly `r` | `card_historyBlocksOf_of_mem_refs`, `card_filter_creator_of_mem_refs` | `SelfParent` |
| **D24** | the floor: `(2f+1)·r + 1 ≤ \|H(b)\|` | `card_history_ge` | `SelfParent` |
| — | unexposed means one chain | `mem_history_of_creator_eq_of_not_exposedIn` | `Adoption` |
| — | tops: chains made countable | `topsOf`, `exists_top_of_mem_history`, `card_filter_creator_le_card_topsOf` | `Adoption` |
| — | the adoption collapse | `top_eq_of_mem_namer_history`, `card_topsOf_le` | `Adoption` |
| **B1** | the main bound, unique-equivocator: `\|H(b)\| ≤ (6f+1)(r+1)` | `card_history_le_of_unique_equivocator`, `…_of_card_exposedTo_le_one` | `Adoption` |
| **C1′ (f ≤ 1)** | unconditional linearity at one fault | `card_history_le_of_f_le_one` | `Adoption` |
| — | pedigrees exist, authors all fresh | `exists_pedigree`, `pedigree_spec` | `Pedigree` |
| — | pedigrees determine their top | `pedigree_deterministic` | `Pedigree` |
| — | the general top count: `≤ (3f+2)^(3f+1)` | `card_topsOf_le_pow` | `Pedigree` |
| **C1′** | per-author per-round `≤ c(f)`, every `f` | `card_historyBlocksOf_le` | `Pedigree` |
| **B2** | the general bound: `\|H(b)\| ≤ (3f+1)·c(f)·(r+1)` | `card_history_le` | `Pedigree` |
| — | branching proves equivocation: unexposed = one chain | `card_topsOf_le_one_of_not_exposedIn` | `Pedigree` |
| — | anchored pedigrees | `PedigreeVia`, `exists_pedigreeVia`, `pedigreeVia_deterministic` | `Pedigree` |
| — | the sharp top count: `(3f+1-e)·e^(e-1)` | `card_topsOf_le_of_exposed` | `Pedigree` |
| **C1′ sharp** | per-author per-round `≤ 1 + 3f·f^(f-1)` | `card_historyBlocksOf_le'` | `Pedigree` |
| **B2 sharp** | `\|H(b)\| ≤ (3f+1 + 3f^(f+1))·(r+1)` | `card_history_le'` | `Pedigree` |
| **D25** | density: all but `f` correct per round appear | `card_missingAt_le` | `Density` |
| — | novelty: the measure, antitone in the view | `novelty`, `novelty_anti`, `card_history_le_card_add` | `Novelty` |
| **D26** | the telescope: stepwise novelty ⇒ linear history | `StepNovelty`, `card_history_le_of_stepNovelty` | `Novelty` |
| **B3** | the view bound under the budget | `NoveltyBudget`, `card_viewUpto_le`, `card_history_le_of_noveltyBudget` | `Novelty` |
| **C3** | post-`R` cost of a correct block: gap, plus spend | `card_novelty_le_viewGap_add_one`, `card_viewGap_le`, `card_novelty_correct_le` | `Novelty` |
| **C3′** | the gap collapses: `≤ f·κ`, constant after `R` | `viewUpto_subset_history`, `card_viewGap_succ_le_of_block` | `Novelty` |
| **C3″** | the correct clause is derived: `Κ = f·κ + 1` | `ByzBudget`, `card_novelty_le_of_byzBudget` | `Novelty` |
| **B3′** | linear storage from the enforceable rule alone | `RefsAccepted`, `card_viewUpto_le_of_byzBudget` | `Novelty` |
| — | the capstone: liveness ∧ storage, one hypothesis set | `no_stall_and_card_viewUpto_le` | `Novelty` |
| **B4** | unconditional linear storage: no synchrony, from round 0 | `byzPool`, `card_byzPool_le`, `card_viewUpto_le_of_refsAccepted` | `Novelty` |
| — | the capstone, asynchronous | `no_stall_and_card_viewUpto_le'` | `Novelty` |

Supporting definitions: `history` and `mem_history_iff` (S6, `History`);
`ExposedIn`, `DoSValid`, `EquivPair` (`Exposure`); `Accepted` (`Acceptance`);
`EquivFree`, `atRound`, `card_le_of_equivFree` (`Counting`). All four
predicates are decidable, so the witnesses settle by `decide`.

### Witnessed

**`Uexcl`** (`LeanDagTest/Exclusion`) closes §8's chain end to end: validator 0
equivocates, is exposed at the merge from round 2, and the three correct
validators — `2f+1` exactly, so zero margin — carry the DAG on alone and
**still commit**, at a slot whose three rounds lie entirely after the
exclusion. D15a is applied there rather than assumed: the references of every
block from round 3 on are exactly `Correct`, by theorem.

`Umerge` (`LeanDagTest/Exposure`) is the `f = 1` model the plan asked for, and
it is non-vacuous in the way that matters: validator 0 equivocates, is exposed
at the merge, and is thereby debarred from being referenced — while retaining a
perfectly valid block that no later block may name. `U6` is its foil, an
equivocation nobody built on and therefore never exposed. `U3` pins D5 as
tight.

**`LeanDagTest/SelfParent`** reads D20–D24 off `Umerge` and `Uexcl`: validator
1's chain `12 → 9 → 6 → 1` is exactly one block per round (D22, totalled to
`4 = r + 1`); referencing validator 2's block costs its chain `10 → 7 → 2`,
exactly `3 = r` blocks (D23); the histories meet the floor with room — `12`
blocks against a floor of `10`, and `18` against `16` on the six-round
`Uexcl` — with the counts confirmed twice, once by theorem and once by
`decide` on the raw data.

**`LeanDagTest/Adoption`** counts the chains: in `H(12)` of `Umerge` the
equivocator has exactly **two tops** — its two geneses, `topsOf = {0, 4}` —
against one for every honest author, within `card_topsOf_le`'s ceiling of
`3f`. B1 then bounds the same dirty history end to end (`12 ≤ 28`), and on
`Uexcl` floor and ceiling hold together: `16 ≤ 18 ≤ 42` at round 5.

**`LeanDagTest/Pedigree`** takes the case B1 cannot: `Ufault` at `f = 2`,
where **both** Byzantine validators are exposed at once
(`exposedTo = {0, 1}`, each with two chains). C1′ and B2 apply with no
hypothesis beyond `DoSValid`, bounding the 20-block history and every
per-round contribution — the multi-equivocator regime, witnessed.

**`LeanDagTest/Novelty.lean`** prices the doubling family and runs the
budget on a real schedule. Against the correct bystander's 27 blocks the
reveal costs **15 novel blocks** where a correct tip costs 1 — every
`κ ∈ [1, 14]` defers the reveal and never a correct block — and absorbing
branch N drops the price to 8: antitone, on data. The telescope is tight
on `Udouble` (`|H(30)| = 19 = 9·2 + 1`) and its constant is the data's,
not slack: `StepNovelty Utwin 4` is *false*, the forced merge costs
exactly 5. `Dtwin` equips `Utwin` with its delivery story and satisfies
`NoveltyBudget Dtwin 0 3` — the dearest acceptance charges validator 1
for the missed genesis *and* the equivocation half riding in on a correct
carrier, the pre-`R` divergence priced inside `Κ` — B3 and the whole C3
chain then apply with `R = 1`, and the round-0 gap between validators 3
and 1 is exactly `{0}`, the Byzantine half one accepted and the other
never saw: the gap *is* the budget's spend, on data. The collapse and the
capstone run on the same schedule: `Dtwin` carries `Live`,
`DeliversQuorum` and `RefsAccepted` instances, C3′ applied through
validator 3's own round-1 block gives gap `≤ f·κ = 0`, C3″ prices the
merge block at exactly the derived threshold `f·κ + 1 = 1`, and
`no_stall_and_card_viewUpto_le` — liveness and the storage bound in a
single application — closes it. B4 on the same data: the global pool is
exactly the two accepted equivocation halves, `byzPool Dtwin = {0, 4}`,
frozen there forever at `κ = 0`, and the asynchronous capstone
`no_stall_and_card_viewUpto_le'` applies with `EventuallyDelivers`
nowhere in sight.

The S10 repair itself touched only `Model.lean`:
validator 3's blocks (and dependents) gained their self-parents, and three
vote-count examples shifted because an author now always votes for its own
block. `Umerge`, `Uexcl`, `Ufault` already satisfied the condition untouched,
and `Ugrow` proves it with one new clause.

### Not yet proved

Nothing. **C1′ is proved in full and tightened**
(`card_historyBlocksOf_le'`, `card_history_le'`): it was false in the
pre-S10 model — §10.5 constructs the laundering family — and under S10 it
holds at every fault budget: per author per round `≤ 1 + 3f·f^(f-1)`, in
total `|H(b)| ≤ (3f+1 + 3f^(f+1))·(r+1)`, which at `f = 1` is exactly the
adoption theorem's `7(r+1)`. What remains open is *quantitative only*, and
§10.6 settles its shape: the truth is `2^Θ(e)` — the doubling family shows
polynomial is **impossible** without changing the model, and the remaining
gap is `2^(e-1)` (constructible) versus `e^(e-1)` (proved), whose closure
needs set-determinism of pedigrees. Beyond that: Q1's network-layer rate
limit, which bounds what no DAG condition can — the size of `U` itself —
is now designed (§10.7) **and formalized to the end** (B3, D26, C3, C3′,
C3″, B3′, B4 and both capstones in `LeanDag/Novelty.lean`): a constant
hysteresis threshold is *derived* (`f·κ + 1`), no repair protocol is
needed, and B4 closes the pre-`R` conjecture — storage is linear from
round 0 under full asynchrony. What remains is exactly one edge term: the
wire-level cap on `held` — how many *candidate* blocks a validator will
hold from the network before deciding anything — which the model
deliberately does not see (S5: `held` must stay undeduplicated so that
`U` means what §4.2 says). That is a statement about messages, not
blocks, and it is the one part of Q1 that was always going to live at the
network layer.

The gap C1′ has to close is visible on the witness rather than merely stated:
validator 1, which block `9` references, contributes three blocks to `H(9)` —
one per round, the D19b bound exactly. Validator 0, which `9` does *not*
reference, contributes two blocks **at a single round**. Same history, same
count, and only one of them is bounded as the DAG grows.
