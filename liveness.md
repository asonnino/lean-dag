# lean-dag — Liveness

Design notes for the liveness results. Separate from `spec.md` because the
approach is exploratory and because liveness needs modelling primitives the
static development deliberately lacks. Things graduate into `spec.md` once
they settle.

## 1. The original notes

> Traditional proofs of liveness assume some synchrony on a message per
> message basis. Something like after GST messages between honest parties
> arrive within a bound Δ. This is awkward as it requires us to think of the
> mechanics of how the DAG is transmitted in terms of messages.
>
> I would like to make a higher level assumption, which we could call
> **"Eventual DAG synchrony"**. I would state it as: after a Global
> stabilization time (GST), then if a correct validator has a view V1, then
> within a time bound Δ all correct validator views will contain V1 (as a
> subset of their view). Outside GST this sync only happens eventually
> (maybe not within time Δ).
>
> This should allow us to prove a few results:
>
> - After GST, within Δ if a correct validator commits all will commit.
> - From round 0 onwards correct validators have enough (2f+1) references to
>   previous rounds to build blocks, always.
> - After GST if validators wait to build these blocks they will commit.

## 2. Why the abstraction fits

The assumption is stated in terms of **views**, and `View` is already a
first-class structure in the development: a downward-closed subset of the
universe, sharing `U.block`. So `V₁ ⊆ V₂` is already meaningful, and every
safety result is already view-relative. The assumption composes with what
exists rather than sitting beside it.

It also abstracts the right thing. Nothing in the development cares *how*
blocks propagate, only that they do — and the assumption is realisable by
ordinary gossip, so it cannot be quietly inconsistent.

**But views carry only half of it.** View convergence gives L3 directly: the
common view *is* `View.full` (§4.2). It does **not** give
honest-to-honest coverage, because a block's references are frozen when it is
built and no later convergence enlarges them (§4.3). That is why
`Synchronised` is stated on `refs` rather than on views — the one place the
notes' framing does not reach.

## 3. What must be added

Liveness needs three primitives the static model does not have, and it is
worth being explicit about what kind of thing each is: (a) and (c) are
**protocol behaviour**; (b) is an **outcome** the protocol produces but cannot
name. None of the three is a DAG property.

**(a) Correct validators produce blocks.** `Correct` currently means only
*does not equivocate* — a purely negative condition, satisfied by a validator
that crashes at round 0 and never speaks again. That is deliberate: it is what
lets every safety result hold for crashed validators too. But it makes every
liveness statement vacuous without a positive rule:

> up to a horizon `N`, a correct validator has a round-`(r+1)` block once it
> **holds** round-`r` blocks from 2f+1 validators

**"Holds", not "exist".** A validator builds after a timeout, on a quorum
that is in *its own view* — it cannot act on blocks it has never received.
That needs a notion the static model lacks, so rule (a) is stated against
`Delivery.held` (§5). The timeout itself leaves no trace beyond that: with no
clock, waiting longer can only show up as a larger `held`.

This splits into two assumptions of different kinds, which is the point:
`builds` is **protocol** (hold a quorum, build), while `DeliversQuorum` is
**network** (a quorum that exists is eventually held). Both are
**asynchrony-only** — they need eventual delivery, not synchrony, and they are
what makes the pre-GST results go through.

**The horizon is not optional** — see §4.4. Without the bound `r < N` this
rule forces infinitely many distinct blocks into `U.ids`, which is a
`Finset`, so *no universe satisfies it* and every theorem assuming it is
vacuous. That was found by trying to build the witness model.

**(b) Correct blocks cover the correct blocks below them.** Distinct from
(a), and pulling the other way: (a) says build as soon as you can, (b) says
do not. After GST, every correct block references every correct block of the
round below. Without (b) correct validators race ahead under perfect
synchrony and never vote for the leader, so nothing commits. This is the
**synchrony** assumption, and §5's `Synchronised` is where it lives — for
now; §9's S4 splits it into an implementable rule and a delivery
assumption. It is not leader-specific: catching the leader's block is *why*
we want it, not what it says.

**This is an outcome, not an instruction.** A validator cannot tell which of
its peers are correct, so "wait for the correct blocks" is not something it
can execute. What it can do is wait on a **timeout** and build with whatever
arrived — and raise that timeout when commits stop arriving. After GST a long
enough timeout delivers every correct block of the round below. The coverage
is what synchrony plus backoff *produces*; the protocol never names it. See
§4.3.

The restriction to correct blocks is likewise not a simplification. A
validator cannot wait for Byzantine blocks, because they may never come.

**(c) Correct leaders recur.** `Slots.leader` is an arbitrary function, so
nothing currently stops a schedule from naming Byzantine validators forever —
and then nothing ever commits, however synchronous the network. Any statement
that commits *recur* needs a fairness condition:

> for every slot `k` there is a slot `k' ≥ k` whose leader is correct

Round-robin over `3f+1` validators supplies it, since at least `2f+1` of every
`3f+1` leaders are correct. But the `Slots` class does not require
round-robin, so this has to be assumed separately.

## 4. The phases

The three phases the protocol actually passes through, and what each one
supports. This is the part where the abstraction has to be handled carefully:
one of the phases turns out to be invisible, and saying so precisely is what
keeps the framing honest.

§4.4 is **not** a fourth phase. It records why `U` is finite and what that
costs — a modelling constraint that cuts across all three.

### 4.1 Before GST — the DAG still grows

Messages are delayed arbitrarily, so correct validators sit at wildly
different rounds: one whose incoming traffic is delayed is stuck at round 0
while others race ahead. Nothing rules that out, and nothing needs to.

Two things still hold.

**L0 needs no assumptions whatever.** Validity alone forces the DAG to be
*dense* below its frontier — see §6. The interesting content is not that the
DAG grows but that it **cannot grow tall and thin**: a single block high up
forces a quorum of authors at every round beneath it.

**L1 needs only asynchrony.** With rule (a) and eventual delivery, every
correct validator eventually has a block at every round up to the horizon
(§4.4). No synchrony.

**Round spread is not a theorem.** That correct validators may be far apart in
round number is a *negative* fact — an absence of any bound — so it belongs in
a test model as an exhibit, not as a statement to prove. Worth building: a
universe where L0 holds while the spread is arbitrary.

### 4.2 The transition — invisible to this framing, and that is the honest report

At GST the slow validators hold stale views, receive everything, and burst
forward through the rounds they missed. In wall-clock terms this catch-up is
real and takes time.

**The snapshot cannot see it.** Up to the horizon every correct validator has
a block at every round (L1). The only question the snapshot can ask of a block
is *whether it references every correct block of the round below*, and that is
a property of the round it was built at — not of when it was built.

So GST and the end of catch-up are **indistinguishable** here: both are "some
round from which correct blocks see every correct block below them".

**`U` is the common view as of the snapshot.** Eventual DAG synchrony says
anything one correct validator holds, all eventually hold. So the union of the
correct validators' views *is* `U`, and every correct validator's view of the
snapshot is the **full** view — `ids := U.ids`, downward-closed for free by
`U.complete`.

That is the crispest form the assumption takes here, and it is what makes L3
a theorem rather than an appeal: "eventually all agree" becomes "L2
instantiated at the full view". It also fixes what `U` *means* — not "every
block anyone ever wrote", but "every block some correct validator ever held".
A Byzantine block revealed to nobody is simply not in the universe.

**(assumption)** `R` is therefore *not* the GST round. It is defined as the
round from which synchrony has fully taken effect — GST plus however long
catch-up ran. What this framing gives up is any bound on `R − GST`, which is
precisely the quantitative content already dropped with Δ (§4.3). It is not
evasion: the framing is correctly reporting that the distinction is not
observable in it.

### 4.3 After R — honest-to-honest coverage, and why views do not give it

The final phase is *"all correct blocks contain all other correct blocks
because of the sufficient delay"*.

**Honest-to-honest only.** The assumption says a *correct* block references
every *correct* block of the round below, and both restrictions are load
bearing:

- **Nothing may be assumed about Byzantine blocks existing.** A Byzantine
  validator can publish nothing at all, so there is no round-`n` block of
  theirs to reference. It can equally publish and reveal to only some
  validators, so even correct validators cannot be assumed to hold it.
- **Nothing needs to be.** L4 counts only correct certificates, and there are
  `2f+1` correct validators — a quorum — so the argument never asks whether a
  Byzantine block was seen.
- **Well-formedness survives.** A correct block referencing every correct
  block of the round below already names `≥ 2f+1` distinct creators, so
  validity's quorum condition is met without any Byzantine reference. Nothing
  is lost by the restriction.

Getting this wrong in the *strong* direction — assuming all blocks are
referenced — would be assuming Byzantine validators behave, which is exactly
what a fault model must not do.

This **does not follow** from view convergence, and the reason is worth
recording.

**A block's references are frozen when it is built.** A correct validator
building at round `n+1` waits for 2f+1 round-`n` blocks; the arrival of the
2f+1st says nothing about the rest having arrived. Convergence of *views* does
not retroactively enlarge *blocks*.

So honest-to-honest coverage comes from **waiting past 2f+1**, justified by a
timing argument this development does not formalize.

**The mechanism is an adaptive timeout, and the gap matters.** A correct
validator cannot identify which of its peers are correct, so it cannot wait
*for the correct blocks*. It waits a fixed period and builds on whatever
arrived. Before GST no period is long enough, and nothing lets the validator
detect that directly — what it observes is that **commits have stopped**.
Raising the timeout when commits stall is what eventually pushes the period
past the true delay.

`Synchronised R` is therefore the *outcome* of that feedback loop once the
network settles, not a rule any validator follows. It is stated in terms the
protocol cannot itself observe, and the loop that delivers it is driven by
liveness failure — the very thing being proved away.

It also welds two unlike things into one object: the network guarantee and
rule (3b). That is a modelling defect rather than a necessity, and open
§9's S4 records the split — `Synchronised` becomes a **theorem**, derived
from an implementable protocol rule plus a delivery assumption. The timeout
story above then attaches to something real: a timeout governs what a
validator *holds*, which is a notion the split introduces and `refs` alone
cannot express.

What the split does **not** do is make anything unconditional. There is no
time model here, so the chain bottoms out at delivery: the timing content
still enters as an assumption, only a cleaner one. And this section's argument
is untouched either way — coverage does not follow from view convergence,
however the assumption is packaged.

**(assumption)** No wall clock and **no Δ**. Δ would force views indexed by an
instant and every statement quantified over instants, for no proof content:
the theorems are *"all will commit"* and *"never gets stuck"*, and Δ is a
performance claim layered on top. Flag if the quantitative bound is wanted —
it brings back the time model and should be scoped separately.

### 4.4 The horizon — why `U` is finite, and what that costs

`BlockUniverse.ids` is a **`Finset`**. Every universe holds finitely many
blocks. That is not incidental: it is what makes `authorsAt` have a
cardinality at all, and every quorum argument in the development counts one.

The first draft of `Live` ignored this. It said a correct validator has a
block at round 0 and another at every round after — infinitely many distinct
blocks, in a `Finset`. So **no universe satisfied it**, and L1, though
proved, said nothing. This is checked, not argued — writing `Live⁰` for that
unbounded draft:

```lean
theorem not_live (U : BlockUniverse Validator BlockId Payload) : ¬ Live⁰ U
```

The proof is three lines: pick a correct validator, collect its blocks at
rounds `0 … |U.ids|`, and note they are `|U.ids| + 1` distinct members of
`U.ids`.

The fix is a **horizon** `N`: `builds` fires only for `r < N`, so the DAG
reaches round `N` and stops. Three things follow.

**`N` is a demand on the DAG, not a bound on it.** `Live U D N` requires that
correct validators *actually have* blocks at every round up to `N`. A larger
`N` is a **stronger** hypothesis satisfied by **fewer** DAGs — it is not
slack, and picking it enormous does not make the theorems cover more. What
makes them cover everything is that they are universally quantified over `N`:
a DAG of height `h` is handled at `N = h`, whatever `h` is. There is no
feasibility ceiling and no constant to choose.

**Two independent axes.** `N` measures *extent* — how far the DAG reaches.
`R` measures *quality* — from which round correct blocks cover the correct
blocks below. Neither implies the other, and all four combinations are real:

| | `R` small | `R` large, or never |
|---|---|---|
| **`N` large** | tall and synchronous — commits | tall but asynchronous — grows, commits nothing |
| **`N` small** | synchronous but short — nothing to commit yet | short and asynchronous |

Neither is a clock. `R` is a round index and `N` a round count; Δ stays
dropped (§4.3).

**Unboundedness moves to the family.** No finite snapshot contains infinitely
many commits, and the first draft's claim that one could was the bug. "The
ledger grows without bound" is now a statement across horizons: for every `N`
there is a DAG reaching it (`Ugrow`), and for every slot there is a later one
that commits (L6). That is the honest form of the claim when the object is a
`Finset`.

**What this does *not* touch.** L4 needs correct blocks at three consecutive
rounds — a local, finite requirement. It takes `Populated` at `r`, `r+1` and
`r+2` and never mentions `N`, growth, or a limit. The horizon appears only in
L1, which manufactures `Populated` from growth, and in L6, which chains them.
The only real proof in the plan is untouched by any of this.

## 5. Definitions

```lean
/-- What L4 actually needs of a round: every correct validator has a block
there. Local and finite — no growth, no horizon, no limit. Splitting this out
is what keeps `N` out of L4 entirely. -/
def Populated (U : BlockUniverse Validator BlockId Payload) (r : ℕ) : Prop :=
  ∀ v ∈ Correct, ∃ b ∈ U.ids,
    (U.block b).creator = v ∧ (U.block b).round = r

/-- What each validator had in hand, one round at a time. The layer the
static model lacks, and what lets `builds` and `Synchronised` each be stated
as a single kind of thing (settled questions S2 and S4).

Note what it does **not** contain: a clock. With no time model, a timeout can
only leave a trace as a larger `held`. -/
structure Delivery (U : BlockUniverse Validator BlockId Payload) where
  held : Validator → ℕ → Finset BlockId
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  /-- **Protocol rule.** A correct validator references everything it held.
  Implementable and observable, unlike `Synchronised` itself. -/
  includes : ∀ v ∈ Correct, ∀ n, ∀ b ∈ U.ids, (U.block b).creator = v →
    (U.block b).round = n + 1 → held v n ⊆ (U.block b).refs

/-- The protocol behaviour liveness needs. Not derivable from the DAG
structure: `Correct` is a negative condition, and these are positive.
Asynchrony-only — no synchrony here.

`N` is the **horizon**: `builds` fires only below it, so the DAG reaches
round `N` and stops. Without that bound the structure is unsatisfiable, since
`U.ids` is a `Finset` (§4.4). -/
structure Live (U : BlockUniverse Validator BlockId Payload)
    (D : Delivery U) (N : ℕ) where
  genesis : Populated U 0
  builds  : ∀ r < N, ∀ v ∈ Correct,
    2 * F.f + 1 ≤ (creatorsOf U.block (D.held v r)).card →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r + 1

/-- Asynchrony: a quorum that *exists* is eventually *held*. Conditional on
existence, since unconditionally it would assert the block production L1 sets
out to prove. No round bound — this holds before GST too. -/
def DeliversQuorum (D : Delivery U) : Prop :=
  ∀ n, 2 * F.f + 1 ≤ (authorsAt U n).card →
    ∀ v ∈ Correct, 2 * F.f + 1 ≤ (creatorsOf U.block (D.held v n)).card

/-- From round `R` on, correct blocks reference every correct block of the
round below.

`R` is **not** GST: it is the round from which synchrony has fully taken
effect (§4.2). This single predicate carries both the network guarantee and
rule (§3b), because honest-to-honest coverage does not follow from view
convergence alone (§4.3). §9's S4 splits it and makes this a
*theorem*; the statement below is unchanged by that — only how it is
obtained.

Both quantifiers are restricted to `Correct`, and deliberately: a Byzantine
validator may publish nothing, or publish and withhold, so no assumption
about referencing its blocks would be sound — and none is needed (§4.3). -/
def Synchronised (U : BlockUniverse Validator BlockId Payload) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ (Correct : Finset Validator) → a ∈ (U.block b).refs

/-- **Synchrony.** After `R`, the *whole* correct round is held — not merely
a quorum of it, which is what `DeliversQuorum` gives unconditionally.
Together with `Delivery.includes` this yields `Synchronised` (L7). -/
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ Correct, ∀ a ∈ U.ids, (U.block a).round = n →
    (U.block a).creator ∈ Correct → a ∈ D.held v n

/-- Every correct validator's *eventual* view (§4.2). Downward-closed for
free, by `U.complete`. -/
def View.full (U : BlockUniverse Validator BlockId Payload) :
    View Validator BlockId Payload U where
  ids := U.ids
  subset_ids := Finset.Subset.rfl
  complete := U.complete

/-- The schedule names a correct leader arbitrarily far out (§3c). Without
it, no recurrence statement holds: `Slots.leader` is an arbitrary function
and could name Byzantine validators forever. -/
def FairSchedule : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ (Correct : Finset Validator)
```

## 6. The results

### Without synchrony

- **L0 — The DAG is dense below its frontier.** If any block exists at round
  `r`, then every round `n < r` has at least `2f+1` distinct authors.

  A round-`r` block references 2f+1 distinct round-`(r-1)` creators, so round
  `r-1` carries a quorum of authors; that round is then nonempty, so the same
  argument applies below it. Downward induction.

  **No assumptions at all** — not `Live`, not `Synchronised`. This is validity
  alone, and both ingredients already exist (`creators_quorum`,
  `creators_refs_subset_authorsAt`). It is the precise form of *"the DAG grows
  regardless"*, and it says more than growth: the DAG cannot be tall and thin.

- **L1 — No stall.** Given `Live U D N` and `DeliversQuorum D`, every correct
  validator has a block at every round up to `N`: `r ≤ N → Populated U r`.

  Induction on `r`. Base is `genesis`. The step takes **two** hops, because
  `builds` is view-relative: the induction hypothesis puts every correct
  validator in `authorsAt U r`, so a quorum *exists*; `DeliversQuorum` turns
  that into each correct validator *holding* a quorum; only then does `builds`
  apply. Still **no synchrony** — the notes' *"from round 0 onwards,
  always"*, now qualified by the horizon (§4.4).

  This is where `card_correct` (`2f+1 ≤ |Correct|`) finally gets used.
  `spec.md` §2 has carried it as unused-but-kept-for-liveness from the start.

  L1 is the **only** result where `N` does real work: its whole job is to turn
  a growth assumption into the local `Populated` facts L4 consumes.

### View growth

- **L2 — Decisions are monotone in the view.** If `V ⊆ V'` then
  `Decided U V k v → Decided U V' k v`.

  Induction on the derivation. `DirectCommitIn` and `DirectSkipIn` are both
  monotone — intersecting the certificate or blame set with a larger view can
  only grow the creator set — and the indirect cases follow inductively.

  **This works only because `CertifiedIn` is universe-level.** The
  `indirectSkip` case carries a *negative* premise — no candidate is certified
  in reach of the anchor. Had the indirect check been view-relative, that
  premise would be **anti**-monotone: growing the view could reveal a
  certificate and flip a skip into a commit, and L2 would be false. C1 defined
  `CertifiedIn` over `U` rather than `V`, with T6a
  (`certifiedIn_iff_of_view`) showing the view-restricted computation agrees.
  That is what keeps the negative premise stable.

  Worth having independently of liveness: combined with M1 it says a validator
  **never revises a decision** as its view grows. The safety results so far say
  decisions do not *conflict*; they do not say decisions do not *change*.

- **L3 — Commit propagation.** If any validator decides slot `k` on any view,
  the same verdict holds on the **full** view:
  `Decided U V k v → Decided U (View.full U) k v`.

  L2 instantiated at `V' = View.full U`. Since every correct validator's
  eventual view is the full view (§4.2), this *is* "all correct validators
  eventually reach the same decision" — with the informal "eventually"
  discharged by the framing rather than waved at.

### After R

- **L4 — A correct leader commits.** Write `r = slotRound k`. Given
  `Populated U r`, `Populated U (r+1)`, `Populated U (r+2)`,
  `Synchronised U R`, `R ≤ r`, and `leader k` correct, the leader's block is
  directly committed.

  **Population is not optional here.** `Synchronised` says correct blocks
  *reference* correct blocks; it says nothing about blocks *existing*. Without
  it the theorem is satisfied vacuously by an empty DAG.

  **But growth is.** The three hypotheses are local and finite — no `Live`,
  no `N`, no limit universe. L1 supplies them from `Live U D N` when
  `r + 2 ≤ N`, but L4 does not care where they come from. That is what keeps
  the only hard proof in the plan independent of the horizon question
  (§4.4).

  Every correct round-`(r+1)` block references `L` by synchrony — `L` is
  correct-authored, so honest-to-honest coverage applies — and the supporters
  therefore include all correct validators, at least `2f+1`. Every correct
  round-`(r+2)` block then references all of *those*, so its `votesIn` has
  `2f+1` distinct correct creators and it certifies `L`. Since there are
  `2f+1` correct validators, `DirectCommit` follows.

  **Only correct-to-correct coverage is used.** The argument never asks
  whether any Byzantine block was produced or seen, which is what lets
  `Synchronised` stay restricted to correct authors on both sides (§4.3).

  The conclusion is the *universe-level* `DirectCommit`. It becomes an actual
  decision through the full view: `DirectCommitIn` there is `DirectCommit`,
  so `Decided U (View.full U) k (some L)` follows — which is what L6 needs and
  what L3 propagates.

- **L5 — An absent leader is skipped.** If `leader k` has no
  round-`slotRound k` block, the slot is decided `none`.

  Nearly free, and it vindicates a C1 decision: `Decided.directSkip` takes the
  premise `∀ L, IsLeaderBlock U k L → DirectSkipIn U V L …`, which is
  **vacuously true** when the leader published nothing. Choosing the `∀` form
  over naming a candidate block is what makes this case disappear.

- **L6 — Commits recur.** Given a `FairSchedule`, for every slot `k` there is
  a slot `k' ≥ k` such that **every** sufficiently grown synchronous DAG
  commits it:

  > `∀ k, ∃ k' ≥ k, R ≤ slotRound k' ∧`
  > `  ∀ U D N, Live U D N → DeliversQuorum D → Synchronised U R →`
  > `    slotRound k' + 2 ≤ N → slot k' commits`

  **The quantifier order is the whole content, and getting it wrong makes the
  statement false.** The tempting form — *given `Live U D N`, for every `k`
  there is a committing `k' ≥ k` with `slotRound k' + 2 ≤ N`* — is not
  provable. Fairness promises a correct leader *somewhere* beyond `k`, and
  that slot may lie past the horizon; nothing lets you ask for a nearer one.
  Fixing `U` and `N` first therefore caps how far fairness may reach.

  Stated as above the problem disappears, because `k'` depends only on the
  **schedule** — `FairSchedule` and `slotRound` are properties of the `Slots`
  instance, not of any DAG. So the slot is named first and the DAG grows to
  it second, which is also the correct reading of *"the ledger grows without
  bound"*: not that one DAG commits infinitely often, but that no slot is the
  last one a DAG can be grown far enough to commit.

  Fairness names a correct leader at some `k' ≥ max(k, k_R)`, where `k_R` is
  any slot with `R ≤ slotRound k_R`; L1 then populates its three rounds and L4
  commits it.

  Such a `k_R` exists because `slotRound` is unbounded — the `Slots` spacing
  condition gives `slotRound k + 3 ≤ slotRound (k+1)`, so rounds grow without
  limit. Small, but it is a real proof obligation rather than an aside.

  **The two side conditions read as they should.** `R ≤ slotRound k'` is
  *this slot is after synchrony took hold*; `slotRound k' + 2 ≤ N` is *the
  DAG has grown past this slot's certificate rounds*. A DAG with `R > N`
  satisfies neither for any slot and commits nothing — correct, since it
  stopped growing before synchrony arrived.

  **Unboundedness lives across horizons, not inside one.** No finite snapshot
  holds infinitely many commits. Read L6 together with `ugrow_live` — for
  every `N` a DAG reaches it, and for every slot a later one commits (§4.4).

  **Not "every slot decides".** An earlier draft claimed that, and it is
  false. L4 needs a *correct* leader and L5 an *absent* one; a Byzantine
  leader that publishes a block and reveals it to only some validators falls
  in neither gap. `Synchronised` is honest-to-honest, so it says nothing about
  whether correct validators reference a Byzantine-authored block — some will,
  some will not, and the slot stays undecided.

  That case is exactly why the indirect rule exists, and why M4/M6 are **not**
  made redundant by liveness. Recurrence is the right shape for the statement:
  not "the machinery for undecided slots becomes unreachable" but "undecided
  slots cannot delay the ledger indefinitely, because a correct leader is
  always coming".

## 7. Staging

| | | risk | |
|---|---|---|---|
| L0 | density below the frontier | low — existing lemmas, no new primitives | ✓ `card_authorsAt_of_lt` |
| L2 | view-monotonicity of `Decided` | low — mirrors `decided_unique`'s induction | ✓ `decided_mono` |
| L3 | `View.full`, then L2 instantiated | low | ✓ `decided_full` |
| — | **`Ugrow`: a family satisfying `Live`, `DeliversQuorum` and `Synchronised` at every `N`** | low, and required **first** | ✓ `ugrow_live`, `ugrow_deliversQuorum`, `ugrow_synchronised` |
| L1 | `Live U D N` + `DeliversQuorum D`, then induction on rounds | low | ✓ `no_stall` |
| L4 | `Populated` ×3 + `Synchronised`, then the two-layer argument | medium — the only real proof | ✓ `directCommit_of_correct_leader` |
| L5 | vacuity of the `∀`-over-candidates premise | low | ✓ `decided_none_of_leader_absent` |
| L6 | `FairSchedule`, then L1 and L4 | low — but see the quantifier order | ✓ `commits_recur` |
| L7 | `Delivery`, then `Synchronised` as a theorem | low — see S4 | ✓ `synchronised_of_delivery` |

L0, L2 and L3 come first because none needs a new primitive: L0 is pure DAG
structure, L2 and L3 are pure view reasoning. That defers every modelling
decision until something is already proved.

**The witness now comes before L1, not before L4.** An earlier draft staged it
later, and that ordering is what let an unsatisfiable `Live` be *proved
against* before anyone tried to satisfy it. The revised rule: a definition
gets a witness before anything is proved from it, not before the theorem that
matters most.

**The model is not optional, and this is not hypothetical.** The first draft
of `Live` was *unsatisfiable* — `U.ids` is a `Finset` and the rule forced
infinitely many blocks — so L1 was proved and said nothing. It was caught by
sitting down to build the witness, which is exactly the argument for building
one (§4.4).

The witness must be a **family** `Ugrow N`, not a single model: one model
shows `Live` holds at one horizon, whereas the claim needed is that every
horizon is reachable. `BlockId := ℕ` with round `b / (3f+1)`, creator
`b % (3f+1)`, and refs the previous round's ids — finite at each `N`,
unbounded across them. The existing `U`–`U7` cannot serve: all are `Fin n`
and fixed height.

It must also satisfy `Synchronised` for some `R`, since if `Live` and
`Synchronised` were jointly unsatisfiable then L4–L6 would still be vacuous.
Building both into one family settles both questions at once — and since
`Ugrow`'s blocks reference *every* block of the round below, `R = 0` should
fall out.

**L7 came last deliberately, and that was right — but it was not "purely
additive" as predicted.** The reasoning for staging it late held up: L4–L6
keep taking `Synchronised` unchanged, L7 simply supplies it a second way, and
doing it first would have meant guessing which shape of `held` L4 wanted.

What was not foreseen is that once `Delivery` existed, it made S2 settleable —
and settling S2 changed `Live`, which now takes the `Delivery` it is stated
against. So the layer is additive *downstream* of `Synchronised` and a
*prerequisite* upstream of it.

The visible consequence: **proof order and file order now differ.** `Delivery`
is defined near the top of `Liveness.lean`, ahead of `Live`, even though
`synchronised_of_delivery` was the last theorem proved. That is the right
outcome — the late proof is what revealed where the definition belonged — but
it is worth flagging, since the staging table below reads as a file order and
is not one.

## 8. Open questions

Ordered by **importance** — whether a real deployment could be hurt if the
question goes unanswered — not by how easy each is to settle. Cost is listed
separately, because the cheapest item here is not the most important one.

| | question | why it matters | cost |
|---|---|---|---|
| **Q1** | Does a timeout actually deliver honest-to-honest coverage? | the central assumption could be **false** in practice | high |
| **Q2** | Is `Populated` too strong? | guarantees lapse under ordinary operation, not attack | **low** |
| **Q3** | How far should the quantitative version go? | no operational bound of any kind | high |
| **Q4** | Should `FairSchedule` be round-robin? | no throughput bound; leader predictability unmodelled | medium |
| **Q5** | Is a partial-view model needed? | two definitions are exercised only degenerately | low |
| **Q6** | Should L1 hold from round 0, or only after `R`? | presentational | low |

### Q1 — Does a timeout actually deliver honest-to-honest coverage?

**The largest unproved link between this development and an implementation.**

A correct validator waits on a timeout and builds on whatever arrived; it
cannot tell correct peers from Byzantine ones (§3b). If Byzantine validators
respond *fast* while some correct ones are slow, a validator can fill its
quorum with Byzantine blocks and miss correct ones — **violating
`Synchronised` even after GST**. §4.3 states the justification is "a timing
argument this development does not formalize". That sentence is the gap.

Distinct from Q3: Q3 asks for a *bound*, Q1 asks whether the qualitative
property holds **at all**. If it fails, L4–L6 are true but empty — every
theorem after L3 rests on `Synchronised`.

Expensive, because settling it needs the time model §4.3 deliberately drops.
But it is the assumption most likely to be false, so it heads the list.

### Q2 — Is `Populated` too strong?

`Populated U r` demands that **every** correct validator have a block at round
`r`, and L4 needs three consecutive such rounds. One correct validator missing
one round — a GC pause, a restart, a slow disk — and L4 becomes inapplicable.

But Mysticeti still commits: it needs `2f+1` blocks at each round, not a
*particular* set of them. **So the theorem is strictly weaker than the
protocol**, and it lapses under ordinary operational hiccups rather than under
attack, which is the wrong way round.

Restate as *a quorum of correct validators is populated*. L4's proof only ever
counts to `2f+1`, so it should survive unchanged — this is the cheapest real
improvement on the list.

One caveat on how much it buys: when exactly `f` validators are Byzantine,
`|Correct| = 2f+1` and the two formulations coincide. The gain shows when
fewer than `f` are actually faulty, which is the common case.

### Q3 — How far should the quantitative version go?

Everything proved here is *"eventually"*. Three things a deployment needs and
this cannot supply:

- **No bound on `R − GST`** (§4.2). Operationally that is recovery time after
  a partition heals — usually the number people care about most.
- **No proof the adaptive timeout converges.** §4.3 records that the backoff
  is driven by commits stalling. Real implementations *cap* the timeout, and
  whether the cap exceeds the true delay **is** the liveness question. A
  system whose cap is too low never recovers, and nothing here would notice.
- **No commit latency.** Direct commit is `r+2`, but a Byzantine leader pushes
  the work onto the indirect rule with no bound on how distant the anchor is.

§4.3 drops Δ, and Q4 would reintroduce counting of a different kind (slots
rather than time); those are separable, since slot-counting needs no clock.
The layer Δ attaches to now exists: `held`, not `refs` (S4).

### Q4 — Should `FairSchedule` be round-robin?

Two distinct issues behind one definition.

**No rate.** `FairSchedule` is satisfied by a schedule naming a correct leader
once every `10⁹` slots. L6 then guarantees the ledger grows and says nothing
about how fast. Round-robin gives at least `2f+1` correct leaders per `3f+1`
slots — a quantitative claim of the kind §4.3 otherwise avoids, but one that
needs no clock.

**Leader predictability is unmodelled.** `Slots.leader` is an arbitrary
function, so nothing distinguishes a schedule an adversary can predict from
one it cannot. An adversary who knows who leads slot `k` can attack them
before their round — a standard attack on this protocol family, and entirely
invisible here.

The witness makes the weakness concrete: `ugrow_fair` uses a *constant*
correct leader, satisfying fairness in the weakest possible way, so nothing
currently exercises the condition.

### Q5 — Is a partial-view model needed?

`Ugrow` sets `held v n` to *every* round-`n` block, so the delivery hop added
by S2 is never exercised against a genuinely partial view — and partial views
are the normal case, not the exception. `DeliversQuorum` and `Delivery` are
therefore satisfiable but barely tested.

One construction would settle two things at once, since the same model gives
the round-spread exhibit §4.1 asks for: a universe where L0 holds while
correct validators sit at arbitrarily different rounds, documenting that L0
assumes no synchrony — easy to doubt when reading L0 alone.

### Q6 — Should L1 hold from round 0, or only after `R`?

As stated it holds from round 0 with no synchrony, which is stronger and
matches the notes. It does assume correct validators never stop before the
horizon — but a correct validator that stops is a *crash* fault, and crash
faults are a subset of Byzantine, so the `f` budget already covers it.
Presentational. Note this is independent of §4.4: the horizon bounds *how far*
L1 reaches, not *where it starts*.

## 9. Settled questions

Kept because each was decided against a defensible alternative, and the
reasoning is what a later reader will want.

### S1 — `Live` is an explicit argument, not a class

`Faults` is a class because it is *universal*: every theorem in the
development carries it, so hiding it costs nothing. `Live` is not — L0, L2
and L3 do without it and L1 does not. When an assumption separates the
unconditional results from the conditional ones, hiding it is exactly
backwards; a reader could no longer tell which is which from a signature.

Folding `Live` into `Faults` was considered and is impossible anyway: the
dependency runs the wrong way, since `Live` mentions a `BlockUniverse`
whose own type requires `Faults`. It would also be undesirable if it were
possible — every safety theorem would acquire a liveness hypothesis it does
not use, and `decided_unique` currently holds *even if correct validators
crash*. That is the standard safety/liveness split, and it is worth
keeping.

### S2 — `builds` is stated on `held`, not on existence

The first form said a correct validator builds once *any* `2f+1`
validators have round-`r` blocks. That is not something a validator can
act on: it cannot build on blocks it has never received. The real rule is
a **timeout plus a quorum in its own view**.

Once S4's `Delivery` layer existed, `held` was exactly the missing
notion, so `builds` is now measured against `D.held v r`. The condition
splits cleanly in two, which is the gain: `builds` is protocol (hold a
quorum, build) and `DeliversQuorum` is network (a quorum that exists is
eventually held). Both are asynchrony-only, so L1 still needs no synchrony
— its step simply takes two hops instead of one.

The **timeout leaves no trace** beyond this. With no clock, waiting longer
can only show up as a larger `held`; `builds` therefore asks for a quorum
in view and nothing more, and `EventuallyDelivers` is what demands the
*whole* correct round after `R`.

### S3 — `Live` is finite, with a horizon `N`

Recorded because the alternative is defensible and was rejected on cost,
not on principle. Making `BlockUniverse.ids` a `Set` would let `U` be the
genuine limit and would state unbounded growth inside a single universe —
which is what §4.2 originally claimed. It was rejected because it reopens a
*finished and verified* safety development: `blocksAt`/`authorsAt` would
need per-round finiteness as a new `BlockUniverse` field (not derivable —
`no_equivocation` constrains only correct authors, so a Byzantine validator
may author unboundedly many blocks in one round), and `Set` membership is
undecidable, so all 135 `by decide` proofs in `LeanDagTest` would need
rework across 72 `.ids` sites.

That `decide` infrastructure is what has caught every vacuity bug in this
project — including the one that forced this question. Trading it away to
make a paragraph literally true is the wrong exchange.

A third option — `builds` firing only when round `r+1` is already nonempty
— was rejected for saying nothing about the DAG getting *taller*, which
discards the notes' *"from round 0 onwards, always"* entirely.

### S4 — `Synchronised` is derived, not assumed

`Synchronised` welds two unlike things together: a protocol rule and a
network guarantee. It cannot be derived from anything in the model as it
stands, because the model is a static `BlockUniverse` — blocks and refs,
no time, no delivery, no record of what a validator *held* when it built.
`Synchronised` is stated on `refs` because `refs` is all there is.

Adding that missing layer splits it:

```lean
structure Delivery (U : BlockUniverse Validator BlockId Payload) where
  /-- What `v` held from round `n` when it built its round-`(n+1)` block. -/
  held : Validator → ℕ → Finset BlockId
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  /-- **Protocol rule.** A correct validator references everything it held. -/
  includes : ∀ v ∈ Correct, ∀ n, ∀ b ∈ U.ids, (U.block b).creator = v →
    (U.block b).round = n + 1 → held v n ⊆ (U.block b).refs

/-- **Network assumption.** After `R`, correct blocks reach correct
validators in time to be built on. This is eventual DAG synchrony. -/
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop := ...

theorem synchronised_of_delivery (D : Delivery U) (h : EventuallyDelivers D R) :
    Synchronised U R
```

The proof is `refs ⊇ held ⊇ all correct blocks below` — a few lines. **The
gain is not logical.** One assumption becomes two, and nothing turns
unconditional. The gain is that each piece is a single kind of thing:
`includes` is implementable and observable, which is exactly what §3(b)
notes `Synchronised` fails to be; `EventuallyDelivers` is pure network.

It also puts the timeout in the right place. A timeout governs *when you
build*, i.e. what lands in `held` — it has nothing to do with `refs`. §4.3
currently explains the backoff next to a definition that structurally
cannot express it. And if the quantitative version (Q3) is ever
wanted, Δ attaches to `held`, not to `refs`: that is the layer where a
time bound means anything.

`Synchronised` keeps its exact statement. It stops being a hypothesis one
assumes and becomes one that can be discharged, so L4–L6 are untouched.
