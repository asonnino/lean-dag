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
eventual common view *is* `View.full` (§4.2). It does **not** give
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
*does not equivocate* — a purely negative condition. Every liveness statement
is vacuous without a positive rule:

> a correct validator has a round-`(r+1)` block once 2f+1 validators have
> round-`r` blocks

This is an **asynchrony-only** assumption: it needs eventual delivery, not
synchrony, and it is what makes the pre-GST results go through.

**(b) Correct blocks cover the correct blocks below them.** Distinct from
(a), and pulling the other way: (a) says build as soon as you can, (b) says
do not. After GST, every correct block references every correct block of the
round below. Without (b) correct validators race ahead under perfect
synchrony and never vote for the leader, so nothing commits. This is the
**synchrony** assumption, and §5's `Synchronised` is where it lives — for
now; open question 7 splits it into an implementable rule and a delivery
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
correct validator eventually has a block at every round. No synchrony.

**Round spread is not a theorem.** That correct validators may be far apart in
round number is a *negative* fact — an absence of any bound — so it belongs in
a test model as an exhibit, not as a statement to prove. Worth building: a
universe where L0 holds while the spread is arbitrary.

### 4.2 The transition — invisible to this framing, and that is the honest report

At GST the slow validators hold stale views, receive everything, and burst
forward through the rounds they missed. In wall-clock terms this catch-up is
real and takes time.

**The limit universe cannot see it.** In the limit every correct validator has
a block at every round (L1). The only question the limit can ask of a block is
*whether it references every correct block of the round below*, and that is a
property of the round it was built at — not of when it was built.

So GST and the end of catch-up are **indistinguishable** here: both are "some
round from which correct blocks see every correct block below them".

**The limit universe is the eventual common view.** Eventual DAG synchrony
says anything one correct validator holds, all eventually hold. So the union
of the correct validators' views *is* `U`, and every correct validator's
eventual view is the **full** view — `ids := U.ids`, downward-closed for free
by `U.complete`.

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
question 7 records the split — `Synchronised` becomes a **theorem**, derived
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

## 5. Definitions

```lean
/-- The protocol behaviour liveness needs, as properties of the limit
universe. Not derivable from the DAG structure: `Correct` is a negative
condition, and these are positive. Asynchrony-only — no synchrony here. -/
structure Live (U : BlockUniverse Validator BlockId Payload) where
  genesis : ∀ v ∈ Correct, ∃ b ∈ U.ids,
    (U.block b).creator = v ∧ (U.block b).round = 0
  builds  : ∀ r, 2 * F.f + 1 ≤ (authorsAt U r).card →
    ∀ v ∈ Correct, ∃ b ∈ U.ids,
      (U.block b).creator = v ∧ (U.block b).round = r + 1

/-- From round `R` on, correct blocks reference every correct block of the
round below.

`R` is **not** GST: it is the round from which synchrony has fully taken
effect (§4.2). This single predicate carries both the network guarantee and
rule (§3b), because honest-to-honest coverage does not follow from view
convergence alone (§4.3). Open question 7 splits it and makes this a
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

/-- Every correct validator's *eventual* view (§4.2). Downward-closed for
free, by `U.complete`. -/
def View.full (U : BlockUniverse Validator BlockId Payload) :
    View Validator BlockId Payload U where
  ids := U.ids
  subset_ids := le_refl _
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

- **L1 — No stall.** Every correct validator has a block at every round.

  Induction on `r`. Base is `genesis`. For the step, the induction hypothesis
  puts every correct validator in `authorsAt U r`, and there are at least
  `2f+1` correct validators, so `builds` applies. Needs `Live` but **no
  synchrony** — the notes' *"from round 0 onwards, always"*.

  This is where `card_correct` (`2f+1 ≤ |Correct|`) finally gets used.
  `spec.md` §2 has carried it as unused-but-kept-for-liveness from the start.

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

- **L4 — A correct leader commits.** Given `Live U`, `Synchronised U R`,
  `R ≤ slotRound k`, and `leader k` correct, the leader's block is directly
  committed.

  **`Live` is not optional here.** `Synchronised` says correct blocks
  *reference* correct blocks; it says nothing about blocks *existing*. Without
  `Live` the theorem is satisfied vacuously by an empty DAG. L1 supplies the
  leader's round-`r` block and the correct blocks at `r+1` and `r+2` that the
  argument counts.

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

- **L6 — Commits recur.** Given `Live U`, `Synchronised U R` and a
  `FairSchedule`, for every slot there is a later slot that commits — so the
  ledger grows without bound.

  Fairness names a correct leader at some slot `k' ≥ max(k, k_R)`, where `k_R`
  is any slot with `R ≤ slotRound k_R`; L4 then commits it.

  Such a `k_R` exists because `slotRound` is unbounded — the `Slots` spacing
  condition gives `slotRound k + 3 ≤ slotRound (k+1)`, so rounds grow without
  limit. Small, but it is a real proof obligation rather than an aside.

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
| L2 | view-monotonicity of `Decided` | low — mirrors `decided_unique`'s induction | |
| L3 | `View.full`, then L2 instantiated | low | |
| L1 | `Live`, then no-stall by induction on rounds | low | |
| — | **a model satisfying `Live` and `Synchronised`** | low, and required | |
| L4 | `Live` + `Synchronised`, then the two-layer argument | medium — the only real proof | |
| L5 | vacuity of the `∀`-over-candidates premise | low | |
| L6 | `FairSchedule`, then L4 | low | |
| L7 | `Delivery`, then `Synchronised` as a theorem | low — see question 7 | |

L0, L2 and L3 come first because none needs a new primitive: L0 is pure DAG
structure, L2 and L3 are pure view reasoning. That defers every modelling
decision until something is already proved.

**The model is not optional.** `Live` and `Synchronised` are assumptions, and
if they were jointly unsatisfiable then L1 and L4–L6 would hold vacuously and
prove nothing. They are satisfiable — a DAG in which every correct block
references every correct block below meets both, and `U5`/`U7` nearly do — but
the discipline everywhere else in this development is to *exhibit* a witness
rather than argue one exists. It should be built before L4, so that L4 is
known to say something the moment it is proved.

**L7 comes last deliberately.** It refines the assumptions rather than proving
anything new, and it is purely additive: L4 keeps taking `Synchronised`
unchanged and L7 supplies it a second way. Doing it first would mean carrying
the extra layer through every experiment while guessing which shape of `held`
L4 wants — and the witness model would have to be built against the heavier
definition. Doing it after costs nothing and is informed by a finished proof.

## 8. Open questions

1. **Should `Live` be a class or an explicit structure argument?** `Faults` is
   a class and that worked; but liveness hypotheses are the kind of thing one
   wants visible in a signature.
2. **Is `builds` the right rule?** It says a correct validator builds once
   *any* 2f+1 validators have round-`r` blocks. A real implementation waits for
   2f+1 blocks *it has received*, which in the limit is the same, but the two
   differ if we ever move off the limit framing.
3. **Do we want L1 unconditionally**, or only after `R`? As stated it holds
   from round 0 with no synchrony, which is stronger and matches the notes —
   but it does assume correct validators never stop.
4. **Is the round-spread exhibit worth building?** It proves nothing, but it
   documents that L0 is compatible with arbitrary asynchrony, which is easy to
   doubt when reading L0 alone.
5. **Should `FairSchedule` be round-robin instead?** The `∃ k' ≥ k` form is
   the weakest thing L6 needs, so it makes the theorem strongest. Round-robin
   would be more concrete and would let us say *how often* commits recur —
   at least `2f+1` per `3f+1` slots — which is a quantitative claim of the
   kind §4.3 otherwise avoids.
6. **How far should the quantitative version go?** §4.3 drops Δ, and open
   question 5 would reintroduce counting of a different kind (slots rather
   than time). Those are separable: slot-counting needs no clock.
7. **Should `Synchronised` be assumed or derived?** — **resolved: derived,
   staged after L4 as L7.**

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
   cannot express it. And if the quantitative version (question 6) is ever
   wanted, Δ attaches to `held`, not to `refs`: that is the layer where a
   time bound means anything.

   `Synchronised` keeps its exact statement. It stops being a hypothesis one
   assumes and becomes one that can be discharged, so L4–L6 are untouched.
