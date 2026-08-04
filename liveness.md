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

## 3. What must be added

Liveness needs two primitives the static model does not have, and it is worth
being explicit that these are **protocol behaviour**, not DAG properties.

**(a) Correct validators produce blocks.** `Correct` currently means only
*does not equivocate* — a purely negative condition. Every liveness statement
is vacuous without a positive rule:

> a correct validator has a round-`(r+1)` block once 2f+1 validators have
> round-`r` blocks

This is an **asynchrony-only** assumption: it needs eventual delivery, not
synchrony, and it is what makes the pre-GST results go through.

**(b) Correct validators wait for the leader.** Distinct from (a), and pulling
the other way: (a) says build as soon as you can, (b) says delay until the
round below is complete. Without (b), correct validators race ahead under
perfect synchrony and never vote for the leader, so nothing commits. This is
the **synchrony** assumption, and §5's `Synchronised` is where it lives.

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
*whether its references are complete*, and that is a property of the round it
was built at — not of when it was built.

So GST and the end of catch-up are **indistinguishable** here: both are "some
round from which references are complete".

**(assumption)** `R` is therefore *not* the GST round. It is defined as the
round from which synchrony has fully taken effect — GST plus however long
catch-up ran. What this framing gives up is any bound on `R − GST`, which is
precisely the quantitative content already dropped with Δ (§4.3). It is not
evasion: the framing is correctly reporting that the distinction is not
observable in it.

### 4.3 After R — complete references, and why it must be assumed

The final phase is *"all correct blocks contain all other correct blocks
because of the sufficient delay"*. This **does not follow** from view
convergence, and the reason is worth recording.

**A block's references are frozen when it is built.** A correct validator
building at round `n+1` waits for 2f+1 round-`n` blocks; the arrival of the
2f+1st says nothing about the rest having arrived. Convergence of *views* does
not retroactively enlarge *blocks*.

So reference-completeness is a **waiting rule** — the validator must delay
past 2f+1 — justified by a timing argument this development does not
formalize. `Synchronised R` therefore encodes *both* the network guarantee and
rule (3b), and it is an assumption rather than a theorem.

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
the waiting rule (§3b), because reference-completeness cannot be derived from
view convergence alone (§4.3). -/
def Synchronised (U : BlockUniverse Validator BlockId Payload) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ (Correct : Finset Validator) → a ∈ (U.block b).refs
```

## 6. The results

### Pre-GST

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

  Worth having independently of liveness: combined with M1 it says a validator
  **never revises a decision** as its view grows. The safety results so far say
  decisions do not *conflict*; they do not say decisions do not *change*.

- **L3 — Commit propagation.** If one correct validator decides slot `k`,
  every correct validator eventually reaches the same decision. L2 plus
  eventual DAG synchrony, which supplies `V ⊆ V'`.

### After R

- **L4 — A correct leader commits.** If `Synchronised U R`, `R ≤ slotRound k`,
  and `leader k` is correct, then its block is directly committed.

  Every correct round-`(r+1)` block references `L` by synchrony, so the
  supporters include all correct validators — at least `2f+1`. Every correct
  round-`(r+2)` block then references all of *those*, so its `votesIn` has
  `2f+1` distinct correct creators and it certifies `L`. Since there are
  `2f+1` correct validators, `DirectCommit` follows.

- **L5 — An absent leader is skipped.** If `leader k` has no
  round-`slotRound k` block, the slot is decided `none`.

  Nearly free, and it vindicates a C1 decision: `Decided.directSkip` takes the
  premise `∀ L, IsLeaderBlock U k L → DirectSkipIn U V L …`, which is
  **vacuously true** when the leader published nothing. Choosing the `∀` form
  over naming a candidate block is what makes this case disappear.

- **L6 — After `R`, the direct rule always fires.** Combining L4 and L5: every
  slot from `R` on is *directly* decided, so the indirect rule is never needed
  after synchrony takes effect.

  This is the right shape for a liveness statement here. Not "something
  eventually commits" but "the machinery for undecided slots stops being
  reachable".

**What this deliberately does not cover.** A Byzantine leader that publishes a
block but shows it to only some validators. That can leave a slot genuinely
undecided — which is exactly why the indirect rule exists, and why M4/M6 are
not made redundant by L6.

## 7. Staging

| | | risk |
|---|---|---|
| L0 | density below the frontier | low — existing lemmas, no new primitives |
| L2 | view-monotonicity of `Decided` | low — mirrors `decided_unique`'s induction |
| L1 | `Live`, then no-stall by induction on rounds | low |
| L3 | L2 plus the synchrony hypothesis | low |
| L4 | `Synchronised`, then the two-layer argument | medium — the only real proof |
| L5–L6 | composition | low |

L0 and L2 come first because neither needs a new primitive: L0 is pure DAG
structure, L2 is pure view reasoning. That defers every modelling decision
until there is already something proved.

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
