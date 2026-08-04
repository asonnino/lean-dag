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

**(b) Correct validators wait for the leader.** Distinct from (a), and
pulling the other way: (a) says build as soon as you can, (b) says delay until
the leader's block is in hand. Without (b), correct validators race ahead
under perfect synchrony and never vote for the leader, so nothing commits.
With (a) alone, liveness of *rounds* holds but liveness of *commits* does not.

In the round-indexed framing below, (b) is absorbed into `Synchronised`:
saying a correct round-`(r+1)` block references every correct round-`r` block
*is* the statement that it waited.

## 4. Framing: rounds as the clock

**(assumption)** No wall-clock time, and **no Δ**. Δ would force views
indexed by an instant and every statement quantified over instants, for no
proof content — the theorems are *"all will commit"* and *"never gets
stuck"*; Δ is a performance claim on top. Flag if the quantitative bound is
wanted, since it changes the whole model.

**(assumption)** GST is a **round**, not a time. Write `Synchronised U R` for

> from round `R` on, every correct validator's round-`(n+1)` block references
> every correct validator's round-`n` block.

This is what eventual DAG synchrony delivers *once rounds are advancing*, and
it is the formal content of "after GST".

**A subtlety that forces the round index.** One might hope to avoid GST
entirely by working in the *limit* universe — the DAG as it eventually
becomes — and saying every correct block references everything from the round
below. That is **false**, and instructively so: a block's references are
fixed when it is built, not in the limit. A correct validator builds its
round-`(r+1)` block as soon as it holds 2f+1 round-`r` blocks, which is
generally before all of them have arrived. Convergence of *views* does not
retroactively enlarge *blocks*.

So the limit universe is still the right carrier — "eventually X" becomes "X
holds in `U`", with no clock — but synchrony has to be indexed by the round
from which it holds.

## 5. Definitions

```lean
/-- The protocol behaviour liveness needs, as properties of the limit
universe. Not derivable from the DAG structure: `Correct` is a negative
condition, and these are positive. -/
structure Live (U : BlockUniverse Validator BlockId Payload) where
  genesis : ∀ v ∈ Correct, ∃ b ∈ U.ids,
    (U.block b).creator = v ∧ (U.block b).round = 0
  builds  : ∀ r, 2 * F.f + 1 ≤ (authorsAt U r).card →
    ∀ v ∈ Correct, ∃ b ∈ U.ids,
      (U.block b).creator = v ∧ (U.block b).round = r + 1

/-- From round `R` on, correct blocks reference every correct block of the
round below — the formal content of "after GST", and the place where the
waiting rule (§3b) lives. -/
def Synchronised (U : BlockUniverse Validator BlockId Payload) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ (Correct : Finset Validator) → a ∈ (U.block b).refs
```

## 6. The results

- **L1 — No stall.** Every correct validator has a block at every round.

  Induction on `r`. Base is `genesis`. For the step, the induction hypothesis
  puts every correct validator in `authorsAt U r`, and there are at least
  `2f+1` correct validators, so `builds` applies. Needs **no synchrony
  assumption at all** — it is the notes' *"from round 0 onwards, always"*.

  This is where `card_correct` (`2f+1 ≤ |Correct|`) finally gets used. `spec.md`
  §2 has carried it as unused-but-kept-for-liveness since the beginning.

- **L2 — Decisions are monotone in the view.** If `V ⊆ V'` then
  `Decided U V k v → Decided U V' k v`.

  Induction on the derivation. `DirectCommitIn` and `DirectSkipIn` are both
  monotone — intersecting the certificate or blame set with a larger view can
  only grow the creator set — and the indirect cases follow inductively.

  Worth having independently of liveness: combined with M1 it says a
  validator **never revises a decision** as its view grows. The safety results
  so far say decisions do not *conflict*; they do not say decisions do not
  *change*.

- **L3 — Commit propagation.** If one correct validator decides slot `k`,
  every correct validator eventually reaches the same decision.

  L2 plus eventual DAG synchrony, which supplies `V ⊆ V'`. This is the notes'
  first bullet with Δ dropped.

- **L4 — A correct leader commits.** If `Synchronised U R` and
  `R ≤ slotRound k` and `leader k` is correct, then its block is directly
  committed.

  Every correct round-`(r+1)` block references `L` by synchrony, so the
  supporters include all correct validators — at least `2f+1`. Every correct
  round-`(r+2)` block then references all of *those*, so its `votesIn` has
  `2f+1` distinct correct creators and it certifies `L`. Since there are
  `2f+1` correct validators, `DirectCommit` follows.

- **L5 — An absent leader is skipped.** If `leader k` has no round-`slotRound k`
  block, the slot is decided `none`.

  Nearly free, and it vindicates a C1 decision: `Decided.directSkip` takes the
  premise `∀ L, IsLeaderBlock U k L → DirectSkipIn U V L …`, which is
  **vacuously true** when the leader published nothing. Choosing the `∀` form
  over naming a candidate block is what makes this case disappear.

- **L6 — After `R`, the direct rule always fires.** Combining L4 and L5:
  every slot from `R` on is *directly* decided, so the indirect rule is never
  needed after GST.

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
| L1 | `Live`, then no-stall by induction on rounds | low |
| L2 | view-monotonicity of `Decided` | low — mirrors `decided_unique`'s induction |
| L3 | L2 plus the synchrony hypothesis | low |
| L4 | `Synchronised`, then the two-layer argument | medium — the only real proof |
| L5–L6 | composition | low |

L2 is worth doing first regardless: it is independently useful, it needs no
new primitives, and its induction is the same shape as `decided_unique`, which
is already working.

## 8. Open questions

1. **Is Δ load-bearing?** §4 drops it. If the quantitative bound matters, the
   time model comes back and should be scoped separately.
2. **Should `Live` be a class or an explicit structure argument?** `Faults` is
   a class and that worked; but liveness hypotheses are the kind of thing one
   wants to see in a signature.
3. **Is `builds` the right rule?** It says a correct validator builds once
   *any* 2f+1 validators have round-`r` blocks. A real implementation waits
   for 2f+1 blocks *it has received*, which in the limit is the same, but the
   two differ if we ever move off the limit framing.
4. **Do we want L1 unconditionally**, or only after `R`? As stated it holds
   from round 0 with no synchrony, which is stronger and matches the notes —
   but it does assume correct validators never stop.
