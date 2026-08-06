# lean-dag — Equivocation, growth, and denial of service

The denial-of-service extension of the development. Safety and liveness
(`spec.md`, `liveness.md`) already hold under equivocation — `no_equivocation`
constrains correct validators only, and every result is stated against a
universe in which Byzantine validators may publish as many blocks per round
as they like. What they do not address is **storage**: Byzantine validators
flood the DAG, and correct validators must fetch, validate and retain a view
that grows without bound. This document describes the machinery that rules
that out: a validity condition (`DoSValid`), exact bounds on the size of a
block's causal history, and an acceptance-layer budget (the *novelty budget*)
under which liveness and linear storage hold simultaneously — from round 0,
under full asynchrony, from hypotheses a validator can enforce without ever
knowing who is Byzantine.

> **Status.** Everything below is proved in Lean — no `sorry`, axioms
> `propext`, `Classical.choice`, `Quot.sound` only — and witnessed on
> concrete models by `decide`. §8 is the index, mapping every result to its
> Lean name and file. Result labels (D…, B…, C…, S…) are stable identifiers
> cited by the Lean sources.

## Overview — the two conditions, and the two main theorems

A self-contained summary. Everything used here is defined from scratch;
§1–§7 develop it, and §8 maps every result to its Lean name.

**The setting.** There are `3f+1` **validators**, of which at most `f` are
**Byzantine**; the rest are **correct**. The protocol proceeds in numbered
**rounds**. A **block** `b` carries an author (its *creator*), a round,
and a finite set of **references** to earlier blocks. A block is **valid**
when

1. every reference points to a block of the round exactly below;
2. its references carry pairwise distinct authors;
3. they carry at least `2f+1` distinct authors — a **quorum**; and
4. one of them is by `b`'s own author — the **self-parent** — so every
   author's blocks chain back to round 0.

Correct validators author at most one block per round; a Byzantine
validator may **equivocate** — author several blocks at one round. The
universe `U` is every block some correct validator ever held, so `|U|` is
the storage burden on the correct population; blocks revealed to nobody
cost nothing.

The central quantity is a block's **cone** (causal history): `H(b)` is
`b` together with everything reachable from it through references, and
`|H(b)|` is what a validator must fetch and validate in order to accept
`b`. A validator's **view** `V` is the union of the cones of the blocks it
accepted, so views reduce to cones: `|V| ≤ (3f+1) · max |H(b)|` (D2).
Absent any further condition, `|H(b)|` can grow *exponentially* in the
round: each block may name `f` fresh Byzantine blocks one round down, and
the branching compounds level by level.

**Condition 1 — DoS validity.** Say author `X` is **exposed** in `H(b)`
when the cone contains two `X`-blocks at one round — an equivocation made
visible. The condition:

> a block may not reference an author who is exposed in its own cone.

Exposure is objective (any two validators compute it alike, D13),
permanent along references (D12), and *is* the damage rather than a report
of it (D11): an author's equivocation either inflates nobody's cone, or
exposes the author — and then exclusion is automatic and forever. A
correct author is never exposed (D15), so the condition never blocks a
correct validator.

**Theorem A — the bare-model bound** (§5; `card_history_le'` with
`card_history_ge`). Under validity and DoS validity, every block `b` at
round `r` satisfies

> `(2f+1)·r + 1 ≤ |H(b)| ≤ (3f+1 + 3·f^(f+1)) · (r+1)`.

Linear in `r` at every fault budget — the compounding is gone — with a
per-round, per-author constant `1 + 3f·f^(f−1)` (C1′); at `f = 1` the
ceiling is exactly `7(r+1)`. The constant's exponential shape is **final,
not slack**: with `e` exposed authors an author can lawfully run `2^Θ(e)`
chains through one cone, and a family attaining the doubling is
machine-checked (`Udouble`, §5). So no rule keyed on the *shape* of cones
can bring the constant down to a polynomial in `f` — which is what forces
Condition 2 to price something an adversary cannot shape away.

**Condition 2 — the novelty budget.** Measure an arriving block not by its
cone but by what its cone would *newly* bring. Against a validator's
current store `V`, the **novelty** of `b` is `H(b) \ V` — precisely the
download performed to validate `b`, so the measurement is the work itself.
It is antitone in `V`: as the store grows, every block only gets cheaper.
The enforced rule (`UniformBudget T`, for a parameter `T`):

> never accept a block whose novelty exceeds `T` blocks; defer it instead
> — the store grows, and the block is re-priced later.

together with the **reference discipline** (`RefsAccepted`): a block
references exactly what its author accepted. Real DAG protocols do both.
The rule is **author-blind** — nothing in it consults who is Byzantine —
and it never defers a correct block: a correct block's cone is a complete
record of its author's acceptances (the DAG is its own repair channel,
C3′), so a correct block can never cost another correct validator more
than `f·T + 1` (C3″) — a *derived* threshold, not an assumed one.

**Theorem B — DoS resistance** (§6; `dos_resistance`). Assume correct
validators build once they hold a quorum (`Live`), the network eventually
delivers quorums (`DeliversQuorum`), and correct validators enforce the
budget and the reference discipline. Then, simultaneously:

> **liveness** — every correct validator has a block at every round; and
> **linear storage** — every correct validator's view at round `n` obeys
> `|V| ≤ |Correct|·(n+1) + |Correct|·f·(1 + n·T)`,

from round 0, under full asynchrony — no global stabilization time appears
in either hypothesis or conclusion, and no hypothesis consults an
identity. The proof's engine: every Byzantine block in any correct view
entered through *some* correct validator's budgeted acceptance, so the
global Byzantine pool grows by at most `|Correct|·f·T` per round (B4). The
adversary's hidden mass is thereby repriced rather than forbidden: a
`2^e`-block reveal must trickle through `T`-sized acceptances, taking
exponentially many rounds to place, while correct storage grows linearly
throughout.

Read together: exclusion makes Byzantine damage **one-shot per author**
(C2), Theorem A bounds what one shot can weigh inside the DAG, and
Theorem B bounds what any schedule of shots can cost a correct validator —
from conditions each validator can enforce alone, without ever knowing who
is Byzantine.

## 1. The threat, and the two measures

`liveness.md` §4.2 fixes `U` as *every block some correct validator ever
held* — not every block anyone ever wrote. So `|U.ids|` is the storage burden
imposed on the correct population, and a block revealed to nobody costs
nothing. Two quantities measure the burden:

- **View size.** `V.ids` is a `Finset`; `|V.ids|` is what a validator
  stores. Views are downward closed, so a view with maximum round `r` spans
  rounds `0…r`.
- **History size.** `H(b) := {c | Reaches U b c}` — the causal cone of `b`.
  `|H(b)|` is what a validator must fetch and validate in order to accept
  `b`, and it is the quantity the attack inflates.

§2 reduces the first to the second; §5 bounds the second; §6 bounds both at
the point of acceptance. A third quantity, **bandwidth** — blocks received,
inspected and discarded — is invisible to the model: `U` records what was
*held*, and there is no notion of a message. Every bound here is about
storage; the wire-level cap on candidates held is the one piece that lives
at the network layer (§9).

## 2. The acceptance rule, and view size from history size

The rule: *a correct validator accepts at most one block per author at its
latest round, and its view is the causal history of what it accepts.*

```lean
structure Accepted (U) (A : Finset BlockId) (n : ℕ) : Prop where
  subset_ids : A ⊆ U.ids
  round_eq   : ∀ i ∈ A, (U.block i).round = n     -- one round: the frontier
  inj        : ∀ i ∈ A, ∀ j ∈ A, creator i = creator j → i = j
```

`A` is the **frontier**; earlier rounds enter the view inside the histories,
which is what makes `|A| ≤ 3f+1` rather than `(3f+1)(r+1)`. The set is not
invented for the size bound: the delivery layer needs it independently
(`Delivery.accepted`, §7 S2/S5), and `accepted_inj` there is exactly the
injectivity D2 consumes.

- **D1 — a generated view is a view.** `A.biUnion (history U)` is downward
  closed, because a union of causal histories is. No closure obligation is
  discharged by hand.
- **D2 — the bridge.** `|V| ≤ (3f+1) · max_{b ∈ A} |H(b)|`. Unconditional:
  no DoS condition, no synchrony, no correctness hypothesis.
- **D3 — the sharp form.** When the validator references everything it
  accepted, `H(b) = {b} ∪ V`, so `|V| = |H(b)| − 1`. The exposure clause of
  §3 can make `refs` a proper subset; then D2 is the operative bound.
- **D4 — generated views grow**, provided each block references its own
  previous one — which validity now demands of every block (S10). The
  principle that keeps both D3's failure mode and D4 harmless: **exclusion
  governs what you reference, not what you retain** (§7 S1).

What the rule must *not* be read as claiming: `V ≤ (3f+1)(r+1)` "by
construction". A round-`r` block by `w` may reference the other half of an
equivocation than the one this validator accepted, so `V` holds both. The
rule buys the reduction to `|H(b)|`, not the bound — the bound is §5 and §6.

## 3. The DoS validity condition

> If a block's history contains an equivocation by validator `X`, then `X`
> may not be used as one of that block's references.

```lean
/-- `X` is exposed in `b`'s history: two distinct blocks by `X`, one round. -/
def ExposedIn (U) (b : BlockId) (X : Validator) : Prop :=
  ∃ i j, Reaches U b i ∧ Reaches U b j ∧ i ≠ j ∧
    creator i = X ∧ creator j = X ∧ round i = round j

def DoSValid (U) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator
```

**A predicate on the universe, not a field of `ValidWrt`.** As a separate
predicate, every safety and liveness theorem applies verbatim, and the DoS
results take `(hdos : DoSValid U)` as an extra hypothesis — the condition is
available in both regimes at no migration cost.

**Well founded**: the condition on `b` depends only on the histories of
`b`'s references, since `b` is the only block of `H(b)` at its own round.
**Constructible**: as a building rule it converges — drop references naming
exposed authors, recompute; dropping only shrinks the history, exposure is
monotone, so the iteration terminates within `f` rounds and always retains
every correct reference (a correct author is never exposed, D15). A correct
validator can always build.

The three facts that make it a *validity* condition:

- **D11 — inflation is exposure.** For every block `b` and author `X`,
  either `H(b)` holds at most one `X`-block per round — the equivocation
  gained `X` nothing — or `X` is exposed in `H(b)` and `b` may not reference
  `X`. The two are the same sentence read twice: the mechanism does not need
  to *catch* equivocators, because exclusion is automatic exactly where
  damage occurs. In particular the tie-break policy for accepting halves is
  not a security parameter.
- **D12 — exposure is permanent.** `Reaches U c b → ExposedIn U b X →
  ExposedIn U c X`. Exclusion, once earned, is inherited by everything
  downstream.
- **D13 — exposure is view-independent.** The test computed inside any view
  agrees with the test inside `U`, so two correct validators never disagree
  about whether a block is DoS-valid.

The division of labour: the acceptance rule (§2) bounds what a flood can
make you *keep*; `DoSValid` bounds what a reference can make you *fetch*;
bandwidth stays outside (§1).

## 4. Safety and liveness under the condition

**D14 — safety is untouched.** Literally: `DoSValid` is an extra
hypothesis, and no safety result mentions it. Checked mechanically
(`LeanDagTest/SafetyUnderDoS.lean`).

**Exclusion is sound, and priced correctly.**

- **D15.** `ExposedIn U b X → X ∉ Correct` — a correct validator is never
  excluded, by anyone, ever.
- **D15a.** With `k` authors exposed in `H(b)`, `b`'s references must come
  from the other `3f+1−k` validators: each caught equivocator costs exactly
  one unit of fault-tolerance margin, and at `k = f` a block must reference
  every correct block of the round below. This is the intended report, not a
  defect (§7 S8): redundancy falls in exact proportion to *proved*
  misbehaviour.
- **D15b.** The correct set alone always meets the quorum: exclusion can
  never make the threshold unreachable. The pool shrinks; the threshold does
  not — which is what `|Correct| ≥ 2f+1` was always for.

**Liveness.** The delivery layer separates `held` (what arrived — never
deduplicated, §7 S5) from `accepted` (what the validator builds on — one
block per author, forced by `distinct_creators`, §7 S2). Under the
condition, L1 (*no stall*) holds from `R` rather than from round 0 — before
`R` the adversary controls delivery and can hand a validator a quorum of
authors it has just excluded — and after `R` nothing changes: L4 and L6 are
untouched, a correct leader still commits, commits still recur. The chain
that matters end to end: exclusion bites → the correct set still meets
`2f+1` (D15b) → blocks keep being produced → a post-`R` slot with a correct
leader commits. Witnessed in full on `Uexcl` (§8).

**Exclusion after `R` is total.**

- **D16 — agree, or be exposed.** Post-`R` synchrony puts every correct
  round-`n` block into every correct round-`(n+1)` block's references, so
  correct validators either jointly hold one `X`-block per round — `X`
  gained nothing (D11) — or every correct round-`(n+1)` block is exposed to
  `X`.
- **D17 — total and permanent.** Once every correct block of a round is
  exposed to `X`, *no valid block* of any later round may reference `X` —
  Byzantine blocks included, since every valid block leans on `f+1` correct
  blocks of the round below.
- **D18 — pinning.** An author that publishes a round-`j` block to all but
  at most `f` correct validators loses the freedom to disagree about that
  round later.

- **C2 — the rate guarantee.** Every author contributes at most one block
  per round to any history until it is exposed, and nothing afterwards
  (D11 + D19b + D17). The residual damage is **one reveal per Byzantine
  author** (§7 S4): a history built out of sight and delivered by getting a
  single block accepted — the last block ever accepted from that author.
  Bounding the *size* of that reveal is §5; repricing its *delivery* is §6.

## 5. The size of a reveal — the bare-model bounds

The question S4 prices the residual damage by: what is the biggest `|H(b)|`
a round-`r` block can have and stay valid? Without any condition the answer
is exponential — each block references up to `f` fresh Byzantine blocks per
level, and the layer recurrence `m_s ≤ (3f+1) + f·m_{s+1}` compounds. Under
`DoSValid` and validity the answer is **linear in `r` at every `f`**, with a
per-round constant that is exponential in the number of exposed authors —
and that exponential is *attained*, so the bare model's answer is final.

**The per-block facts.**

- **D5 / D6 — the baseline.** Without equivocation
  `(2f+1)r + 1 ≤ |V| ≤ (3f+1)(r+1)`, both ends attained.
- **D7.** A history's top layer below the block is exactly its reference
  set, and carries distinct authors (`distinct_creators`).
- **D8 / D8a.** An equivocation is visible only at a merge, two rounds up —
  the reference graph cannot *report* one earlier — and merges are not luck:
  a validator whose accepted set spans both halves exposes the author in its
  own next block as a matter of course.
- **D19a.** A history containing no equivocation is linear:
  `|H(b)| ≤ (3f+1)(r+1)`.
- **D19b.** A block is clean about every author it references, so the
  blow-up can only come from authors a block does *not* name.

**The self-parent condition (S10).** `ValidWrt` requires every non-genesis
block to reference *some* block by its own creator:

```lean
self_parent : 0 < b.round → ∃ i ∈ b.refs, (blk i).creator = b.creator
```

Real DAG protocols do this anyway, and without it the linear bound is
false: an author that sheds its own past can launder chains through
single-block *carriers*, giving `Θ(r^{⌊f/2⌋+1})` histories at `f ≥ 3` with
every block valid and `DoSValid`. With it (all in `LeanDag/SelfParent.lean`):

- **D20 — chains reach the ground**: a history holds a block by its own
  author at every round below it.
- **D21 — no self-laundering**: no block is exposed to its own author — an
  author whose equivocation is visible in a history can never build on that
  history again.
- **D22 / D23 — exact prices**: a block's own author contributes exactly
  `r+1` blocks to its history; naming another author costs exactly that
  author's chain, `r` blocks.
- **D24 — the floor**: pure validity forces `(2f+1)·r + 1 ≤ |H(b)|`, so the
  question is two-sided and the ceiling below matches the floor's shape.

**The ceiling — C1′, proved at every `f`.** An author's contribution to a
history is `chains × rounds`, and chains are counted by **tops** — the
author's blocks with no same-author child in the cone (`topsOf`,
`LeanDag/Adoption.lean`). An unexposed author has one chain; a namer's
history has room for only one chain of the named author, so distinct tops
need distinct adopting authors (*the adoption collapse*); and iterating
"who adopted the adopter" climbs strictly nested cones — a **pedigree**
(`LeanDag/Pedigree.lean`) — whose author list is duplicate-free and
determines its top. Anchored at the first unexposed adopter, with
`e := |exposedTo U b| ≤ f` exposed authors:

> per exposed author `|topsOf U b X| ≤ (3f+1−e)·e^(e−1)`
> (`card_topsOf_le_of_exposed`);
> per author per round **`c(f) = 1 + 3f·f^(f−1)`**
> (`card_historyBlocksOf_le'`);
> in total **`|H(b)| ≤ (3f+1 + 3f^(f+1))·(r+1)`** (`card_history_le'`) —
> exactly `7(r+1)` at `f = 1`, constant `31` at `f = 2` against a floor of
> `5r+1`.

Under at most one exposed author the constant is `6f+1` (**B1**), and at
`f ≤ 1` the bound is unconditional. Linear in `r` at every fault budget:
no compounding, which is all C1′ ever demanded.

**The exponential in `e` is real — polynomial `c(f)` is impossible.** Two
proved constraints cut the count and pin its shape:

- **D25 — density** (`LeanDag/Density.lean`): a valid block's history
  contains a block by all but at most `f` of the correct validators, at
  every round below it. Cones cannot be selectively blind; the miss budget
  is exactly `f`.
- **Freshness**: a chain may adopt an author only while no chain of that
  author sits anywhere in what it has already gathered. This prunes the
  pedigree tree to `G(m) = m + Σ_{d<m} G(d) = 2^m − 1`.

And the `2^m` is attained: the **doubling family** — an exposed helper
author whose chains each carry a fresh chain of the doubled author to a
different unexposed scaffold — yields `2^(e−2)` chains of a single author
with only `e` exposed authors, in `O(e)` rounds, passing every proved
constraint. The doubling step is **machine-checked** (`Udouble`,
`LeanDagTest/Doubling.lean`): thirteen validators at `f = 4`, the correct
nine advancing rounds referencing only each other, every Byzantine block
referencing seven real correct blocks of the round below as `predecessor`
and `quorum` force, visibility one-way until the reveal; `decide` confirms
validity, `DoSValid`, four chains of validator 1 against the proved ceiling
of 22, and D25's miss budget honoured throughout. So the truth is
`2^Θ(e)`: no acceptance rule on cone *shape* can do better — the way out is
to change what acceptance *costs*, which is §6.

## 6. The novelty budget

The slogan the design keeps returning to: **legislate novelty, prove
size**. Built in `LeanDag/Novelty.lean`, witnessed in
`LeanDagTest/Novelty.lean`.

**The shape of the hidden mass.** Per block, the doubling family is
unimpeachable — rounds contiguous, quorums full, every cone clean about
what it names. What is anomalous is where the mass sits *relative to the
observer*: the excess blocks are old, and appear in no block any correct
validator has ever held. The reveal delivers them at once — against the
correct view, `Udouble`'s reveal carries fifteen novel blocks where a
correct tip carries one. The signature is **novelty at depth**, and novelty
is relative to an observer: no intrinsic predicate on a block can see it.
Rules on cone shape fail outright: a chain-count cap convicts the *forced*
merge of `Utwin` (quorum leaves a correct block no choice but to reference
both halves' carriers), and a size cap convicts a correct block at the
boundary. So the rule is observer-relative:

```lean
/-- What accepting `b` would newly bring into the view `V`. -/
def novelty (U) (V : Finset BlockId) (b : BlockId) : Finset BlockId :=
  history U b \ V
```

Novelty is the fetch a validator performs anyway to validate `b` — the rule
prices work it is already forced to do — and it is **antitone in the view**
(`novelty_anti`): a deferred block only ever gets cheaper, so deferral is a
rate limiter, never a permanently wrong verdict.

**The telescope (D26, pure DAG).** If each block of a correct author adds
at most `κ'` over its self-parent (`StepNovelty`), the whole history is
linear: `|H(b)| ≤ κ'·r + 1` — no schedule, no network, nothing but S10's
descent. Tight on `Udouble`: correct chains step by exactly `2f+1 = 9` and
`|H(30)| = 9·2+1`.

**The budget, two forms.** `viewUpto D v n` accumulates
`Delivery.accepted` with whole histories — the retained view of S1. The
budget caps acceptances, in two sandwiching formulations:

- `ByzBudget D κ` — the **analysis side**: only Byzantine-authored
  acceptances need cost `≤ κ`. The creator guard is bookkeeping (assume
  only what is enforced, prove the rest), never something a validator
  evaluates.
- `UniformBudget D T` — the **mechanism side**: every acceptance costs
  `≤ T`, author-blind. This is the rule a validator actually runs.

`UniformBudget T → ByzBudget T` (dropping a guard weakens nothing), and
post-`R` a `ByzBudget κ` schedule is uniformly budgeted at `f·κ + 1` with
no guard (`uniform_of_byzBudget`) — equivalent up to one factor of `f`, the
exact price of author-blindness, paid in constants and never in theorems.

**C3 — no correct block is ever over budget.** The liveness half, in three
steps:

- **C3a.** After `R`, a block built from `w`'s acceptances costs any
  correct `v` at most one plus the **view gap** toward `w`
  (`viewGap D v w n := viewUpto D w n \ viewUpto D v n`;
  `card_novelty_le_viewGap_add_one`). The adversary's hidden mass appears
  in neither term.
- **C3′ — the gap collapses.** The repair mechanism the design once
  thought it needed already exists inside `Delivery`: `includes` puts every
  round's acceptances among the next block's references, and the
  self-parent chain carries every earlier round forward, so **a correct
  validator's block is, in its cone, a complete record of everything its
  author ever accepted** (`viewUpto_subset_history`). One such block
  delivered post-`R` erases the standing gap; what remains is one round of
  Byzantine budget: `gap ≤ f·κ`, constant
  (`card_viewGap_succ_le_of_block`). The DAG is its own repair channel.
- **C3″ — the correct clause is derived.** A validator enforcing only the
  Byzantine clause never meets a correct block costing more than
  **`Κ = f·κ + 1`** (`card_novelty_le_of_byzBudget`). The hysteresis
  threshold for counting peers' blocks is a theorem to cite, not a
  parameter to guess — which is what makes the contagion attack (defer a
  correct block, eject its author, lose quorum) impossible: enforcing the
  budget never defers a correct block.

The one hypothesis this chain takes beyond `Delivery` is `RefsAccepted` —
`refs ⊆ accepted`, the converse of `includes`, D3's ordinary case.

**Storage.** Two bounds, one per synchrony regime:

- **B3′** (post-`R`, `card_viewUpto_le_of_byzBudget`): the view grows by at
  most `|Correct|·(f·κ+1) + f·κ` per round after `R`.
- **B4** (unconditional, `card_viewUpto_le_of_refsAccepted`): the pre-`R`
  base is itself linear, with **no synchrony at all**. Every Byzantine
  block in any correct view entered through *some* correct validator's
  budgeted acceptance — a direct acceptance is priced `≤ κ`, and a block
  arriving inside a correct block's cone was already in that block's
  author's earlier view (`RefsAccepted`), hence already in the pool. The
  global Byzantine pool (`byzPool`, `card_byzPool_le`) grows by at most
  `|Correct|·f·κ` per round from round 0, the correct part counts itself
  at one block per author per round (`no_equivocation`), and

  > `|V_v(n)| ≤ |Correct|·(n+1) + |Correct|·f·(1 + n·κ)`

  holds under full asynchrony. **DoS resistance is not a post-GST
  property**: the adversary gains nothing from network delays.

**The headline.** `dos_resistance` (and the post-`R` incremental form
`dos_resistance'`) state liveness and linear storage **simultaneously**,
from enforceable conditions only. The hypothesis audit:

- `Live` — local conduct: build once you hold a quorum, start at genesis;
- `DeliversQuorum` — L1's minimal network assumption, asynchrony-safe;
- `UniformBudget T` — local conduct: never accept anything costing more
  than `T` novel blocks, whoever signed it;
- `RefsAccepted` — local conduct: reference only what you accepted.

No hypothesis consults `Correct`, `byzantine`, or any identity. The two
conclusions never compete: liveness needs no Byzantine block (D15b), and by
C3″ the enforced rule defers no correct one. The doubling family is not
forbidden but **repriced**: a `2^e` cone can no longer arrive in one
reveal — it must trickle through budgeted acceptances, at most `f`
Byzantine authors per round, so placing it takes exponentially many rounds
while correct storage grows linearly throughout.

**Operationally** (not formalized — the model has no clocks): the round
timer counts only budget-eligible blocks toward `2f+1`, so a deferred block
never stalls it and after `R` correct tips alone satisfy it; the fetch
timer pulls unknown ancestors up to the budget and defers past it, with
re-checks event-driven and monotone; commit and leader timers are
untouched — the mechanism sits entirely below the commit rule.

## 7. Design notes

Decisions in force, with the rationale that keeps them from being
relitigated. Labels are cited by the Lean sources.

**S1 — views retain whole histories, and the two sizes compose.** The
acceptance rule constrains the accepted set, not the view; generated views
retain the full histories of what was accepted (fetching `H(b)` to validate
*is* the storage); self-reference keeps them monotone; and exclusion
governs what you reference, never what you retain — a validator keeps what
it accepted even after the author is excluded, which D2 prices regardless.

**S2 — the acceptance rule is forced, not chosen.** `distinct_creators`
makes referencing both halves of an equivocation impossible, so a validator
holding two blocks by one author must pick one. The storage argument and
the validity argument arrive at the same rule independently.

**S3 — no evidence channel.** A reporting relation alongside the universe
was considered and rejected: D11 removes the motivation (exposure *is* the
damage, not a punishment that must fire), post-`R` it is redundant (D16),
pre-`R` it cannot work (disjoint deliveries leave nothing to report), and
it would cost four fields and a behavioural obligation. Revisit only if
accountability — proving misbehaviour to third parties, slashing — becomes
a goal in its own right.

**S4 — one reveal per Byzantine author.** The residual damage under the
condition: an author may build a history out of sight and reveal it by
getting one block accepted — the last block ever accepted from it (D12,
D17). §5 bounds the reveal's size; §6 reprices its delivery. The damage is
one-shot, never recurring.

**S5 — `held` is what arrived; `accepted` is what you build on.** `held`
stays undeduplicated — `U` is defined as every block some correct validator
held, and deduplicating at the delivery layer would put the second half of
an equivocation outside `U`, making every result here vacuous in exactly
the case it is about. The choice of which block to accept is left
unspecified, like the timeout; by D11 it is not a security parameter.

**S6 — `history` is a `Finset` by fuel, not by `filter`.** Counting needs
a `Finset`; `Reaches` is `ReflTransGen` with no free decidability; and
well-founded recursion fails because `U.block` is junk off `U.ids`. Fuel
indexed by the round is structural and computable, `decide` works on the
witnesses, and one lemma (`mem_history_iff`) makes the representation
faithful. Layer arguments go through `mem_history_succ_iff` rather than
unfolding the fuel by hand.

**S7 — `Delivery` requires self-reference** for correct validators, which
keeps generated views monotone (D4). For validity purposes S10 subsumes it.

**S8 — exclusion is by author, and the cost is the point.** Each caught
equivocator costs one unit of fault-tolerance margin (D15a), accepted as
intended behaviour: an author proved Byzantine is not one anybody should
build on, and liveness survives regardless (D15b). L1 holds from `R`
instead of round 0, which is where commits live anyway.

**S9 — the forward-looking variants, rejected.** *"Never reference a block
whose history exposes anyone"* is fatal: every correct block normally
acquires an equivocation in its history (D8a), so the DAG stops. *"Exclude
per-round twins"* loses permanence (D12/D17) and turns one reveal per
author into one per author per round. Rules that penalize cone *shape*
convict correct blocks — the same fact that drives §6's design.

**S10 — the self-parent condition.** Every non-genesis block references
*some* block by its own creator — "some", not "the": an equivocator's
blocks form a forest, and forcing uniqueness would smuggle in a
non-equivocation assumption. Real protocols already behave this way; the
model was more permissive than the thing it models, and that permission
alone made super-linear histories constructible (§5). A strengthening of
validity, so every theorem survives verbatim.

**S11 — the budget lives at the acceptance layer, and `Κ` is a theorem.**
The rule is observer-relative because the doubling family has no intrinsic
signature. It is a predicate over `Delivery` (`ByzBudget`/`UniformBudget`),
not a validity condition — validity stays objective (D13) and every
existing theorem survives. Deferral, never rejection, because novelty is
antitone. The enforced form is guard-free: no mechanism in the development
ever branches on `Correct`, and the hysteresis threshold is derived (C3″),
not assumed. `RefsAccepted` is the one modelling hypothesis on the C3 side
— a candidate `Delivery` field if it earns more use.

## 8. Results

Every result with its Lean name. `LeanDag/` holds the theory,
`LeanDagTest/` the witnesses; the whole development builds with no `sorry`
and the usual three axioms.

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
| **D8a** | exposure is structural, not accidental | `exposedIn_of_accepted_span` | `Exclusion` |
| **D11** | inflation *is* exposure | `not_exposedIn_iff_card_le_one`, `card_le_one_or_not_mem_refs` | `Exposure` |
| **D12** | exposure is permanent | `ExposedIn.mono`, `ExposedIn.of_mem_refs` | `Exposure` |
| **D13** | exposure is view-independent | `exposedIn_iff_of_view` | `Exposure` |
| **D14** | safety is untouched | *(inert-hypothesis checks)* | `LeanDagTest/SafetyUnderDoS` |
| **D15** | exclusion is sound | `ExposedIn.not_correct` | `Exposure` |
| **D15a** | the margin is `f − k`, and zero at the bound | `card_creators_refs_add_card_exposedTo_le`, `creators_refs_eq_correct` | `Exposure` |
| **D15b** | the correct set alone meets the threshold | `correctBlocksAt_admissible_quorum` | `Exclusion` |
| **D16** | after `R`, agree or be exposed | `exposedIn_of_correct_disagree` | `Exclusion` |
| **D17** | exclusion is total and permanent | `exposedIn_of_correct_exposed`, `not_mem_creators_refs_of_correct_exposed` | `Exclusion` |
| **D18** | pinning | `mem_history_of_pinned` | `Exclusion` |
| **D19a** | a clean history is linear | `card_history_le_of_not_exposed` | `Counting` |
| **D19b** | a block is clean about what it references | `card_filter_creator_le_of_mem_refs` | `Counting` |
| — | the intersection lemma | `exists_shared_correct_ref`, `eq_of_both_name_of_shared` | `Exclusion` |
| — | the backbone lemma | `mem_history_of_correct` | `Exclusion` |
| — | nothing published is invisible to the correct | `exists_accepted_of_mem_ids` | `Exclusion` |
| — | the condition is implementable | `not_exposedIn_refs_of_policy` | `Exclusion` |
| — | the quorum is derivable after `R` | `card_creators_accepted_of_eventuallyDelivers` | `Exclusion` |
| **C2** | the rate guarantee: one block per round until exposure, then none | D11 + D19b + D17 | — |
| **D20** | chains reach the ground | `exists_self_ancestor` | `SelfParent` |
| **D21** | no self-laundering | `not_exposedIn_self_creator` | `SelfParent` |
| **D22** | the self price: exactly `r + 1` | `card_historyBlocksOf_self`, `card_filter_self_creator` | `SelfParent` |
| **D23** | the reference price: exactly `r` | `card_historyBlocksOf_of_mem_refs`, `card_filter_creator_of_mem_refs` | `SelfParent` |
| **D24** | the floor: `(2f+1)·r + 1 ≤ \|H(b)\|` | `card_history_ge` | `SelfParent` |
| — | unexposed means one chain | `mem_history_of_creator_eq_of_not_exposedIn` | `Adoption` |
| — | tops: chains made countable | `topsOf`, `exists_top_of_mem_history`, `card_filter_creator_le_card_topsOf` | `Adoption` |
| — | the adoption collapse | `top_eq_of_mem_namer_history`, `card_topsOf_le` | `Adoption` |
| **B1** | unique-equivocator bound: `\|H(b)\| ≤ (6f+1)(r+1)` | `card_history_le_of_unique_equivocator`, `…_of_card_exposedTo_le_one` | `Adoption` |
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
| — | the budget, both forms | `ByzBudget`, `UniformBudget`, `UniformBudget.byzBudget` | `Novelty` |
| **C3a** | post-`R` cost of a correct block: one plus the gap | `viewGap`, `card_novelty_le_viewGap_add_one` | `Novelty` |
| **C3′** | the gap collapses: `≤ f·κ`, constant after `R` | `viewUpto_subset_history`, `card_viewGap_succ_le_of_block` | `Novelty` |
| **C3″** | the correct clause is derived: `Κ = f·κ + 1` | `ByzBudget`, `card_novelty_le_of_byzBudget` | `Novelty` |
| **B3′** | linear storage from the enforceable rule alone | `RefsAccepted`, `card_viewUpto_le_of_byzBudget` | `Novelty` |
| — | the capstone: liveness ∧ storage, one hypothesis set | `no_stall_and_card_viewUpto_le` | `Novelty` |
| **B4** | unconditional linear storage: no synchrony, from round 0 | `byzPool`, `card_byzPool_le`, `card_viewUpto_le_of_refsAccepted` | `Novelty` |
| — | the capstone, asynchronous | `no_stall_and_card_viewUpto_le'` | `Novelty` |
| — | the sandwich converse: uniform at `f·κ+1` post-`R` | `uniform_of_byzBudget` | `Novelty` |
| — | **the headline**: DoS resistance from enforceable conditions only | `dos_resistance`, `dos_resistance'` | `Novelty` |

Supporting definitions: `history` and `mem_history_iff` (S6, `History`);
`ExposedIn`, `DoSValid`, `EquivPair` (`Exposure`); `Accepted`
(`Acceptance`); `EquivFree`, `atRound` (`Counting`); `viewUpto`, `viewGap`,
`byzPool` (`Novelty`). The predicates are decidable, so the witnesses
settle by `decide`.

**The witnesses** — house rule: a definition gets a witness before anything
is proved from it, and the definitions here are easy to satisfy vacuously,
so each model is built to be non-vacuous in the way that matters.

- **`Umerge`** (`LeanDagTest/Exposure`, `f = 1`): validator 0 equivocates,
  is exposed at the merge, and is debarred from being referenced while
  retaining a perfectly valid block no later block may name. `U6` is the
  foil — an equivocation nobody built on, never exposed; `U3` pins D5 tight.
- **`Uexcl`** (`LeanDagTest/Exclusion`): the liveness chain end to end —
  exposure at round 2, the three correct validators (zero margin) carry the
  DAG alone and **still commit**, with D15a applied by theorem rather than
  assumed.
- **`Ufault`** (`LeanDagTest/Pedigree`, `f = 2`): both Byzantine validators
  exposed at once — the multi-equivocator regime C1′ covers with no
  hypothesis beyond `DoSValid`.
- **`Utwin`** (`LeanDagTest/Density`, `f = 1`): two chains of one author
  inside a *correct* validator's history at the minimum fault budget — two
  correct validators adopt the two halves while spending their D25 miss
  budget on excluding each other. The anchor factor is not slack, and the
  merge is quorum-forced: the witness that kills cone-shape acceptance
  rules.
- **`Udouble`** (`LeanDagTest/Doubling`, `f = 4`): the doubling step of
  §5's lower-bound family, machine-checked — four chains of one author,
  `4 = 2^e`, under full validity and `DoSValid`, with the Byzantine
  structure parasitic on the real correct DAG throughout.
- **`Dtwin`** (`LeanDagTest/Novelty`): `Utwin`'s delivery schedule. It
  satisfies the author-blind `UniformBudget Dtwin 3` — the dearest
  acceptance prices the missed genesis *and* the equivocation half riding
  in on a correct carrier — and the sharp `ByzBudget Dtwin 0`; carries
  `Live`, `DeliversQuorum` and `RefsAccepted` instances; and every §6
  theorem applies on it: the gap is exactly the accepted Byzantine half
  `{0}`, C3′ collapses it, C3″ prices the merge block at exactly
  `f·κ + 1 = 1`, `byzPool = {0, 4}` frozen forever at `κ = 0`, and both
  capstones and the headline `dos_resistance` apply in single terms. On the
  `Udouble` side: the reveal costs **15 novel blocks** where a correct tip
  costs 1 — every `κ ∈ [1, 14]` defers the reveal and never a correct
  block — and absorbing one branch drops the price to 8: antitone, on data.

## 9. What remains

- **The wire-level cap on `held`.** The budget governs what is *accepted*;
  `held` — candidate blocks arrived from the network — is deliberately
  unbounded and undeduplicated in the model (S5). Flood resistance of the
  delivery layer itself is a statement about messages, not blocks, and was
  always going to live at the network layer. It is the only piece of the
  DoS story outside the development.
- **The quantitative gap in the bare-model constant.** `2^(e−1)` chains are
  constructible, `(3f+1−e)·e^(e−1)` is proved; closing to `2^(e−1)` needs
  set-determinism of anchored pedigrees (top determined by the *set* of
  pedigree authors, not the list), which resisted proof. Tightness only —
  the budget supersedes the constant in practice.
- **Reconfiguration.** Once `k` validators are permanently excluded, the
  system runs a `(3f+1−k)`-committee on quorums sized for `f` — tolerating
  `f−k` but paying for `f` (D15a). The principled response is to shrink the
  committee; the results here give the precondition (live long enough to
  commit, and a commit is what a reconfiguration needs), but formalizing
  the handover is separate work and would want `Faults` parameterized by a
  committee.
- **Accountability.** Proving misbehaviour to third parties (slashing) is
  a different objective from bounding storage (S3) and would want evidence
  in the block payload rather than beside the universe.
