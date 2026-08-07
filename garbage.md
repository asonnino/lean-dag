# lean-dag — Garbage collection: bounding the DAG

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Design notes and plan for garbage-collecting the DAG. Results use
**G**-labels (G1, G2, …), continuing the house scheme. The document has
been through two design-review passes; their findings are folded in below
rather than kept as errata, with the items that changed the design marked
**(review)**.

> **Status: every G-label is proved and witnessed.** G1 (`LeanDag/GC/Chop.lean`
> — the operator, universe laws, one-way `DoSValid`), G2 and per-slot G3
> (all six verdict invariances including the indirect test `CertifiedIn`),
> G13/G14/G5/G6 (`LeanDag/GC/Window.lean` — windowed novelty, store
> correspondence, liveness transfer, the bounded-storage headline
> `card_retained_le`), G3/G4 at the full `Decided` level
> (`LeanDag/GC/ChopDecided.lean` — `View.chop`, the induced schedule
> `Slots.chop`, `decided_chop` by structural induction both ways, and the
> cross-cut agreement `decided_agree_chop` for **arbitrary** joiner
> views), G10 both halves (`LeanDag/GC/AttestedBase.lean`), G11/G6b/G7/G12
> (`LeanDag/GC/Bootstrap.lean` — `accepted_mem_base`, `card_joinIds_le`,
> `card_serve_le`, `joinView`/`bootstrap_agree`), and G8/G9
> (`LeanDag/GC/Horizon.lean` — the composition law `chop_chop`,
> heterogeneous-horizon agreement, and the one-round universal-possession
> depth bound). Witnessed by `decide` throughout `LeanDagTest/GC/Chop.lean`,
> `LeanDagTest/GC/Bootstrap.lean` (which gives `Uexcl` its delivery
> schedule `Dexcl`) and `LeanDagTest/GC/Horizon.lean`; the G11 witness sits
> exactly on the `t = m + 2` boundary.
>
> Two deviations from the plan, both recorded in module docs. In our
> favour: the slot-schedule correspondence was **not needed** for the
> rule layer — `certificates`/`DirectCommit`/`DirectSkip`/`CertifiedIn`
> are round-indexed and schedule-free; `Slots` enters only at `Decided`,
> where the induced-schedule correspondence went through cleanly (Q4
> resolved: the indirect rule consults anchors only through their cones).
> Against the prose: G8's promised "frontiers differ by at most the
> commit lag" has no carrier in a round-synchronous model with static
> views — the model's exact content is agreement + composition + the
> one-round depth bound, and the timing constant lives with `R` in
> `liveness.md`. P9's resolution is in §8 below.

## 1. The problem

The DoS results end at *linear* storage: under the novelty budget a correct
validator's view obeys `|V_v(t)| ≤ |Correct|·(t+1) + |Correct|·f·(1+t·T)`
(B4) — linear in the round `t`, and that is optimal for what it claims,
since correct production alone is `|Correct|` blocks per round. But linear
still diverges. A validator that runs for years retains years of history,
and a joining validator must fetch it. Eventually storage — and sync time —
is exhausted not by an adversary but by the protocol's own health.

What we want is **bounded storage**: retain a *window* of the DAG and
discard the prefix. This collides with two load-bearing properties of the
current model:

- **Completeness / downward closure.** `BlockUniverse.complete` says every
  referenced block is present; `View.complete` closes views downward; a
  block's cone `H(b)` reaches round 0 (D20 — self-parent chains reach the
  ground). Pruning any prefix falsifies all three as stated.
- **Cone-validity.** `ValidWrt`, `DoSValid` and `ExposedIn` are properties
  of cones. A validator that discarded the prefix cannot recompute them for
  the discarded rounds — and, more subtly, cannot recompute *exposure*
  whose witnessing pair sits below the cut (§3).

One scoping fact to keep straight throughout: **GC bounds *stores*, not
`U`.** The universe — every block some correct validator ever held — keeps
growing as an analysis object; the theorems below live at the level of what
a validator retains (`viewUpto`) and what a joiner must fetch.

So garbage collection is a genuine model change, the third one after S10
(self-parent) and the novelty budget: a **horizon** `G`, a round below
which stores need not retain blocks and sync need not deliver them,
together with theorems that commit safety and commit liveness survive
above it.

## 2. The horizon, and truncation

The design variable: a round `G` (per validator: `G_v`), the **horizon**.
Below it, nothing is retained, requested, or served. The model-side
counterpart is a **truncation operator**:

> `chop U G` — the universe whose blocks are those of `U` at rounds `≥ G`,
> with rounds rebased by `−G` and the (rebased) round-0 blocks' reference
> sets emptied.

The rebasing is the key move: **the round-`G` layer becomes the new
genesis layer.** All four validity clauses then hold of `chop U G` exactly
as they hold of `U` — `predecessor`, `distinct_creators`, `quorum` and
`self_parent` constrain only rounds `> 0`, and the old round-0 special
case (`refs_empty_of_round_zero`) applies verbatim to the new base. This
is why truncation can be an *operator producing a bona-fide
`BlockUniverse`* rather than a weakening of `complete` threaded through
every proof: every existing theorem — safety, liveness, counting, the
budget — applies to `chop U G` **unchanged**, because `chop U G` is just
another universe. The work is not re-proving the theory above the cut; it
is relating verdicts across the cut, and choosing the cut.

**(review) Rebasing must not touch the slot schedule.** Verdicts are
indexed by `Slots` (leader per slot, `slotRound`). A node that recomputed
leaders from *rebased* rounds would assign different leaders than the
network, and every cross-node verdict comparison would be garbage. Nor
can `chop` simply keep absolute rounds: the base layer's emptied
references would then violate `quorum` (genesis-emptiness is *derived*
from `predecessor` at round 0 and does not generalize to round `G` for
free). The resolution as built: rebase the universe, **carry the
offset** — the induced schedule is `Slots.chop S G d hd`
(`ChopDecided.lean`), re-indexed from a base slot `d` whose round clears
the horizon (`hd : G ≤ slotRound d`), with
`slotRound' k = slotRound (d + k) − G`, and every cross-node claim
stated in absolute terms through the correspondence `k ↦ d + k`. Two
things turned out better than planned. The rule layer
(`supporters`/`certificates`/`DirectCommit`/`DirectSkip`/`CertifiedIn`)
is round-indexed and **never consults the schedule**, so all of G2 and
per-slot G3 closed with no correspondence at all; the schedule enters
only at the `Decided` level, where the correspondence
(`decided_chop`) went through by structural induction with the
base-slot condition as the *only* premise. And the base-slot condition
is what makes keying survive: `G ≤ slotRound d` pins the rebased rounds
above zero, where subtraction is faithful.

**Model versus implementation.** `chop` *edits* the base-layer blocks
(empties their reference sets). In a real system a block's identity is a
hash over its references, so this is not a re-hash of history: it is the
checkpoint *reinterpreting* those ids as opaque geneses. The model's block
map makes this a definition; an implementation makes it a rule about what
the sync layer serves.

Two invariants make a horizon *admissible* for a validator:

- **(A1) Decided below.** Every leader slot with proposer round `< G` is
  decided (committed or skipped) in the validator's view. **(review)**
  Note what A1 is *for*: not verdict invariance — verdicts for slots
  `≥ G` are window-local and invariant regardless (§4) — but **ledger
  totality**: a slot's verdict reads rounds `slotRound k` through `+2`,
  so pruning above an undecided slot discards its certificates and the
  slot can never be decided — the ledger stalls below the validator's
  own cut. A liveness-of-output failure, never a safety one. A1 is a
  policy-layer invariant (§6), not a hypothesis of the safety transfer —
  none of `decided_chop`/`decided_agree_chop`/`bootstrap_agree` assumes
  it. It is also *dischargeable*: a committed run decides everything
  below it (`all_decided_below_of_fairRun`), so post-`R` the frontier
  below a commit is total.
- **(A2) Lag bound.** `G` trails the validator's current round by a
  margin `Λ`. **(review)** The first draft justified `Λ` by "the commit
  window and the indirect-anchor reach" — wrong on the second count: the
  indirect anchor sits *above* its slot, so anchor reach never looks
  below the cut. What `Λ` actually buys is now proved, and it is two
  **completeness** properties, not safety: the one-round possession
  bound of the depth rule (G9, `Λ ≥ 1`) and the attestation lag of the
  certified base (G11, `Λ ≥ 2`, tight on data). The full accounting of
  what constrains `Λ` — and what does not — is §6's *lag envelope*.

## 3. What breaks, what bends, what holds

An honest inventory against the existing development.

**Holds without change (after rebasing).**
- The commit rules are **round-local**: votes at `r+1`, certificates at
  `r+2`, `DirectCommit`/`DirectSkip` read a three-round window, and the
  indirect rule consults an anchor *above* its slot. Nothing in a verdict
  for slot `r` looks below `r`.
- L1/production is one-round-local (references point one round down);
  L4/L6 operate in the slot window. Liveness never reaches below the cut.
- `DoSValid` transfers to `chop U G` **one-way**: cones shrink under
  truncation, so exposure shrinks, so the per-block condition weakens —
  `DoSValid U → DoSValid (chop U G)` is proved (`dosValid_chop`). The
  failure of the converse direction *is* the statute of limitations,
  below, and the witness file makes it visible on data.

**Bends #1 (review — a contradiction in the first draft): the budget
must be windowed.** The first draft claimed the novelty budget is
"horizon-friendly by construction". It is not — as stated it is
*anti*-friendly: novelty is antitone in the store, so pruning `V` below
`G` makes every arriving block's `H(b) \ V` **explode** with the entire
discarded prefix, and the budget would defer every correct block forever.
The repair is to measure novelty **on the truncated universe**:

> windowed novelty := `novelty (chop U G) V b` = `(H(b) ∩ [G, ∞)) \ V`

— the fetch never descends below the horizon, which is the entire point
of GC. This must be a definition with its own law (**G13**): windowed
novelty is *monotone under cut-advance* — for `G' ≥ G`,
`novelty_{G'} = novelty_G ∩ [G', ∞) ⊆ novelty_G` — so as the window
slides, **pruning only cheapens blocks**: an affordable block never
becomes unaffordable, and deferral decisions never flip the wrong way.
Without G13 the bounded-storage headline (G6) is unprovable as first
stated.

**Bends #2: exposure below the horizon — the statute of limitations.**
`ExposedIn` needs the witnessing pair — two same-author blocks at one
round. If the equivocation round falls **strictly below** `G`, the pair
is gone: in `chop U G` the author is not exposed, and `DoSValid` no
longer forbids referencing it. Exclusion permanence (D12, D17) is a
statement about `U`; truncation **forgives**. A precision worth having:
the statute applies strictly below the cut — a pair *at* round `G`
survives into the base layer (base blocks keep round and creator), and
later cones containing both halves are still exposed. Three responses,
in order of preference:

1. **Accept it, and let the budget be the backstop.** C2's "one reveal per
   author, ever" weakens to **one reveal per author per GC epoch** — the
   author must first rebuild a self-parent chain from the *new* genesis
   layer (D20 rebased), in public, under the windowed budget, which prices
   every block of the comeback. Forgiveness is a bounded-rate phenomenon,
   not a cliff. And its blast radius is confined by an existing theorem:
   **commit safety never depended on `DoSValid` at all** (D14), so the
   statute of limitations touches only the DoS-storage layer — never
   safety.
2. **Tombstones** — carry the exposed set across the cut as explicit
   state. Rejected on the same grounds as the evidence channel (S3): it is
   state *beside* the DAG, needs its own agreement and its own GC, and
   response 1 makes it unnecessary for storage purposes. Revisit only if
   accountability becomes a goal.
3. **Hold `G` below live exposures.** Unworkable: it hands the adversary
   veto power over GC — equivocate once and your evidence must be retained
   forever, which is the unbounded growth we set out to remove.

**Breaks, by design, and is replaced.** Global downward closure and
"full history available to all". The replacement claim, now proved: for
everything the protocol still *does* — validate new blocks (G1), decide
slots (`decided_chop`), stay live (`live_chopD`), bound storage
(`card_retained_le`) — the truncated universe is as good as the full
one.

## 4. Safety above the horizon

**(review) The right level for invariance is views, not `U`.** `U`
contains held-but-never-accepted blocks (S5 keeps `held` undeduplicated),
which no correct validator retains or serves — a certificate held once and
accepted by nobody counts in a `U`-level verdict but is unobtainable by
any syncing node, GC or no GC. The existing machinery already has the
right idiom for this: decisions are **view-relative and monotone** (L2),
**never conflicting** across views (M6), and **propagating** (L3). The
results, in that idiom — each marked with where it lives:

- **G1 (truncation is a universe) — proved** (`Chop.lean`). `chop U G`
  satisfies `complete`, `valid`, `no_equivocation`;
  `DoSValid U → DoSValid (chop U G)` (`dosValid_chop`). Immediate
  consequence: every existing theorem holds of `chop U G`.
- **G2 (verdict invariance) — proved** (`Chop.lean`,
  `ChopDecided.lean`). For a slot at rebased round `s` (original round
  `G + s`): `supporters_chop`, `blames_chop`, `certificates_chop`,
  `directCommit_chop`, `directSkip_chop`, and the indirect test
  `certifiedIn_chop` — plus the view-relative forms
  (`certificatesIn_chop`, `directCommitIn_chop`, `directSkipIn_chop`)
  against the truncated view `View.chop`. Window-locality does all the
  work, and no slot correspondence was needed at this level: the rule
  layer is round-indexed and schedule-free.
- **G3 (decision invariance) — proved, at both levels.** Per slot as
  planned, and then for the **full decision relation**: `decided_chop`
  (`ChopDecided.lean`) — a validator re-running Mysticeti on the
  truncation from its truncated view decides slot `k` exactly as it
  decided slot `d + k` on the full universe, by structural induction
  through anchors and intermediate skips, both directions. The Q4
  fallback was never needed: the indirect verdict consults its anchor
  only through the anchor's cone. The only premise is
  `G ≤ slotRound d` — no synchrony, no liveness, and A1 is *not* a
  hypothesis (§2).
- **G4 (heterogeneous horizons) — proved, stronger than stated.** The
  target said "never conflict and eventually agree"; the theorem
  (`decided_agree_chop`) gives outright **equality of verdicts**, and
  for an **arbitrary** view of the truncation — not a truncated
  full-history view. That asymmetry matters: a joiner's view is never
  `V.chop` for any full-history `V` (lifted to `U` it would not be
  downward closed), so `decided_unique` is played *inside* the
  truncation against a truncated view, and `decided_chop` carries the
  verdict across the cut. Cross-horizon agreement `G_v ≠ G_w` is
  `decided_agree_horizons` (§6).

Safety needs no new quorum argument anywhere: it inherits T0/T3/M-series
through G1, and G2–G4 are locality and correspondence bookkeeping — the
counting was never redone.

## 5. Liveness, storage, and the cost of joining

- **G5 (liveness transfer) — proved** (`Window.lean`). A `Delivery` for
  `U` induces a `Delivery` for `chop U G` (`chopD`, drop everything
  below `G`); `DeliversQuorum` transfers (`deliversQuorum_chopD`),
  `Live` transfers with the horizon offset (`live_chopD`), hence L1
  holds in the truncated universe (`populated_chop`), and the post-`R`
  commit chain with it.
- **G13 (windowed novelty) — proved** (`Window.lean`). The definition of
  §3 with its cut-advance monotonicity law (`history_chop_anti`,
  `novelty_chop_anti`): as the window slides, pruning only cheapens
  blocks. Prerequisite to everything below.
- **G14 (store correspondence) — proved** (`viewUpto_chopD`). Pruning a
  store below `G` yields exactly the `viewUpto` of the induced delivery
  on `chop U G`:
  `viewUpto (chopD D G) v m = (viewUpto D v (G+m)).filter (G ≤ round ·)`.
  The bridge between "what a validator retains" and "B4 on the truncated
  universe".
- **G6 (bounded storage — the headline) — proved**
  (`card_retained_le`). Stated **per time**, because a validator's life
  is a sequence of cuts, not one: at each `t` with `G ≤ t ≤ G + Λ`, the
  retained store `(viewUpto D v t).filter (G ≤ round ·)` obeys
  > `|retained| ≤ |Correct|·(Λ+1) + (|Correct|·f + Λ·|Correct|·f·κ)`
  — **constant in `t`**, under `ByzBudget κ` and `RefsAccepted`
  (mechanism-side, instantiate `κ` through the budget sandwich of the
  DoS doc), with G13 guaranteeing the sequence of prunings never
  un-prices anything. The DoS story ended at "linear forever"; the GC
  story ends at "constant, at lag `Λ`".
- **G6b (bounded join) — proved** (`base_subset_retained`,
  `card_joinIds_le`). Sharper than planned: the joiner's *entire* fetch —
  attested base plus window (`joinIds`) — is a **subset of one correct
  peer's retained store**, so the same G6 constant bounds sync cost, not
  just storage.
- **G7 (relay obligation, windowed) — proved**
  (`history_chop_subset_retained`, `card_serve_le`). What a correct
  author can be asked to serve for its block — the block's truncated
  cone — is its **own retained store above its own horizon, plus the
  block itself** (`RefsAccepted` one step down, S10 the rest of the
  way): the G6 constant plus one. Floods are still dampened at
  acceptance; now the *honest* obligation is bounded too, and
  everything below the cut is the base's job.

## 6. Setting the horizon without consensus

The traditional design runs consensus on `G` itself: after a commit, all
correct validators agree on a GC round. That works, but it is worth
resisting: **we do not need horizons to be equal — we need each to be
admissible, and the skew to be bounded.** G4 already makes heterogeneous
horizons safe. Two local rules, not exclusive:

- **The commit-frontier rule.** `G_v :=` (the largest round such that
  every slot below it is decided in `v`'s view) `− Λ`. A1 holds by
  construction — and is *supplied* post-`R` by the pipelining theorem
  that a committed run decides everything below it
  (`all_decided_below_of_fairRun`); A2 by the margin. On skew, the model
  is more honest than the first draft: "two correct frontiers differ by
  at most the commit lag" is a statement about *clocks*, and this model
  is round-synchronous with static views — the constant has no carrier
  here. What the model proves instead is that skew **does not need
  bounding for correctness**: verdicts at different horizons are equal
  outright (`decided_agree_horizons`), and different horizons compose
  (`chop_chop` — a deeper cut is just another cut, so validators at
  different `G` sit on one tower of truncations, never in incomparable
  worlds). No agreement protocol; the DAG's own commits are the
  synchronizer, and the timing constant lives with `R` in `liveness.md`.
- **The common-core rule** (depth-based). Proved sharper than stated:
  possession universalises in **one** round, not `Λ` —
  `viewUpto_subset_viewUpto_succ` (post-`R`, everything *any* correct
  validator retains by round `m` is in *every* correct store by `m+1`),
  so a validator may set `G_v := t − Λ` for any `Λ ≥ 1` knowing no
  correct peer in the L1 envelope still lacks what it discards
  (`pruned_subset_peer_store`). **The rule's guarantee is exactly
  coextensive with that envelope**: any validator outside it —
  partitioned, crashed, joining — is by definition on the bootstrap path
  below.

The two rules bound different things (frontier: decidedness; depth:
universality of possession) and the admissible horizon is their minimum.

**The lag envelope — what actually constrains `Λ`.** Collecting the
proved facts in one place, because the answer is easy to misremember:
*safety constrains `Λ` not at all*; every restriction is a completeness
or cost statement, each pinned to its theorem.

| bound | source | what breaks below it |
|---|---|---|
| — (any `G` is safe) | `decided_chop`, `decided_agree_chop`, `bootstrap_agree` | nothing — commit safety carries no lag hypothesis at all; its only premise is `G ≤ slotRound d` |
| `Λ ≥ 0` vs the *decided* frontier | A1 / `all_decided_below_of_fairRun` | ledger totality: a slot reads rounds `slotRound k … +2`, so cutting above an undecided slot discards its certificates and the slot is undecidable forever — output stalls, safety unharmed |
| `Λ ≥ 1` | G9, `viewUpto_subset_viewUpto_succ` | no-desync among correct peers: possession universalises in exactly one round, so at `Λ = 0` a peer may still lack what you discard |
| `Λ ≥ 2` | G11, `accepted_mem_base` (`t ≥ m + 2`, tight on data) | base completeness for joiners: below it, an accepted round-`G` block can be missing from the attested base and a window block dangles — the `Dexcl` witness realises this at `t = m + 1` |
| upper bound: none | G6/G6b/G7 constants | nothing breaks; storage, join cost and relay obligation grow **linearly in `Λ`** (`|Correct|·(Λ+1) + |Correct|·f + Λ·|Correct|·f·κ`), so the ceiling is appetite, not correctness |

One further consideration that is a trade-off, not a restriction: `Λ` is
the epoch length of the statute of limitations (§8). Smaller `Λ`
forgives exposed equivocators sooner; the budget prices every re-entry
either way. The practical envelope is therefore
**`2 ≤ Λ ≤` storage appetite** — everything below 2 loses a
completeness property, never a safety one.

**Where a residue of agreement genuinely lives: bootstrap — and the
inexact certificate that dissolves most of it.** A validator so far behind
that its needs predate every peer's horizon cannot fetch the prefix — it
must adopt the new genesis layer from others. Demanding `f+1` *identical*
checkpoints would be wrong: correct validators' layers share the correct
core exactly (backbone) but differ in the Byzantine fringe, so honest
presenters need never match block-for-block. The right primitive is the
**inexact certificate**, filtered per block:

> attest the layer, keep what `≥ f+1` distinct authors attest.

Post-`R` each correct attestation is `C ∪ B_v` — the **shared correct
layer** `C` (identical across correct validators, `|C| ≥ n−f`, by the
backbone; one block per correct author by T1) plus a varying Byzantine
fringe. Among any `n−f` attestations, `≥ n−2f ≥ f+1` are correct and each
contains all of `C`, so nothing of `C` is filtered out; conversely
anything surviving the filter has a correct attester, hence lies in a
correct cone, hence (relay, C3′) in *every* correct cone within a round.
The certified base is therefore **sandwiched** —
`C ⊆ Base ⊆` (the layer of the union of correct cones) — and the sandwich
is all rebasing needs: window completeness holds two rounds above the
window frontier (`t ≥ m + 2`, one round for the carrier, one for the
backbone — tight on data), verdicts above the cut are view-local (G2),
and extra fringe is inert and bounded. Bases need not agree, exactly as
horizons need not.
Two further precisions from review: the fringe may contain **several
same-author blocks** — harmless, since `no_equivocation` constrains
correct authors only, and the witnesses already carry Byzantine
multi-geneses (`Udouble`); and when both halves of a round-`G`
equivocation circulated, **both clear the filter**, so the certificate
*preserves* boundary exposure — the statute of limitations is mitigated
at the cut itself.

Better still, **no signatures are needed even here**: in this model a
validator's attestation *is its block* — its cone is its objective,
checkable (D13), unforgeable statement of what the layer contains. The
certificate is definable DAG-internally and decidably:
`Base U t G := { y at round G : y lies in the cones of round-t blocks by
≥ f+1 distinct authors }`, with the guarantee side supplied by `n−f`
authors *having* round-`t` blocks (Populated) rather than by collecting
messages. Equivocating attesters cost nothing — the filter counts
distinct authors, and `f+1` authors always include a correct one
(`exists_correct_of_card`). A joiner adopts a specific pair `(t, G)`; the
protocol detail of choosing it (presenters may offer different cuts) is
recorded in P8.

- **G8 (heterogeneous horizons) — proved as composition + agreement**
  (`Horizon.lean`). The planned "differ by a bounded amount" was a clock
  statement with no model carrier (see the deviation note in the status
  block); what is proved is stronger where it matters:
  `chop_chop : chop (chop U G₁) (G₂−G₁) = chop U G₂` — every pair of
  horizons is related by the one operator — and
  `decided_agree_horizons` — validators truncated at *different*
  horizons, holding arbitrary views of their truncations, decide every
  shared slot (matched through the absolute index `d₁+k₁ = d₂+k₂`)
  identically.
- **G9 (no desync) — proved** (`viewUpto_subset_viewUpto_succ`,
  `pruned_subset_peer_store`). Post-`R`, possession universalises in
  one round, so a correct validator never *needs* a block below any
  correct peer's admissible horizon (`Λ ≥ 1`), except at bootstrap —
  where the attested base suffices. This is the formal content of
  "slightly different horizons are fine".
- **G10 (the sandwich) — proved** (`AttestedBase.lean`). Post-`R`,
  `C ⊆ Base U t G ⊆` the round-`G` layer of the union of correct
  cones — completeness from the backbone (`correct_mem_base`),
  soundness from `f+1`-implies-a-correct-attester
  (`exists_correct_attester_of_mem_base`). Witness: `Base Utwin 1 0 =
  {1,2,3}`, the shared correct layer exactly, both equivocation halves
  filtered.
- **G11 (window completeness) — proved, with a sharper scope**
  (`accepted_mem_base`). *Every* round-`G` block a correct validator
  accepted into its window by `m` — not merely those referenced by
  surviving window blocks — is in the base attested at any `t ≥ m + 2`,
  and the bound is tight on data. The proof route is the three existing
  theorems composed, as planned: acceptance puts the block in a correct
  store, the store rides into its keeper's next block
  (`viewUpto_subset_history`), and the backbone
  (`mem_history_of_correct`) carries that block into every correct
  round-`t` cone — a cone *is* an attestation. The scope — blocks in
  *accepted* cones — is exactly the obtainable window of §4.
- **G12 (bootstrap safety) — proved, as equality** (`joinView`,
  `bootstrap_agree`). The joiner's assembly — base as genesis layer plus
  a correct peer's window strictly above the cut — is a bona-fide
  `View` of `chop U G` (downward closure is the content: window
  references above the cut stay in the window; references *at* the cut
  are exactly the G11 blocks), and any decision reached from it equals
  any full-history validator's — not "never conflicts, eventually
  agrees" but outright equality. Inexact certificates, exact
  decisions.

## 7. The plan

House rule as always: every definition gets a witness before anything is
proved from it. Phases, with their dependencies; P8 (attested base) is
independent of P4 (the hard phase) and can run in parallel.

- **P0 — witnesses for the cut** *(no dependencies)*. `chop Uexcl 2`
  computed concretely: the post-exclusion DAG re-based, its round-2 layer
  as geneses; `decide` that it is a universe and that the surviving slot
  verdicts match **through the slot correspondence**. The negative
  witness: `chop Umerge` above the equivocation round, where validator 0
  is *no longer exposed* — the statute of limitations on data. Settles
  computability: `chop` as a `Finset`-level operator, fuel-based
  `history` under rebasing, and the induced schedule all `decide`. Also
  checks Q4 against the actual indirect-rule definition.
- **P1 — the operator (G1)** *(after P0)*. `chop U G : BlockUniverse`,
  the universe laws, the one-way `DoSValid` transfer, and the induced
  schedule with its correspondence lemma. Design decisions settled here:
  rebasing versus a genesis-round parameter in `ValidWrt` (rebasing
  preferred; the parameter threads through everything), and the schedule
  offset (carried, never recomputed).
- **P2 — windowed novelty (G13, G14)** *(after P1; prerequisite for
  storage)*. The windowed measure, cut-advance monotonicity, and the
  store correspondence. Small, but G6 is unprovable without it — the
  phase the first review pass added.
- **P3 — verdict invariance (G2)** *(after P1)*. View-relative,
  window-local, through the correspondence; decided instances on the P0
  witness for every lemma.
- **P4 — decision invariance (G3, G4)** *(after P3; the hard phase)*.
  Per-slot direct and indirect verdicts; heterogeneous horizons in the
  M6/L3 idiom. The fallback for an unruly indirect rule: induction over
  slot indices with the checkpoint as base.
- **P5 — liveness transfer (G5)** *(after P1; independent of P3–P4)*.
  Induced `Delivery`, transferred `Live`/`DeliversQuorum`, `no_stall` and
  the commit chain on `chop`.
- **P6 — bounded storage and join (G6, G6b, G7) — the headline**
  *(after P2, P5)*. The per-time statement over the sliding cut; the
  same constant for join cost; the windowed relay obligation.
- **P7 — horizon policy (G8, G9)** *(after P4; A1 discharged post-`R` by
  `all_decided_below_of_fairRun`)*. The commit-frontier and common-core
  rules, admissibility, skew, no-desync; the `(t, G)` adoption detail
  for joiners.
- **P8 — the attested base (G10–G12)** *(after P1, P3; parallel to
  P4–P7; uses the backbone, relay, and `viewUpto_subset_history`
  as-is)*. `Base` as a DAG-internal decidable definition; the sandwich;
  window completeness via the three-theorem composition; bootstrap
  safety. Witness: `Base` on truncated `Uexcl`/`Utwin` at two
  attestation samples, a fringe block surviving in one collector's base
  and not the other's, verdicts agreeing regardless — and a boundary
  equivocation whose both halves clear the filter.
- **P9 — the forgiveness ledger** *(last; after P6, P8)*. What survives
  of C2/D17 across epochs — one reveal per author per GC epoch — with
  the windowed budget backstop (B4/B5 on `chop`), and the D14 note that
  safety never depended on any of it. Doc updates throughout;
  `dos-equivocation-and-growth.md` §9's "wire-level residue" gains a
  sibling: the GC residue is bootstrap sampling, `f+1`-sized, not
  consensus-sized. **Resolved in §8** — no new theorems were needed,
  and the Q1 product turned out to be a term the G6 constant already
  carries.

**Open questions**, recorded before they were argued about — now all
settled; answers inline:

- **Q1 — epoch coupling. Answered: yes, and the product is already in
  the proved constant.** A forgiven author re-enters at budget rate, and
  the per-epoch price of that re-entry is exactly the third term of the
  G6 bound: `Λ·(|Correct|·(f·κ))` — one lag window's worth of budgeted
  Byzantine freight, per correct store. "Adversary work per epoch" is
  not a new quantity to bound; it is the constant `card_retained_le`
  already carries. See §8.
- **Q2 — checkpoint content.** For the DAG machinery the attested base
  *is* the checkpoint (P8 settled the DAG side, no signatures needed).
  What remains out of scope is application state — the ledger prefix a
  joining node also wants — a different object with different trust
  requirements; "bootstrap" for a full node means both. This stays a
  scope boundary, not an open problem.
- **Q3 — one `Λ` or two. Answered: two roles, both proved, one covers
  the other.** The attestation lag is `t ≥ m + 2` — two rounds above the
  window frontier, and the G11 witness sits exactly on that boundary.
  The possession lag of the depth rule is **one** round
  (`viewUpto_subset_viewUpto_succ`). Any `Λ ≥ 2` serves both; `Base`
  need not be pinned to `t = G + Λ` — every `t ≥ m + 2` works — and G8
  needed no lag constant at all in-model (its content is agreement plus
  the composition law).
- **Q4 — the indirect rule's true shape. Answered favourably, twice.**
  The rule layer never consults `Slots` (per-slot G2/G3 closed
  schedule-free), and at the `Decided` level the indirect verdict
  consults its anchor only through the anchor's *cone* — so the induced
  schedule correspondence (`Slots.chop`, `decided_chop`) went through by
  structural induction with no fallback needed.

## 8. The forgiveness ledger (P9)

What survives of the exclusion economy across epochs, and why nothing
new needed proving.

**Within an epoch, everything survives.** `chop U G` is a bona-fide
`BlockUniverse` and `DoSValid` crosses the cut (`dosValid_chop`), so the
entire D-series applies to the truncation *verbatim*: exposure anywhere
in the window debars for the rest of the window (D12), at most `f`
authors are ever exposed (C2), exclusion lands only on the guilty (D15).
No theorem is re-proved; the truncation is just another universe.

**Across a cut, forgiveness is one-way and priced.** The statute of
limitations (`LeanDagTest/GC/Chop.lean`) forgives exactly the equivocations
whose witnessing pair falls strictly below the cut — a pair *at* the cut
survives, and the attested base *preserves* boundary exposure (both
halves of a circulated round-`G` equivocation clear the `f+1` filter).
To be debarred again, a forgiven author must equivocate **again, inside
the new window**: one reveal per author per epoch is the maximum
forgiveness rate. And the re-entry is not free — the windowed budget
backstop (`byzBudget_chopD`, `refsAccepted_chopD`, feeding
`card_retained_le`) prices a forgiven author's freight exactly as it
prices a fresh author's: `Λ·f·κ` per correct store per epoch, the Q1
product, already sitting in the G6 constant.

**And safety never depended on any of it** (the D14 note, restated for
GC): commit safety is quorum arithmetic; exclusion and forgiveness are a
DoS-layer economy. The cross-cut safety results (`decided_chop`,
`decided_agree_chop`, `bootstrap_agree`) carry **no** exclusion, budget,
or exposure hypothesis — their only premise is the base-slot condition
`G ≤ slotRound d`. A world that forgives every equivocation still
commits the same blocks; it just stores more junk.
