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

> **Status.** The core is **proved**: G1 (`LeanDag/Chop.lean` — the
> operator, universe laws, one-way `DoSValid`), G2 and the per-slot heart
> of G3 (all six verdict invariances including the indirect test
> `CertifiedIn`), G13/G14/G5/G6 (`LeanDag/Window.lean` — windowed
> novelty, store correspondence, liveness transfer, and the
> bounded-storage headline `card_retained_le`), and both halves of G10
> (`LeanDag/AttestedBase.lean`). Witnessed by `decide` in
> `LeanDagTest/Chop.lean`: the `Uexcl` commit surviving the cut verbatim,
> the statute of limitations vanishing an exposure (and surviving *at*
> the cut), the G6 constant on `Dtwin`, and `Base Utwin 1 0 = {1,2,3}` —
> the sandwich tight at the bottom, both equivocation halves filtered.
> One deviation from the plan, in our favour: the slot-schedule
> correspondence of §2 was **not needed** for any of this — the entire
> Mysticeti rule layer (`certificates`, `DirectCommit`, `DirectSkip`,
> `CertifiedIn`) is round-indexed and schedule-free, so G2/G3 close
> without touching `Slots`. The schedule enters only at the
> `Decided`-over-slots level (G3/G4 in the M6/L3 idiom), which remains,
> along with G6b/G7 statements, G8/G9 (policy), G11/G12, and P9.

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
indexed by `Slots` (leader per slot, `slotRound`, 3-round spacing). A node
that recomputed leaders from *rebased* rounds would assign different
leaders than the network, and every cross-node verdict comparison would be
garbage. Nor can `chop` simply keep absolute rounds: the base layer's
emptied references would then violate `quorum` (genesis-emptiness is
*derived* from `predecessor` at round 0 and does not generalize to round
`G` for free). The resolution: rebase the universe, **carry the offset** —
define the induced schedule `slotRound' k = slotRound (k + k₀) − G` for
`k₀` the first slot at or above `G`, and state every cross-node claim in
absolute terms through the correspondence `k ↦ k + k₀`. One induced
definition, one correspondence lemma, settled in P1; this is also the
likeliest place G2's "mechanical" reputation fails, so it gets a decided
witness early.

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
  totality**: the pruner must not discard a slot whose output it still
  owes the application. A1 is a policy-layer invariant (§6), not a
  hypothesis of the safety transfer. It is also *dischargeable*: the
  pipelining results already prove that a committed run decides
  everything below it (`all_decided_below_of_fairRun`), so post-`R` the
  frontier below a commit is total.
- **(A2) Lag bound.** `G` trails the validator's current round by a
  margin `Λ`. **(review)** The first draft justified `Λ` by "the commit
  window and the indirect-anchor reach" — wrong on the second count: the
  indirect anchor sits *above* its slot, so anchor reach never looks
  below the cut. What `Λ` actually buys: (i) the **peer-frontier skew** —
  do not prune what a slower correct peer's undecided slots still window
  over, bounded post-`R` by the commit lag (G8); (ii) the **attestation
  lag** of the certified base (G11). Whether these are one constant is
  Q3.

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
  `DoSValid U → DoSValid (chop U G)` should be a lemma of G1. The failure
  of the converse direction *is* the statute of limitations, below.

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
"full history available to all". The replacement claim, to be proved: for
everything the protocol still *does* — validate new blocks, decide slots,
stay live, bound storage — the truncated universe is as good as the full
one.

## 4. Safety above the horizon

**(review) The right level for invariance is views, not `U`.** `U`
contains held-but-never-accepted blocks (S5 keeps `held` undeduplicated),
which no correct validator retains or serves — a certificate held once and
accepted by nobody counts in a `U`-level verdict but is unobtainable by
any syncing node, GC or no GC. The existing machinery already has the
right idiom for this: decisions are **view-relative and monotone** (L2),
**never conflicting** across views (M6), and **propagating** (L3). The
invariance targets are stated in that idiom:

- **G1 (truncation is a universe).** `chop U G` satisfies `complete`,
  `valid`, `no_equivocation`; `DoSValid U → DoSValid (chop U G)`; and the
  induced schedule with its slot correspondence `k ↦ k + k₀` (§2).
  Immediate consequence: every existing theorem holds of `chop U G`.
- **G2 (verdict invariance, per view).** For a slot with proposer round
  `r ≥ G`: `supporters`, `certificates`, `blames`, `DirectCommit`,
  `DirectSkip` computed in a truncated view agree with the same view
  untruncated, through the slot correspondence. Window-locality does the
  work; the index bookkeeping is where mistakes would hide, so every
  lemma gets a decided instance on the P0 witness.
- **G3 (decision invariance, per slot).** Direct and indirect verdicts
  for slots `≥ G` agree between a view and its truncation. Stated
  **per slot**, not as a claim about a sweep procedure: the direct
  verdict is window-local, and the indirect verdict is a property of the
  anchor's cone, also entirely above the slot. (If the Lean form of the
  indirect rule turns out to consult earlier slots' verdicts, the
  fallback shape is induction over slot indices `≥ k₀` with the
  checkpoint as base — Q4.) A1 is *not* a hypothesis here (§2).
- **G4 (heterogeneous horizons).** For correct `v, w` with horizons
  `G_v ≤ G_w`: on slots `≥ G_w` their verdicts never conflict and
  eventually agree — M6/L3 relativized through G3 twice. Nodes need not
  share a horizon; they need each horizon admissible and the skew
  bounded (G8).

Safety needs no new quorum argument anywhere: it inherits T0/T3/M-series
through G1, and G2–G4 are locality and correspondence bookkeeping.

## 5. Liveness, storage, and the cost of joining

- **G5 (liveness transfer).** A `Delivery` for `U` induces a `Delivery`
  for `chop U G` (drop everything below `G`); `Live` and `DeliversQuorum`
  transfer; hence L1 (`no_stall`) holds in the truncated universe, and the
  post-`R` commit chain (L4, L6) with it, with the usual `R`-offsets.
- **G13 (windowed novelty).** The definition of §3 with its cut-advance
  monotonicity law. Prerequisite to everything below.
- **G14 (store correspondence).** Pruning a store below `G` yields
  exactly the `viewUpto` of the induced delivery on `chop U G`:
  `viewUpto D v t ∩ [G, ∞) = viewUpto (chop D G) v (t − G)`. The bridge
  between "what a validator retains" and "B4 on the truncated universe".
- **G6 (bounded storage — the headline).** Stated **per time**, because a
  validator's life is a sequence of cuts, not one: at each `t`, with
  admissible horizon `G(t) ≥ t − Λ`, the retained store is (G14) the
  truncated view, and B4 on `chop U G(t)` at rebased round `≤ Λ` gives
  > `|retained| ≤ |Correct|·(Λ+1)·(1 + f·T)`-shaped — **constant in `t`**,
  with G13 guaranteeing the sequence of prunings never un-prices anything.
  The DoS story ended at "linear forever"; the GC story ends at
  "constant, at lag `Λ`".
- **G6b (bounded join).** The same constant bounds what a joining
  validator must fetch: the attested base plus the window — GC bounds
  **sync cost**, not just storage. Half the point of the exercise, and it
  deserves its own statement.
- **G7 (relay obligation, windowed).** The no-amplification story of the
  DoS doc survives with "your block's cone" replaced by "your block's
  cone above `max(G_v, G_w)`": a correct validator serves at most the
  window; everything below is the base's job. Floods are still dampened
  at acceptance; now the *honest* obligation is bounded too.

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
  (`all_decided_below_of_fairRun`); A2 by the margin. Skew: decisions are
  final (M-series), shared where shared (M6), and propagating (L3), so
  post-`R` two correct frontiers differ by at most the commit lag, which
  L6 (commits recur) bounds. No agreement protocol; the DAG's own commits
  are the synchronizer.
- **The common-core rule** (depth-based). Post-`R`, the backbone lemma
  puts every correct block of round `m` inside every correct cone from
  `m+1` on, and D25 (density) says even Byzantine-authored blocks cannot
  be selectively blind below any valid block. So "everything `Λ` rounds
  deep is in every correct validator's cone" is a *theorem*, and a
  validator may set `G_v := t − Λ` knowing no correct peer in the L1
  envelope still lacks what it discards. **The rule's safety is exactly
  coextensive with that envelope**: post-`R`, round skew ≤ 1; any
  validator outside it — partitioned, crashed, joining — is by definition
  on the bootstrap path below.

The two rules bound different things (frontier: decidedness; depth:
universality of possession) and the admissible horizon is their minimum.

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
is all rebasing needs: window completeness holds after one propagation
lag, verdicts above the cut are view-local (G2), and extra fringe is
inert and bounded. Bases need not agree, exactly as horizons need not.
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

- **G8 (skew).** Post-`R`, admissible horizons of correct validators under
  either rule differ by a bounded amount (commit lag, resp. round skew).
- **G9 (no desync).** A correct validator never *needs* a block below any
  correct peer's admissible horizon, except at bootstrap — where the
  attested base suffices. (This is the formal content of "slightly
  different horizons are fine".)
- **G10 (the sandwich).** Post-`R`, `C ⊆ Base U t G ⊆` the round-`G`
  layer of the union of correct cones — completeness from the backbone,
  soundness from `f+1`-implies-a-correct-attester.
- **G11 (window completeness).** With the attestation round one
  propagation lag above `G`, every round-`G` block referenced by a
  surviving window block is in `Base` — rebasing on `Base` restores
  `complete` for the obtainable window. The proof route is three existing
  theorems composed: acceptance puts the block in a correct store, the
  relay (C3′) puts it in every correct store within a round, and
  `viewUpto_subset_history` lifts stores into own-block cones — i.e.,
  into attestations. The scope — blocks in *accepted* cones — is exactly
  the obtainable window of §4, which is the right scope.
- **G12 (bootstrap safety).** Rebasing on *any* base satisfying the G10
  sandwich yields slot verdicts that never conflict with any correct
  validator's and eventually agree (compose G10–G11 with G2–G4): inexact
  certificates, exact decisions.

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
  consensus-sized.

**Open questions**, recorded before they are argued about:

- **Q1 — epoch coupling.** Should the budget parameter `T` and the lag
  `Λ` be related? A forgiven author re-enters at budget rate; `Λ` sets how
  often forgiveness can recur. The product `Λ·f·T` may be the right
  "adversary work per epoch" quantity, and P9 should say so or refute it.
- **Q2 — checkpoint content.** For the DAG machinery the attested base
  *is* the checkpoint (P8 settles the DAG side, no signatures needed).
  What remains out of scope is application state — the ledger prefix a
  joining node also wants — a different object with different trust
  requirements; "bootstrap" for a full node means both.
- **Q3 — one `Λ` or two.** A2 now names two distinct roles for the lag:
  peer-frontier skew (G8) and attestation lag (G11). Are they the same
  constant, and should `Base` be pinned to `t = G + Λ`? Likely resolvable
  inside P8, but the answer shapes G8's statement.
- **Q4 — the indirect rule's true shape.** G3's per-slot statement
  assumes the Lean indirect verdict does not consult earlier slots'
  verdicts. P0 checks this against the actual definition before P4
  commits to a statement; the fallback induction is recorded in G3.
