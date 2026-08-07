# lean-dag — Garbage collection: bounding the DAG

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Design notes and plan for garbage-collecting the DAG. Nothing here is
proved yet; this document fixes the problem, the design, the interactions
with the existing development, and the phased plan. Results will use
**G**-labels (G1, G2, …), continuing the house scheme.

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

So garbage collection is a genuine model change, the third one after S10
(self-parent) and the novelty budget: a **horizon** `G`, a round below
which views need not retain blocks and sync need not deliver them, together
with theorems that commit safety and commit liveness survive above it.

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

Two invariants make a horizon *admissible* for a validator:

- **(A1) Decided below.** Every leader slot with proposer round `< G` is
  decided (committed or skipped) in the validator's view. GC never
  discards an open question.
- **(A2) Lag bound.** `G` trails the validator's current round by at least
  a fixed margin `Λ` (covering the commit window and the indirect-anchor
  reach), so all live machinery operates strictly above the cut.

## 3. What breaks, what bends, what holds

An honest inventory against the existing development.

**Holds without change (after rebasing).**
- The commit rules are **round-local**: votes at `r+1`, certificates at
  `r+2`, `DirectCommit`/`DirectSkip` read a three-round window, and the
  indirect rule consults an anchor at `≥ r+3` whose relevant cone content
  sits at `≥ r`. Nothing in a verdict for slot `r` looks below `r`.
- The backward sweep of the indirect rule descends only through
  **undecided** slots — and (A1) says there are none below `G`. New
  commits never need the pruned prefix.
- L1/production is one-round-local (references point one round down);
  L4/L6 operate in the slot window. Liveness never reaches below the cut.
- The novelty budget is horizon-friendly by construction: `novelty` is
  measured against the retained store, and B4's accounting applies to
  `chop U G` as to any universe — which is precisely where bounded storage
  will come from (§5).

**Bends: exposure below the horizon — the statute of limitations.** This
is the one real casualty, and it should be faced rather than papered over.
`ExposedIn` needs the witnessing pair — two same-author blocks at one
round. If the equivocation round falls below `G`, the pair is gone:
in `chop U G` the author is *not exposed*, and `DoSValid` no longer
forbids referencing it. Exclusion permanence (D12, D17) is a statement
about `U`; truncation **forgives**. Three responses, in order of
preference:

1. **Accept it, and let the budget be the backstop.** C2's "one reveal per
   author, ever" weakens to **one reveal per author per GC epoch** — the
   author must first rebuild a self-parent chain from the *new* genesis
   layer (D20 rebased), in public, under the novelty budget, which prices
   every block of the comeback. Forgiveness is then a bounded-rate
   phenomenon, not a cliff: the B4/B5 arithmetic on `chop U G` caps what a
   forgiven author can cost exactly as it capped the original.
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

The target theorems, in dependency order:

- **G1 (truncation is a universe).** `chop U G` satisfies `complete`,
  `valid`, `no_equivocation`. Immediate consequence: *every* existing
  theorem holds of `chop U G`.
- **G2 (verdict invariance).** For a slot with proposer round `r ≥ G`:
  `supporters`, `certificates`, `blames`, `DirectCommit`, `DirectSkip`
  computed in `chop U G` agree with `U` (after rebasing). The proofs
  should be mechanical: each notion quantifies over a bounded round window
  above `r`, and `chop` is the identity there.
- **G3 (decision invariance).** Given (A1) — all slots below `G` decided —
  the full decision relation (direct and indirect, including the backward
  sweep) agrees between `U` and `chop U G` on slots `≥ G`. This is the
  commit-safety transfer: **pruning never flips or un-decides a slot
  above the horizon.**
- **G4 (heterogeneous horizons).** For correct `v, w` with admissible
  `G_v ≤ G_w`: verdicts agree on slots `≥ G_w`. Composition of G3 twice —
  the point being that nodes need *not* share a horizon; they need each
  horizon to be admissible. Together with the existing agreement results
  (M6: decided slots agree across views), heterogeneity is harmless.

Safety needs no new quorum argument anywhere: it inherits T0/T3/M-series
through G1, and G2–G4 are locality bookkeeping. The risk is concentrated
in getting the *statements* right (rebasing indices; the sweep in G3).

## 5. Liveness and bounded storage above the horizon

- **G5 (liveness transfer).** A `Delivery` for `U` induces a `Delivery`
  for `chop U G` (drop everything below `G`); `Live` and `DeliversQuorum`
  transfer; hence L1 (`no_stall`) holds in the truncated universe, and the
  post-`R` commit chain (L4, L6) with it, for slots above the cut with the
  usual `R`-offsets. The sync side of liveness changes meaning, for the
  better: a joining or recovering validator syncs the **window**, not the
  history — `chop`'s content plus a checkpoint (§6), which is the entire
  point of the exercise.
- **G6 (bounded storage — the headline).** Compose B4 on `chop U G` with
  the lag invariant (A2): if every correct validator keeps its horizon
  within `Λ` of its current round `t`, then
  > `|V_v(t)| ≤ |Correct|·(Λ+1)·(1 + f·T)`-shaped — **constant in `t`**.
  This is the theorem the whole extension exists for: the DoS story ends
  at "linear forever", the GC story ends at "constant, at lag `Λ`".
- **G7 (relay obligation, windowed).** The §6 no-amplification story
  survives with "your block's cone" replaced by "your block's cone above
  `max(G_v, G_w)`": a correct validator serves at most the window, and
  everything below is covered by the checkpoint. Floods are still dampened
  at acceptance; now the *honest* obligation is bounded too.

## 6. Setting the horizon without consensus

The traditional design runs consensus on `G` itself: after a commit, all
correct validators agree on a GC round. That works, but it is worth
resisting, for the reason the user-level intuition suggests: **we do not
need horizons to be equal — we need each to be admissible, and the skew to
be bounded.** G4 already makes heterogeneous horizons safe. What remains
is choosing `G_v` locally so that admissibility and bounded skew come for
free. Two candidate rules, not exclusive:

- **The commit-frontier rule.** `G_v :=` (the largest round such that
  every slot below it is decided in `v`'s view) `− Λ`. Admissibility (A1)
  holds by construction; (A2) by the margin. Skew: decisions are *final*
  (M-series: a decided slot never flips) and *shared* (M6: two views never
  disagree on a decided slot; L3: decisions propagate to the full view),
  so post-`R` two correct frontiers differ by at most the commit lag —
  which L6 (commits recur) bounds. No agreement protocol; the DAG's own
  commits are the synchronizer.
- **The common-core rule** (depth-based). Post-`R`, the backbone lemma
  puts every correct block of round `m` inside every correct cone from
  `m+1` on, and D25 (density) says even Byzantine-authored blocks cannot
  be selectively blind below any valid block. So "everything `Λ` rounds
  deep is in every correct validator's cone" is a *theorem*, not a
  coordination outcome — a validator may set `G_v := t − Λ` knowing that
  no correct peer can still be missing what it discards. Skew between
  correct nodes is the round skew, ≤ 1 post-`R`.

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
lag (referenced layer blocks are in correct cones), verdicts above the
cut are window-local (G2), and extra fringe is inert and bounded. Bases
need not agree, exactly as horizons need not.

Better still, **no signatures are needed even here**: in this model a
validator's attestation *is its block* — its cone is its objective,
checkable (D13), unforgeable statement of what the layer contains. The
certificate is definable DAG-internally and decidably:
`Base U t G := { y at round G : y lies in the cones of round-t blocks by
≥ f+1 distinct authors }`, with the guarantee side supplied by `n−f`
authors *having* round-`t` blocks (Populated) rather than by collecting
messages. Equivocating attesters cost nothing — the filter counts
distinct authors, and `f+1` authors always include a correct one
(`exists_correct_of_card`).

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
  `complete` for the window.
- **G12 (bootstrap safety).** Rebasing on *any* base satisfying the G10
  sandwich yields a universe whose slot verdicts above the cut agree with
  every correct validator's (compose G10–G11 with G2–G4): inexact
  certificates, exact decisions.

## 7. The plan

House rule as always: every definition gets a witness before anything is
proved from it. Phases, in order:

- **P0 — witness first.** `chop Uexcl 2` computed concretely: the
  post-exclusion DAG re-based, its round-2 layer as geneses; `decide` that
  it is a universe and that the surviving slot verdicts match. Also the
  negative witness: `chop Umerge` at a cut above the equivocation round,
  where validator 0 is *no longer exposed* — the statute of limitations
  made visible on data.
- **P1 — the operator.** `chop U G : BlockUniverse` (blocks `≥ G`,
  rounds rebased, base layer's refs emptied) + **G1**. Design decision to
  settle here: rebase (preferred — every theorem applies verbatim) versus
  weakened completeness (rejected unless rebasing hits an unforeseen
  wall; it threads a hypothesis through everything).
- **P2 — verdict invariance (G2).** Window-locality of
  `supporters`/`certificates`/`blames`/`DirectCommit`/`DirectSkip` under
  `chop`.
- **P3 — decision invariance (G3, G4).** The backward sweep under (A1);
  then heterogeneous horizons by composition. The delicate statements of
  the extension; expect the effort here.
- **P4 — liveness transfer (G5).** Induced `Delivery`, transferred
  `Live`/`DeliversQuorum`, `no_stall` and the commit chain on `chop`.
- **P5 — bounded storage (G6, G7).** B4 on the truncated universe plus
  the lag invariant; the windowed relay obligation. The headline.
- **P6 — horizon policy and the attested base (G8–G12).** The
  commit-frontier and common-core rules, admissibility, skew, no-desync;
  then the inexact certificate: `Base` as a DAG-internal, decidable
  definition, the sandwich (G10), window completeness after the lag
  (G11), and bootstrap safety (G12). Witness on data: `Base` computed on
  a truncated `Uexcl`/`Utwin`, with a Byzantine fringe block surviving in
  one collector's base and not another's — and the verdicts agreeing
  regardless.
- **P7 — the forgiveness ledger.** State precisely what survives of
  C2/D17 across epochs (one reveal per author per epoch) and prove the
  budget backstop on `chop` (B4/B5 relativized). Doc updates throughout;
  `dos-equivocation-and-growth.md` §9's "wire-level residue" gains a
  sibling: the GC residue is bootstrap trust.

**Open questions**, recorded before they are argued about:

- **Q1 — epoch coupling.** Should the budget parameter `T` and the lag
  `Λ` be related? A forgiven author re-enters at budget rate; `Λ` sets how
  often forgiveness can recur. The product may be the right "adversary
  work per epoch" quantity.
- **Q2 — checkpoint content.** Is the new genesis layer alone enough for
  all consumers (it is for the DAG machinery), or does application state
  (the ledger prefix) force a richer checkpoint? Out of scope for the DAG
  theorems, in scope for honesty about what "bootstrap" means.
- **Q3 — pruned-view decidability.** `decide`-checkable witnesses need
  `chop` computable; the fuel-based `history` (S6) should survive
  rebasing untouched, but this is exactly the kind of thing P0 exists to
  catch.
