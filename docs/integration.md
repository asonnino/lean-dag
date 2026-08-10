# lean-dag — Integration: composing the arcs

> **Provenance.** Code and prose in this project were co-written with
> heavy LLM assistance. The Lean proofs are machine-checked — the kernel
> verifies every theorem against its stated form — but whether the
> definitions and theorem statements capture their *intended* meaning,
> and whether the surrounding prose is faithful to what is proved, has
> only human-plus-LLM review behind it. Read critically.

Every arc of this development was built additively: each consumes the
core read-only, and none modifies another. That discipline bought
independence, and it left a question unanswered — **do the arcs compose
with each other?** A validator that garbage-collects below a horizon,
recovers from a crash by Safe Skip, runs an adaptive leader schedule
and tolerates hybrid faults is running all four mechanisms at once, and
nothing proved so far says the four are jointly consistent.

This document is the design record for the **integration** arc. Its
thesis is that the composition matrix must *not* be proved cell by
cell. Nine arcs pair into thirty-six combinations, and triples into far
more; the development would double in size to say something most
readers would assume anyway. Instead: give each arc a small,
explicitly named **interface** — the invariants it consumes and the
invariants it preserves — and prove interface-to-interface facts. Then
composition is a corollary, and the cost is linear rather than
quadratic. §2 collects that interface and reports an audit confirming
it is closed; §3 turns it into a work plan of roughly twenty small
lemmas in place of thirty-six real proofs.

Results will carry **I**-labels. Everything will live in
`LeanDag/Integration/`, with `decide` witnesses in
`LeanDagTest/Integration.lean`.

## 1. What the arcs actually are

The arcs are not all the same kind of object, and the composition
strategy differs by kind. Four kinds:

**Universe transformers.** Take a `BlockUniverse` and produce another:
`chop U G` (§9, truncation at a horizon) and `SkipMsg.skipFill` (§12,
extension by a fill). These are the arcs that can *break* another arc's
hypotheses, because they change the object every other arc quantifies
over.

**Fault-layer variants.** Replace the `Faults` instance: `Faults5`
(§10, `n ≥ 5f+1`) and `HybridFaults` (§14, with its *derived* base
instance). These change the quorum arithmetic under everything.

**Schedule- and timing-layer variants.** Replace or refine the `Slots`
instance or the timed structure: `slotsOf` (§13, adaptive assignment),
`Slots.chop` (§9's induced schedule), `ReactiveCore`/`ReactiveM` (§11),
`CatchupSync` (§6.12).

**Property provers.** Consume a universe plus conditions and conclude:
chain quality (§7), the storage bounds (§8), the liveness capstones
(§6), agreement (§5).

The asymmetry is the point. A property prover cannot break anything —
it only reads. A transformer can break everything. So the interface
discipline needs to bear almost entirely on the transformers, and the
property provers need only be *stated* against named invariants rather
than against incidental facts about a particular universe.

## 2. The named invariants

The development already has the right vocabulary; it has simply never
been collected. Collecting it turns out to be the substantive part of
the plan, because the invariants do **not** all live at the same level,
and the level is what determines which transformer can break them.

There are three layers, and they are not independent: a `Delivery` is
*indexed by* a universe, so a universe transformer forces a delivery
transformer, while a `Slots` instance is independent of the universe
entirely.

### 2.1 Layer U — the block universe

The object: `BlockUniverse Validator BlockId Payload`. Broken by:
`chop`, `skipFill`.

**U1. The DAG laws (P1–P5).** Carried by the `BlockUniverse` structure
itself — predecessor rounds, distinct creators, the reference quorum,
the self-parent clause, completeness, non-equivocation.
*Provides:* everything; no theorem in the development is stated without
them. *Preservation is free*, in the strict sense that a transformer
cannot typecheck without proving it — which is why `chop` and
`skipFill` both discharge it in their definitions rather than as
lemmas.

**U2. Production.**
```lean
def PopulatedOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r
```
*Provides:* every liveness result in the development. L4 (a reliable
leader is committed) consumes it three times — at the leader's round
and the two above — and every capstone above L4 inherits it. If a
transformer preserves nothing else, it must preserve this or nothing
downstream of §6 applies.

**U3. Coverage.**
```lean
def SynchronisedOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ T →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ T → a ∈ (U.block b).refs
```
*Provides:* the other half of L4, and with it the whole liveness line.
Note the shape: it is a statement about **every** block of `T` at
**every** round above `R`, which is precisely why adding blocks to a
universe is dangerous for it and removing blocks is not (§3.1, I4/I5).

**U4. The exposure condition.**
```lean
def DoSValid (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator
```
*Provides:* C2 (at most `f` authors exposed per cone) and through it
C1′, the general per-cone storage bound of §8. Consumed by nothing
outside §8 and §9 — safety and liveness are provably independent of it,
which is one of §8's headline claims.

**U5. Honest non-equivocation.**
```lean
def HonestNoEquiv (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ i ∈ U.ids, ∀ j ∈ U.ids, (U.block i).creator ∉ H.byzantine →
    (U.block i).creator = (U.block j).creator →
    (U.block i).round = (U.block j).round → i = j
```
*Provides:* every safety theorem of §14 — H2 through H6. It is P5 at
the wider honest class, and it is the *only* invariant in this list
introduced by an arc rather than by the core, which makes it the
canonical example of the audit question of §2.4.

**U6. Verdict facts** — `Decided U V k v`, and its bounded variant
`DecidedWithin`. Not an invariant of a universe so much as a family of
derivable facts about one, but it behaves like one for composition
purposes: a transformer must say what happens to verdicts.
*Provides:* the ledger (M7, M8), chain quality (§7), and — through
`DecidedWithin` — the entire adaptive fixpoint (§13).

### 2.2 Layer D — the delivery structure

The object: `Delivery U`, **indexed by the universe**. This dependency
is the structural fact the first draft of this document missed: a
universe transformer `F : U ↦ F U` does not merely need to preserve
delivery-level invariants, it needs a *transformer of its own* at this
layer, `F_D : Delivery U → Delivery (F U)`, before those invariants can
even be stated in the transformed setting.

GC has one — `chopD D G : Delivery (chop U G)`, shifting every index by
`G`. **Safe Skip has none**, which is why I6 as first drafted was not a
well-formed obligation (§3.1).

**D1. Production, operationally** — `Live U D N`: every correct
validator has a genesis block, and one holding a quorum at `r` builds
at `r+1` (P8). *Provides:* the untimed production derivation, hence U2.

**D2. Delivery conditions** — `DeliversQuorum D`, `EventuallyDelivers D R`.
*Provides:* the legacy quorum route (§15) and the delivery derivation
of coverage (L7a). Both already have `chopD` counterparts.

**D3. The storage budgets** — `UniformBudget D T`, `ByzBudget D κ`,
`RefsAccepted D`. *Provides:* B4 and B, the linear-storage capstone of
§8. All three have `chopD` counterparts (`byzBudget_chopD`,
`refsAccepted_chopD`).

### 2.3 Layer S — the schedule

The object: `Slots Validator`, independent of the universe. Broken not
by universe transformers but by *schedule* variants — `Slots.chop`
(§9's re-indexing) and `slotsOf` (§13's adaptive assignment).

**S1. Fairness** — `FairScheduleOn T` (a reliable leader arbitrarily
far out) and `FairRunOn T c` (`c` consecutive reliable-led slots
arbitrarily far out). *Provides:* recurrence (L6), chain-quality
inclusion (CQ6, CQ7), and the liveness capstone L10.

**S2. Shape** — `SpansEligible c` (a run of `c` reaches past everything
below it) and `BoundedSpacing s`. *Provides:* the committed-run
descent, hence L10 and its Odontoceti and hybrid mirrors.

**S3. Adaptive fairness** — `PlacesRuns P T c`: every assignment the
policy can emit still places a reliable run in each epoch.
*Provides:* the existence half of the adaptive fixpoint (AL5). Note it
is a condition on a *policy*, not on a schedule — the only invariant in
the list at that level, and a sign that §13 sits one abstraction step
above the rest.

### 2.4 What the audit found

The claim that these are *all* the hypotheses is now checked rather
than asserted, by querying the extracted statements of the principal
capstones (`dos_resistance`, `chain_quality`, `decided_agree_chop`,
`card_retained_le`, `bootstrap_agree`, `all_decided_below_of_fairRun`,
`commits_recur_on`, `decided_fill`, `adaptiveRun_exists`,
`adaptiveRun_agree`, `committed_of_correct_block`, `card_history_le'`,
`card_viewUpto_le`) for hypothesis-position identifiers outside the
list. Three findings, all of which changed this plan:

1. **The schedule layer was missing entirely.** `FairScheduleOn`,
   `FairRunOn`, `SpansEligible` and `PlacesRuns` appear as hypotheses
   of five capstones and were absent from the first draft's list. The
   first draft would therefore have produced a preservation table that
   silently omitted every combination involving a schedule variant —
   including GC × Adaptive, the most interesting one (I9).
2. **The delivery layer is dependent, not parallel.** `UniformBudget`
   and `RefsAccepted` range over `Delivery U`, not `U`, so they cannot
   be stated for a transformed universe without a transformed delivery.
3. **Nothing else turned up.** Modulo the two structural corrections,
   the surface really is closed: every hypothesis of every capstone
   audited is `U1`–`U6`, `D1`–`D3`, `S1`–`S3`, or arithmetic side
   conditions on `ℕ`. That is the fact the linear strategy rests on,
   and it is now evidence rather than hope.

The list is also the thing to *audit when a new arc is added*: an arc
that introduces a hypothesis outside it has, by that act, created a new
row in every future preservation table. §14 did exactly this with
`HonestNoEquiv`, which is why it is the one entry above with a single
consumer. The integration arc should treat "does this need a new named
invariant?" as a design question, not bookkeeping.

## 3. The strategy: preservation, not combination

### 3.1 Transformers × invariants

The core move. For each transformer `F` and each named invariant `I`,
prove one lemma:

    I U  →  I (F U)

Then any property `P` whose statement depends only on named invariants
transfers to `F U` **for free**, with no new proof and no mention of
`P` anywhere. The pattern is already established — GC carries most of
its column, and this is why §9 reads as cleanly as it does.

**Layer U — universe transformers.**

| Invariant | `chop U G` | `skipFill` |
|:---|:---|:---|
| U1 DAG laws | ✅ (definitional) | ✅ SS1 (definitional) |
| U2 `Populated` | ✅ `populated_chop` | ✅ SS2 `skipFill_populatedOn` |
| U3 `SynchronisedOn` | ✅ **I4** `synchronisedOn_chop` | ⛔ **I5 — refuted**; ✅ above the fill |
| U4 `DoSValid` | ✅ `dosValid_chop` | **I1 — open** |
| U5 `HonestNoEquiv` | ✅ **I2** `honestNoEquiv_chop` | ✅ **I3** `honestNoEquiv_skipFill` |
| U6 verdicts | ✅ G3 `decided_chop` | ✅ SS5 `decided_fill` |

**Layer D — delivery transformers.** `chopD` supplies the whole
column; Safe Skip has no delivery transformer at all, so the entire
column is blocked behind constructing one:

| Invariant | `chopD D G` | Safe Skip |
|:---|:---|:---|
| — the transformer itself | ✅ `chopD` | **I6a — open, blocking** |
| D1 `Live` | ✅ `live_chopD` | I6b |
| D2 `DeliversQuorum` | ✅ `deliversQuorum_chopD` | I6c |
| D3 budgets | ✅ `byzBudget_chopD`, `refsAccepted_chopD` | I6d |

**Layer S — schedule variants.** Universe transformers do not touch
this layer, but both schedule variants do, and the table is nearly
empty:

| Invariant | `Slots.chop S G d` | `slotsOf hinj a` |
|:---|:---|:---|
| — the correspondences | ✅ `chop_slotRound`, `chop_leader` | ✅ `slotsOf_slotRound`, `slotsOf_leader` |
| S1 `FairScheduleOn`, `FairRunOn` | ✅ **I13** `fairScheduleOn_chop`, `fairRunOn_chop` | ✳︎ not a preservation fact |
| S2 `SpansEligible` | ✅ **I15** `spansEligible_chop` | ✅ `spansEligible_slotsOf` |

✳︎ The empty cell is the informative one. `slotsOf` sets
`leader := a`, so fairness of the induced instance is a statement about
the *assignment* and is not derivable from the base schedule's
fairness — an adaptive policy changes who leads, which is the entire
point of §13. There is no lemma to prove here; `PlacesRuns` (S3) *is*
the replacement, and seeing it arise this way explains its otherwise
peculiar shape: it quantifies over every verdict function the policy
might see, because no fact about the base schedule survives
reassignment. The contrast with `spansEligible_slotsOf` directly below
is the whole distinction — eligibility reads only `slotRound`, which
reassignment fixes, so *shape* transfers verbatim while *fairness*
cannot transfer at all.

### 3.2 What the proved cells establish

Six cells are closed, all on the standard three axioms
(`LeanDag/Integration/`, witnessed in `LeanDagTest/Integration.lean`).

**I2, I3 — honest non-equivocation survives both transformers**
(`honestNoEquiv_chop`, `honestNoEquiv_skipFill`). Together these are
what let §14's hybrid model be used inside §9's truncation and across
§12's fill: a hybrid universe stays a hybrid universe on both sides.
I3 is the same argument `skipFill`'s own `no_equivocation` field makes
for the derived correct class, at the wider honest class, and turns on
the same clause — `hgap`, the crash itself.

**I4 — coverage survives truncation** (`synchronisedOn_chop`), needing
only the horizon offset `R ≤ G + R'` and no base-layer exception. The
reason is structural and generalises (§3.3): coverage constrains a
block at chopped round `n + 1`, which lies above the cut by
construction, so `chop` retains its references and the original clause
applies unchanged.

**I5 — coverage does *not* survive the fill**
(`not_synchronisedOn_skipFill`), refuted in general rather than on
data: at every gap round of every fill, an old block at the round above
fails to reference the filled block below it, because no old block
references a fresh identifier. The `Ucrash` witness
(`ucrash_not_synchronisedOn`) is retained to show the hypotheses are
satisfiable and the refutation therefore bites.

This is the same fact that makes Safe Skip **safe**. SS3 concludes a
filled candidate is always directly skipped *because no old block
references a fresh identifier*; I5 concludes coverage fails at gap
rounds for the identical reason. One fact, two consequences: the fill
can manufacture neither a commit nor coverage. §12 claims only that it
restores *production*, which is the hypothesis liveness consumes, so
nothing in §12 weakens — but the boundary is now exact. Coverage
returns strictly above the fill (`synchronisedOn_skipFill_above`,
requiring `sk.r < R'`); at `n = sk.r` the lower block may still be the
last filled one, and the refutation reaches there too.

**I13, I15 — the schedule layer survives truncation**
(`fairScheduleOn_chop`, `fairRunOn_chop`, `spansEligible_chop`). A
joiner reasoning inside a truncation has a schedule that is fair and
spanning in its own right, which is what I9 needs.

**I10 — a crash-prone validator can Safe Skip, once a hypothesis is
stated as the fact it stands for.** This is the composition that did
*not* fit, and the misfit is the finding. `SkipMsg` carried
`hv1 : v1 ∈ Correct`; the hybrid model splits `Correct` into honest and
available, and a crash-prone validator — precisely the one Safe Skip
serves — is honest but not correct. The structure could not describe
its own motivating case.

The hypothesis was stronger than its use. It appeared **once**, pinning
`v1`'s round-`r0` block to the anchor at the fill's boundary. §12 now
carries that fact directly (`hB1uniq`), with `hB1uniq_of_correct`
recovering the base model's route and `hB1uniq_of_crash` supplying the
hybrid one from `HonestNoEquiv`. Neither arc was wrong; one of them
stated a hypothesis in terms of a class the other splits, and finding
that is what an integration arc is for.

This is the arc's one modification to existing code, and it is a strict
weakening: every model that satisfied the old field satisfies the new
one, and the report's §12.1 now explains why the fact is stated rather
than the membership.

**I11 — nothing to prove, and that is the result.** The expectation was
a lemma relating `AdaptivePolicy` to `HybridFaults`. There is none, and
there cannot usefully be one: a policy reads verdicts, and the crash
class is invisible in verdicts. A halted validator's slot is skipped by
L5, whose hypothesis is that no block at the round carries the leader
as creator — which says nothing about *why* the leader is absent. A
crash-prone leader, a withholding Byzantine leader and a correct leader
that has not yet built are indistinguishable there, and a demoting
policy demotes all three alike. I11 joins I14 as a non-task, and
`lifecycle` composes L5, SS2 and I3 into one statement in which three
arcs meet without any of them mentioning another.

**I16 — the thesis holds: composition is free.** The capstone
(`LeanDag/Integration/Stack.lean`) puts a validator on all four
mechanisms at once — recovered by Safe Skip, then truncated below a
horizon, read in the hybrid fault model, under an adaptive schedule —
and every proof is a chain of existing lemmas. Honest non-equivocation
survives the stack by I3 then I2 (`honestNoEquiv_stack`, one line);
coverage by I5-positive then I4, the two offsets composing exactly as
their statements suggest; production by SS2 then the truncation's
rebasing. The payoff is `hybrid_agree_stack`: **a validator that
recovered from a crash and then pruned still cannot disagree with
anyone about a verdict**, its proof being §14's agreement theorem
applied to a different universe with the one hypothesis discharged by
`honestNoEquiv_stack`. Nothing about the fill or the cut is re-proved.

Two things the capstone settled that the ingredients did not.

**Order matters, asymmetrically — and the deployment order is the free
one.** Fill-then-truncate is unconditional: `chop (skipFill U) G` is
well formed at every horizon, because the fill has already happened
when the cut is made. The reverse needs the anchor retained, since a
`SkipMsg` for `chop U G` requires `B1 ∈ (chop U G).ids`. So I7's
condition is real but appears here as an *asymmetry between orders*
rather than as an obstacle, and the order that costs nothing is the one
deployments actually take: fill the gap on recovery, prune later. §5.4
anticipated that I16 might need I7 first; it does not, and this is why.

**The schedule layer stacks entirely for free** (`schedule_stack`).
`Slots.chop` and `slotsOf` are functions of a `Slots` instance and
nothing else, so the layer-S results hold for a validator running *any*
stack of universe transformers, with no compatibility lemma. That is
the clearest vindication of §2's layering: the composition matrix is
smaller than the arc count suggests because one of its three layers
does not interact with the others at all.

**I9 — a joiner can run the network's schedule, under two obligations**
(`LeanDag/Integration/Joiner.lean`). The question decomposed further
than expected, and the decomposition is the result.

The schedule half is *definitional*: truncating an adaptive schedule
and adapting a truncated one produce the same rounds and the same
leaders, `slotsChop_slotsOf` closing by `⟨rfl, rfl⟩`, provided the
assignment used inside the truncation is the original one shifted past
the base slot. No policy hypothesis is involved — all of I9's content
sits in whether a joiner can *produce* that shifted assignment.

That is `HorizonStable`, and it is the deployment obligation the arc
was looking for: the joiner's rule, run on the truncation with the
joiner's own slot numbering, must return what the network's policy
returns at the corresponding slot. Under it a joiner computes exactly
the leaders the network is using (`joiner_assign_agree`), so the two
run one schedule seen from two origins (`joiner_leader_agree`). The
obligation is stated on the *rule* rather than on a whole
`AdaptivePolicy`, because a policy is indexed by its `Slots` instance
and a joiner's policy therefore inhabits a different type from the
network's; the rule is the part that survives re-indexing, and the
leaders are what must agree.

A **second, independent obligation** surfaced from the run structure.
Horizon-stability aligns leaders; it does not align *epochs*. A
joiner's slot `k` is the network's `d + k`, so the epoch numberings
correspond only when the base slot is a whole number of epochs
(`epochOf_add_of_dvd`), and the example beneath it shows the
correspondence genuinely failing otherwise. So: **a garbage-collection
base slot must be a multiple of the adaptive epoch width.** Without
it two validators can agree on who leads every slot and still disagree
about which verdicts the policy was entitled to read.

The constant policy is horizon-stable only at `d = 0`
(`horizonStable_const_zero`), which is the informative degenerate
case: even a rule that ignores verdicts entirely must be *stated
relative to the reader's own slot numbering* to survive truncation.
Horizon-stability is not only about how far back a policy reads.

### 3.3 Transport heuristics

Three patterns emerged that should be applied to the remaining cells
before attempting them, because each predicts the shape of the answer:

**Quantify upward, transport cheaply.** A clause constraining a block
at round `n + 1` in terms of round `n` transports through truncation
without a base-layer exception, because the constrained block is above
the cut by construction (I4). A clause pinned at a fixed round needs
one (`supporters_chop`'s `1 ≤ m`). When a new invariant is added to
§2, its quantifier shape predicts its transport cost.

**Truncated subtraction is faithful only above the cut.** Paid three
times now — in I2, in `Slots.chop`'s `keyed` clause, and in I15 — and
discharged the same way each time: some hypothesis already in scope
pins the rounds above `G` (the `chop` filter; the base-slot condition
`G ≤ S.slotRound d`, carried upward by monotonicity in
`le_slotRound_add`). Expect every round-sensitive `chop` lemma to pay
it, and look for the pinning hypothesis rather than strengthening the
statement.

**Adding blocks is dangerous; removing them is not.** Truncation
restricts universally quantified invariants downward for free (I2, I4).
Extension does not (I5), because an invariant of the form "every block
here relates to every block there" acquires new obligations when new
blocks arrive — and `skipFill`'s new blocks are, by SS3's own argument,
exactly the ones nothing old can reference. **This predicts I1**: the
fill's cone is strictly larger than the donor's — it adds `v1`'s chain
below the anchor — and `DoSValid` forbids referencing an author exposed
*in one's own cone*, so a larger cone can only expose more. I1 is
therefore likely false without a hypothesis confining equivocations in
`v1`'s pre-crash history; see §5.6.

### 3.4 Transformers × transformers

Rather than prove that every *order* of applying transformers is safe,
prove a **commutation or normalization** result once. §9 already has
`chop_chop`: two horizons compose, and the composite is the coarser
one. What is missing is the mixed pair:

**I7 — `chop` and `skipFill` commute, on their common domain.**
Concretely, if the anchor `B1` is retained (`G ≤ round B1`), then
truncating a filled universe and filling a truncated one agree:

    chop (skipFill sk) G  ≃  skipFill (sk.chop G) G

with the fill's data re-indexed. The side condition is the interesting
content, and it is an *engineering* fact worth stating plainly: **Safe
Skip requires its anchor to be above the horizon.** A validator that
crashes for longer than the garbage-collection lag cannot Safe Skip
back in — its last block has been pruned — and must instead bootstrap
by the §9.5 attested-base route. That is a genuine deployment
constraint that neither arc alone can see, and pinning it as a theorem
(with the negative case witnessed on data) is exactly the kind of
result integration should produce.

### 3.5 Layer variants: parametrize once, instantiate thrice

The schedule and fault layers should not be handled by preservation
lemmas but by **abstraction over the interface actually consumed**.

The evidence that this works is already in the development. §14
(hybrid) composes with the entire DAG layer for free — not through any
composition theorem, but because `HybridFaults.toFaults` places the
hybrid parameters into the *base* `Faults` interface, so every theorem
stated over an arbitrary `Faults` instance applies verbatim. Nothing
was proved to make that happen; the theorems were simply stated at the
right level of generality.

The same move is available, and not yet taken, for the adaptive layer.
§13.5 already observes the adaptive layer is rule-agnostic — but it
demonstrates this by *mirroring* the whole development onto Odontoceti,
a second copy of every definition and theorem. A third copy for Hybrid
is the obvious next step and the wrong one. Instead:

**I8 — the decision-relation interface.** Extract the three properties
the adaptive fixpoint actually consumes from its underlying rule:

1. a bounded decision relation with an agreement theorem
   (`DecidedWithin.agree`);
2. a congruence lemma — the relation reads `leader` only below its
   bound;
3. a committed-run descent producing bounded derivations.

Anything satisfying these three admits the adaptive construction. The
existing Mysticeti and Odontoceti mirrors become instances, the Hybrid
case follows without a third copy, and the report's §18.5 remark about
the one refactor the development declined ("a rule-parameterised
decision relation shared between §3.5 and §10.3") is finally
discharged — with three instances to justify it where two did not.

It is the most invasive item considered here — it touches existing
code rather than adding to it, which every other arc has avoided — and
it should be done as a *generalization with the old statements retained
as corollaries*, so nothing downstream breaks and the diff is
auditable. That is a refactor, and §4.2 moves it out of this arc
accordingly: I9 settled adaptive × GC without it, so no integration
result now depends on it. The analysis above is kept because it is the
specification that arc will need.

### 3.6 What remains genuinely pairwise

Some combinations are not preservation facts and must be proved
directly. These are the ones with real content, and there are fewer
than the matrix suggests:

**I9 — GC × Adaptive: can a joiner recompute the schedule?** *(Closed;
see §3.2. The account below states the question as it was posed.)* The
adaptive schedule at epoch `e` is a function of verdicts at epochs
`≤ e−2`. Garbage collection prunes history below a horizon. A
validator that joins from the truncation therefore may not hold the
verdicts the policy needs to compute the current schedule — and if it
computes a *different* schedule, §13's uniqueness theorem does not
apply to it, because uniqueness quantifies over runs of *one* policy
over *one* universe. This is the sharpest integration question in the
development, it has a deployment analogue (Hammerhead's schedule is
recomputed from committed sub-DAGs, which a pruned node lacks), and it
has a clean statement: the policy must be **horizon-stable** — its
output depends only on verdicts within the retained window —

        pick U v k = pick (chop U G) (v restricted above G) k

    and then a joiner's run agrees with a full-history run (I9). A
policy that reads arbitrarily far back is a policy incompatible with
garbage collection, and saying so precisely is worth more than proving
one compatible instance.

**I10 — Hybrid × Safe Skip: the natural pairing.** The hybrid model
names a *crash-prone* class; Safe Skip is the recovery mechanism for a
crashed validator. That these two were built separately is an accident
of order. The composite statement — a crash-prone validator's fill,
verified at hybrid thresholds, restoring it to the correct class — is
the arc's most natural end-to-end story, and mostly follows from I3
plus restating §12's theorems over `HybridFaults`.

**I11 — Hybrid × Adaptive: demotion of the crash class.** The
demote-on-skip policy of §13.6 is the mechanism that removes a crashed
validator from the leader rotation; the hybrid model is where "crashed"
is a named class. Combined with I10, this is the full lifecycle: a
crash-prone validator is demoted while down (I11), safe-skipped back in
(I10), and re-promoted after recovery. That lifecycle, machine-checked,
is a stronger claim than any single arc makes.

**I12 — DoS × Safe Skip.** Two questions, now separated by the
analysis of §5.6. At the universe layer, whether the fill preserves
`DoSValid` (I1) — expected conditional rather than preserved, since the
fill's cone is strictly larger than the donor's. At the delivery layer,
whether a bulk fill respects the novelty budget (§5.3), which is gated
behind I6a and moot if I1 fails. The pair is the arc's most likely
*open* entry, and recording it as open is a legitimate outcome.

## 4. Module plan and order

| Module | Contents | Status |
|:---|:---|:---|
| `Integration/Preservation.lean` | I2, I3, I4: honest non-equivocation under both transformers; coverage under truncation | **done** |
| `Integration/Coverage.lean` | I5: coverage refuted under the fill, and recovered strictly above it | **done** |
| `Integration/ScheduleShape.lean` | I13, I15: fairness and shape under `Slots.chop` | **done** |
| `Integration/Joiner.lean` | I9: the transformers commute; horizon-stability; epoch alignment | **done** |
| `Integration/Stack.lean` | I16: the composition capstone — several transformers at once | **done** |
| `Integration/Lifecycle.lean` | I10: the crash-prone fill; I11 recorded as a non-task; the lifecycle | **done** |
| — | I7 and the placement conditions | §4.4: prose, not a module |
| `Integration/Exposure.lean` | I1: `DoSValid` under the fill, conditionally (§5.6) | design decision pending |
| `Integration/DeliveryFill.lean` | I6a–d: Safe Skip's delivery transformer, then its budget column | deferred, likely open |
| `LeanDagTest/Integration.lean` | the refutation witnessed as biting; the stack and lifecycle exhibits | ongoing |
| — | I8: the decision-relation interface | **moved out of this arc**, see §4.2 |

### 4.1 What the arc turned out to be

Seven cells in, the results have not all been of the kind the plan
anticipated. Three kinds have appeared, and naming them changes what
should be built next:

1. **Preservation lemmas** (I2, I3, I4, I13, I15) — the planned kind,
   and the cheapest. Each closes a column of the composition matrix.
2. **A refutation with an exact boundary** (I5) — worth more than the
   positive would have been, and now the template: refute in general,
   witness that the refutation bites, state the positive form that
   survives.
3. **Placement conditions** (I9's two obligations; I7's expected one) —
   *not in the original plan at all*, and arguably the arc's most
   useful output, because they are engineering guidance rather than
   proof plumbing. A horizon may not be put anywhere: its base slot
   must fall on an epoch boundary, and the retained window must carry
   what the policy reads.

I16 is not a fourth kind but the payoff of the first: it is the proof
that the preservation lemmas *compose*, which is what makes collecting
them worthwhile rather than merely tidy.

The third kind should be pursued deliberately rather than collected
incidentally, and stated as one account — *where may a cut be made,
given everything running above it?* — rather than left as side
conditions scattered across three files. Two of the three conditions
are proved (§3.2); §4.4 settles where the account belongs.

### 4.2 What the arc is not

**I8 (the decision-relation interface) leaves this arc.** It was
included on the reasoning that Hybrid should become a third instance of
the adaptive layer rather than a third copy. That is still worth doing,
but I9 settled adaptive × GC without it, so nothing in the integration
programme now depends on it — and it is a *refactor*: restructuring
working code for elegance. It belongs in its own arc, planned and
reviewed as such, with the old statements retained as corollaries.

The distinction that keeps this honest is not "adds versus modifies".
I10 modified §12, weakening `hv1` to `hB1uniq`, and had to — the
composition was **unstatable** otherwise. That is a different act from
a refactor: it is a hypothesis weakening forced by a theorem one wants
to state, it is strictly conservative, and it is one field and one
proof line. The rule this arc follows is therefore: *modify existing
code only when a result cannot otherwise be stated, never for
elegance.*

### 4.3 The thesis is demonstrated

The plan's claim was that named invariants plus preservation lemmas
make composition free. I16 (§3.2) is that claim, proved: the stacked
universe satisfies every invariant its arcs require, by chains of
existing lemmas with no new argument, and the end-to-end statement —
a validator that recovered from a crash and then pruned cannot
disagree with anyone about a verdict — is §14's agreement theorem
applied to a different universe.

This changes what the rest of the arc is *for*. Nothing remaining is
load-bearing for the central claim; the arc could stop here and be
complete as an argument. What follows is pursued because it is
independently useful, and should be scoped that way rather than as
obligations.

### 4.4 What I16 changed

**I7 drops in priority.** The question was posed as "do the
transformers commute?", and the answer turns out to be that the
*deployment* order — fill on recovery, prune later — is unconditional,
while only the reverse needs the anchor retained. So I7 is no longer a
prerequisite for anything: it is the cost of a corner case (a validator
pruning while a recovery message is in flight). Worth stating, not
worth stating first.

**The placement account shrinks to a section, not a module.** Two of
its three conditions are proved and live in `Joiner.lean` — epoch
alignment and horizon-stability — and the third is I7's, now demoted.
`Integration/Placement.lean` is dropped from the plan; the account
belongs in the eventual report section, where the three conditions can
be stated together in prose without a module that would hold one
lemma.

**A design rule for future arcs.** The schedule layer stacks for free
because `Slots.chop` and `slotsOf` depend on a `Slots` instance and
nothing else. That is a property worth *preserving deliberately*: a
future arc that introduces a schedule variant reading the universe
would forfeit it, and would owe a compatibility lemma against every
universe transformer. Keeping schedule variants universe-independent
is the cheapest structural decision available, and §2's layering is
what makes the cost visible.

### 4.5 Order

1. **I7 next**, as the corner case it turned out to be, and stated with
   the other placement conditions in prose rather than in a module of
   its own.
2. **I1 only with the hypothesis §5.6 identifies**, or not at all; the
   choice between conditional statement and open record is a design
   decision, and "open" is now a perfectly good outcome given §4.3.
3. **I6a–d deferred**, to be recorded as open if §5.6's prediction
   holds — a delivery transformer whose only consumer is a combination
   of doubtful value is not worth constructing.

The arc is now tellable: with I10 and I16 done, a reasonable stopping
point is here, with items 1–3 recorded as open in the report. The arc's results are the preservation table, the
refutation with its boundary, the placement conditions, and the
composition capstone; none of them needs the remainder to stand.

## 5. Risks and predictions

**5.1 The negative results are the valuable ones.** Four cells in this
plan are expected to be *false*: coverage under `skipFill` (I5, now
**settled negative**), `chop`/`skipFill` commutation without the anchor
condition (I7), horizon-stability for an unrestricted adaptive policy
(I9), and `DoSValid` under the fill (I1, §5.6). Each is worth more than
the corresponding positive would have been, because each names a
deployment constraint that no single arc can see. I5 sets the pattern
to follow: refute in general where possible, keep a witness to show the
refutation bites, and state the positive form that survives — the
boundary is the result, not the failure.

**5.2 The interface audit is done, and it moved the plan.** This risk
was live in the first draft, where §2's list was a survey rather than a
verified fact. It has now been checked mechanically against the
extracted statements of thirteen capstones (§2.4), and it was
*wrong in two structural ways* — the schedule layer was missing
entirely, and the delivery layer is universe-indexed rather than
parallel. Both corrections are folded in above; the residual risk is
that the audit covered capstones rather than every theorem, so an
intermediate lemma could still consume something unlisted. That is
cheap to re-check as the arc proceeds and should be re-run whenever a
new preservation lemma turns out to need a hypothesis not in §2.

**5.3 The DoS accounting may not survive a bulk fill.** §8's novelty
budget limits the rate at which an author can inject material; Safe
Skip injects one block per gap round in a single message. Whether that
respects `UniformBudget` depends on whether the budget is per-block or
per-round — and the fill produces exactly one block per round, which
suggests it does, but the *acceptance* side (`RefsAccepted`) may see a
burst. This is the combination most likely to require a genuinely new
argument rather than a preservation lemma. It is also gated behind
I6a's construction, and §5.6 now suggests the universe-level half fails
first, which would make the delivery-level question moot.

**5.4 The composition capstone chained cleanly, in one order.** This
risk is discharged (§3.2). The second half of it was right: the
invariants compose in one order and not obviously the other. But the
order that works — fill, then truncate — is the deployment order, so
I16 needed no hypothesis `chop`'s statement does not already carry, and
I7 was not a prerequisite after all. The residual is that
truncate-then-fill remains unproved and is what I7 will address; it is
the rarer deployment case (a validator pruning while a recovery message
is in flight) and its condition is already identified.

**5.5 Scope discipline.** The temptation in an integration arc is to
prove the full cross product because each individual proof is easy once
the interface exists. That would defeat the purpose. The rule for this
arc: **a combination gets its own theorem only if it has content that
the preservation lemmas do not already imply.** Everything else is a
one-line corollary at most, and more often simply an observation in the
report that the composition is immediate.

**5.6 `DoSValid` under the fill is probably conditional, not
preserved.** The third heuristic of §3.3 predicts I1 negative, and the
mechanism is specific enough to state before attempting: a filled
block's cone is the donor block's cone *plus* `v1`'s chain below the
anchor, since `fillBlock` inserts the self reference. `DoSValid`
forbids a block from referencing an author exposed **in its own cone**,
and a larger cone can only expose more authors. So the donor's own
`DoSValid` does not transfer: the fill inherits the donor's references
while acquiring a strictly larger cone in which one of those
referenced authors may be exposed by an equivocation in `v1`'s
pre-crash history.

If that is right, I1 needs a hypothesis of the form *no author of the
donor line's references is exposed within `B1`'s cone*. Two responses
are available and the choice is a design decision, not a proof detail:
state I1 conditionally and record the hypothesis as a deployment
obligation on the recovering validator, or record Safe Skip × DoS as
open. The first is preferable if the hypothesis turns out to be
checkable by `v1` itself — which it is, since `B1`'s cone is exactly
what `v1` retains — and that would make it enforceable in the sense
§8 requires.

## 6. Out of scope

- **Executions.** Composition here is composition of structural
  conditions, not of protocol executions; nothing about the *order* in
  which mechanisms fire is modelled, and nothing can be, in a model
  with no traces (§1.4).
- **Reactive × everything.** The reactive schedule (§11) is a timing
  refinement below the `SynchronisedOn`/`Populated` interface, so it
  composes with the structural arcs trivially — it produces the same
  interface by a different route. Nothing to prove; worth one sentence
  in the report.
- **The certified variant, and cryptography** — outside the model, as
  in every other arc.
