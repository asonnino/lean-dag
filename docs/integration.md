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
| U3 `SynchronisedOn` | **I4 — open** | **I5 — open, expect negative** |
| U4 `DoSValid` | ✅ `dosValid_chop` | **I1 — open** |
| U5 `HonestNoEquiv` | ✅ **I2 — done while drafting** | **I3 — open** |
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
| S1 `FairScheduleOn`, `FairRunOn` | **I13 — open** | ✳︎ not a preservation fact |
| S2 `SpansEligible` | **I15 — open** | ✅ `spansEligible_slotsOf` |

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

Predictions worth recording before the work, since a plan that cannot
be wrong is not a plan:

- **I2** (`chop` preserves `HonestNoEquiv`) is nearly free: truncation
  removes blocks and never adds them, and `HonestNoEquiv` is a
  *universally quantified* statement over pairs of retained blocks, so
  it restricts downward. This single lemma is what makes §14 (hybrid)
  compose with §9 (GC). **Verified while drafting** — four lines — and
  the one non-trivial step is worth recording, because it will recur:
  `chopBlock` rebases rounds to `round − G`, so equal *chopped* rounds
  do not immediately give equal original rounds. Truncated subtraction
  is faithful only above the cut, and the filter supplies `G ≤ round`
  on both sides to close it by `omega`. This is the same subtlety §9
  already met in `Slots.chop`'s keying clause, and I15 will meet it a
  third time — `SpansEligible` is stated through `slotRound`, which
  `Slots.chop` rebases by exactly this subtraction.
- **I3** (`skipFill` preserves `HonestNoEquiv`) is the interesting one.
  The fill creates blocks authored by `v1`, who is honest — so the
  proof must show the filled blocks do not equivocate against `v1`'s
  own history. `skipFill`'s existing `no_equivocation` field already
  proves exactly this for the *derived* correct class, using `hgap`;
  the honest-class version should be the same argument with the class
  widened, provided `v1` is honest, which `hv1` gives.
- **I4** (`chop` preserves `SynchronisedOn`) should hold *above the
  cut* and cannot hold at the base layer, where `chop` deliberately
  empties references. Expect the statement to need `G < n`, in the
  same shape as `supporters_chop`'s `1 ≤ m`.
- **I5** (`skipFill` preserves `SynchronisedOn`) is where I expect a
  genuine *negative* result, and it is the most valuable cell in the
  table. Coverage says every correct block references every correct
  block of the round below. A filled block copies the donor's
  references — it does **not** reference every correct block of the
  round below unless the donor did — and, worse, *old* blocks at the
  round above a filled block cannot reference it (they were built
  first; this is precisely SS3's argument). So `SynchronisedOn` is
  almost certainly **false** in the extension at the gap rounds. That
  is not a defect: it says the fill restores *production*, not
  *coverage*, which is exactly what §12 claims and no more. The
  integration arc should state the negative result on data — a witness
  where `SynchronisedOn (skipFill …)` fails — and then state the
  positive form: coverage holds *above* the fill (`r > sk.r`), which
  is what a liveness argument after recovery actually needs.
- **I6a** is the blocking item of its column and is not a preservation
  lemma but a *construction*: what does a validator hold, and what has
  it accepted, in a universe extended by a fill? The fill's blocks
  arrive in one message, so the natural definition adds them to every
  correct validator's `accepted` set at their gap round — at which
  point `accepted_inj` (at most one block per author per round) must be
  rechecked against `hgap`, and the whole of I1 and I6b–d becomes
  statable. Scope this before starting it; it may be the largest single
  item in the arc, and §5.3's budget question lives inside it.
- **I13/I15** (`Slots.chop` preserves fairness and shape) are the cells
  the first draft missed entirely, and they are prerequisites for I9 —
  a joiner reasoning about the truncation needs *its* schedule to be
  fair and spanning, not merely the original's. `FairScheduleOn` should
  shift by `d` and go through directly; `SpansEligible` will meet the
  subtraction wrinkle above. Unlike the layer-U cells these are pure
  arithmetic over the schedule — no universe, no views — so they are
  the best first exercise for anyone picking the arc up cold.

### 3.2 Transformers × transformers

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

### 3.3 Layer variants: parametrize once, instantiate thrice

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

This is the highest-value item in the plan and also the most invasive:
it touches existing code rather than adding to it, which every other
arc has avoided. It should be done as a *generalization with the old
statements retained as corollaries*, so nothing downstream breaks and
the diff is auditable.

### 3.4 What remains genuinely pairwise

Some combinations are not preservation facts and must be proved
directly. These are the ones with real content, and there are fewer
than the matrix suggests:

**I9 — GC × Adaptive: can a joiner recompute the schedule?** The
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

**I12 — DoS × Safe Skip: does a fill respect the budget?** See §5.3.

## 4. Proposed module plan

| Module | Contents |
|:---|:---|
| `Integration/Invariants.lean` | the named-invariant list, collected; the preservation-lemma interface |
| `Integration/Preservation.lean` | I1–I5: the layer-U table filled |
| `Integration/DeliveryFill.lean` | I6a–d: Safe Skip's delivery transformer, then its budget column |
| `Integration/ScheduleShape.lean` | I13–I15: fairness and shape under `Slots.chop` and `slotsOf` |
| `Integration/Commute.lean` | I7: `chop` ∘ `skipFill`, and the anchor-above-horizon condition |
| `Integration/RuleInterface.lean` | I8: the decision-relation interface; Mysticeti, Odontoceti, Hybrid as instances |
| `Integration/Joiner.lean` | I9: horizon-stable policies; the joiner's adaptive run |
| `Integration/Lifecycle.lean` | I10, I11: the crash-prone lifecycle end to end |
| `LeanDagTest/Integration.lean` | the negative witnesses (I5, I7's side condition) and the lifecycle exhibit |

Order matters, and the audit sharpened it:

1. **I2, I3, I5 first** — cheap, and they either confirm or refute the
   assumption that the fill is well-behaved. I2 is already done; the
   answer to I5 determines how much of the rest is worth stating.
2. **I13, I15 next** — small, and they unblock I9, the sharpest
   question in the arc.
3. **I6a before anything else in its column**, and only after scoping:
   it is a construction rather than a lemma, and §5.3's budget question
   is inside it. If it proves large, the honest move is to state the
   Safe Skip × DoS combination as *open* rather than to force it.
4. **I8 last.** It is the largest item, it touches existing code where
   every other arc only added, and its value depends on how many
   instances it ends up serving — which is known only once the rest is
   in place.

## 5. Risks and predictions

**5.1 The negative results are the valuable ones.** Three cells in this
plan look likely to be *false*: `SynchronisedOn` under `skipFill` (I5),
`chop`/`skipFill` commutation without the anchor condition (I7), and
horizon-stability for an unrestricted adaptive policy (I9). Each is
worth more than the corresponding positive would have been, because
each names a deployment constraint that no single arc can see. The arc
should be written expecting them, in the house style of
`bound_is_necessary` — a witness, not an apology.

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
suggests it does, but the *acceptance* side (`RefsAccepted`, and the
exposure condition) may see a burst. This is the combination most
likely to require a genuinely new argument rather than a preservation
lemma, and it should be scoped before it is started.

**5.4 Scope discipline.** The temptation in an integration arc is to
prove the full cross product because each individual proof is easy once
the interface exists. That would defeat the purpose. The rule for this
arc: **a combination gets its own theorem only if it has content that
the preservation lemmas do not already imply.** Everything else is a
one-line corollary at most, and more often simply an observation in the
report that the composition is immediate.

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
