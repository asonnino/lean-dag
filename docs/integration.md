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
quadratic.

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
been collected. These are the universe-level `Prop`s that arcs consume
as hypotheses:

| Invariant | Introduced | Consumed by |
|:---|:---|:---|
| the `BlockUniverse` laws (P1–P5) | §2.3 | everything |
| `Populated U r`, `PopulatedOn U T r` | §6.3 | every liveness result |
| `SynchronisedOn U T R` | §6.4 | every liveness result |
| `DoSValid U` | §8.2 | the exposure bound (C2, C1′) |
| `HonestNoEquiv U` | §14.1 | every hybrid safety theorem |
| `UniformBudget D T`, `RefsAccepted D` | §8.4 | the storage bounds (B4, B) |
| `Decided U V k v` facts | §3.5 | the ledger, chain quality |

Seven entries, and the last is a family rather than a single `Prop`.
That is the whole surface. **Every theorem in the development is
stated against some subset of this list** — which is exactly the
property that makes the linear strategy work.

The invariant list is also the thing to *audit* when a new arc is
added: an arc that introduces a hypothesis outside this list has, by
that act, created a new column in every future composition table. The
integration arc should treat "does this need a new named invariant?"
as a design question, not a bookkeeping one.

## 3. The strategy: preservation, not combination

### 3.1 Transformers × invariants

The core move. For each transformer `F` and each named invariant `I`,
prove one lemma:

    I U  →  I (F U)

Then any property `P` whose statement depends only on named invariants
transfers to `F U` **for free**, with no new proof and no mention of
`P` anywhere. Two transformers × seven invariants is fourteen lemmas,
most of them a few lines, against thirty-six pairwise combinations that
would each need real work.

The pattern is already established — GC's `chop` carries most of its
row, and this is why §9 reads as cleanly as it does:

| | `chop U G` | `skipFill` |
|:---|:---|:---|
| DAG laws | ✅ (the `chop` definition) | ✅ (SS1) |
| `Populated` | ✅ `populated_chop` | ✅ SS2 (`skipFill_populatedOn`) |
| `Decided` | ✅ G3 (`decided_chop`) | ✅ SS5 (`decided_fill`) |
| `DoSValid` | ✅ `dosValid_chop` | **I1 — open** |
| `HonestNoEquiv` | **I2 — open** | **I3 — open** |
| `SynchronisedOn` | **I4 — open** | **I5 — open** |
| budgets (`UniformBudget`, `RefsAccepted`) | ✅ `byzBudget_chopD`, `refsAccepted_chopD` | **I6 — open** |

Seven open cells, each a single lemma, and filling them closes far more
than seven combinations. Predictions worth recording before the work,
since a plan that cannot be wrong is not a plan:

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
  already met in `Slots.chop`'s keying clause; expect every
  `chop`-preservation lemma about rounds to pay it.
- **I3** (`skipFill` preserves `HonestNoEquiv`) is the interesting one.
  The fill creates blocks authored by `v1`, who is honest — so the
  proof must show the filled blocks do not equivocate against `v1`'s
  own history. `skipFill`'s existing `no_equivocation` field already
  proves exactly this for the *derived* correct class, using `hgap`;
  the honest-class version should be the same argument with the class
  widened, provided `v1` is honest, which `hv1` gives.
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
- **I1** (`skipFill` preserves `DoSValid`) is a real question with a
  possible negative answer, for a different reason: the fill creates
  one block per gap round in a single message, and the exposure /
  novelty accounting of §8 was designed around blocks arriving one at
  a time. See §5.3 below.

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
| `Integration/Preservation.lean` | I1–I6: the transformer × invariant table filled |
| `Integration/Commute.lean` | I7: `chop` ∘ `skipFill`, and the anchor-above-horizon condition |
| `Integration/RuleInterface.lean` | I8: the decision-relation interface; Mysticeti, Odontoceti, Hybrid as instances |
| `Integration/Joiner.lean` | I9: horizon-stable policies; the joiner's adaptive run |
| `Integration/Lifecycle.lean` | I10, I11: the crash-prone lifecycle end to end |
| `LeanDagTest/Integration.lean` | the negative witnesses (I5, I7's side condition) and the lifecycle exhibit |

Order matters: **I2, I3, I5 first** — they are cheap, they either
confirm or refute the assumption that the fill is well-behaved, and the
answer to I5 determines how much of the rest is worth stating. I8 is
the largest item and should not start until the preservation table is
complete, since its value depends on how many instances it actually
serves.

## 5. Risks and predictions

**5.1 The negative results are the valuable ones.** Three cells in this
plan look likely to be *false*: `SynchronisedOn` under `skipFill` (I5),
`chop`/`skipFill` commutation without the anchor condition (I7), and
horizon-stability for an unrestricted adaptive policy (I9). Each is
worth more than the corresponding positive would have been, because
each names a deployment constraint that no single arc can see. The arc
should be written expecting them, in the house style of
`bound_is_necessary` — a witness, not an apology.

**5.2 The interface may not be as clean as §2 suggests.** The claim
that every theorem is stated against the seven named invariants is an
*assertion from a survey*, not a verified fact. The first task of the
arc is to check it mechanically — the extraction in `scripts/` already
walks every declaration's dependencies, so "which hypotheses does this
capstone actually reach?" is a query, not a reading exercise. If the
survey is wrong, the plan needs revising before any Lean is written.

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
