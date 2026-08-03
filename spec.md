# lean-dag — Specification

Formalize, in Lean 4 + Mathlib, the core combinatorial structures and safety
arguments underlying DAG-based BFT consensus, starting with the fragment of
**Mysticeti** needed to state and prove its key persistence/safety lemma,
then extending outward.

Sections marked **(assumption)** are modeling choices made where the
original notes were open-ended — flag any you want changed.

## 1. Scope

- **Phase 1 (main target):** static block DAG structure, quorum-intersection
  combinatorics, and the causal-persistence theorem from the notes (T0–T3).
  This is the mathematical core of why Mysticeti-style protocols are safe.
- **Phase 2:** views, round leaders, the direct-commit rule, and agreement
  between correct validators on committed blocks (T4–T5).
- **Phase 3 (stretch):** total-order safety across the commit sequence;
  liveness under partial synchrony. Liveness needs network timing axioms
  (GST, message delay bounds) rather than pure DAG combinatorics — scope it
  separately once Phase 1–2 land.

## 2. System model

**(assumption)** The fault model is **bundled as a class**, not threaded as
section variables. This fixes the signature of `ValidWrt`, `BlockUniverse`,
and every theorem below, so it is worth settling first.

```lean
class Faults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  f : ℕ
  byzantine : Finset Validator
  card_validators : Fintype.card Validator = 3 * f + 1
  card_byzantine : byzantine.card ≤ f

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*}
variable {Payload : Type*}

def Correct : Finset Validator := (F.byzantine)ᶜ
```

Bundling wins on two counts, both verified against the built file rather
than assumed:

- **The cardinality hypotheses ride on the instance**, so they never appear
  as explicit arguments and no `include` is ever needed. With section
  variables every theorem carried `(f) (Byzantine) (hcard) (hbyz)` before
  its real arguments, and every declaration needed `include hcard hbyz in`,
  since `Prop`-valued variables are not auto-included.
- **`Correct` takes no argument** — the instance is inferred from
  `Validator`. As a section-variable `def` it necessarily absorbed
  `Byzantine` as a parameter, forcing `Correct Byzantine` at every use.

**Refer to the fault bound as `F.f`, never as a bare `f`.** With `f` as a
class field, `Faults.f` takes `Validator` explicitly, and a bare `f` in a
position expecting only an `ℕ` gives Lean nothing to determine the type
from — it elaborates to a metavariable and fails confusingly later. Naming
the instance `F` and writing `F.f`, `F.byzantine`, `F.card_validators`,
`F.card_byzantine` keeps every reference unambiguous.

Remaining notes:

- `DecidableEq Validator` is needed for `creatorsOf` (§3.2), a
  `Finset.image` into `Validator`. **`DecidableEq BlockId` is not needed**:
  `Finset α` itself imposes no decidable equality — only operations like
  `image`, `∪`, and `∩` do, and here those all land in `Validator`. Expect
  to need it locally in `Commit.lean`, where T4's support set is a
  `Finset.filter` over a predicate mentioning `i ∈ (U.block q).refs`;
  introduce it there rather than globally.
- **(assumption)** `Fintype.card Validator = 3 * f + 1` exactly (notes say
  "3f+1 validators").
- Rounds are plain `ℕ` throughout. No `Round` abbreviation — it would buy
  nothing, and two spellings for one type reliably drift apart.

Two consequences worth naming once rather than re-deriving at each use:

- `exists_correct_of_card`: any `S : Finset Validator` with
  `F.f + 1 ≤ S.card` contains a correct validator, since
  `F.byzantine.card ≤ F.f` means `S` cannot be wholly Byzantine. Used by T0,
  and so reaches T3 and T5 through T0'.
- `card_correct : 2 * F.f + 1 ≤ Correct.card`. Note this is currently used
  by **nothing** — T0, T3, and T5 all route through `F.card_byzantine`
  instead. It is kept because liveness (T7) would want it, but it is not on
  any Phase 1–2 path.

## 3. Blocks and the DAG

### 3.1 Block and BlockId

Blocks are referenced by **id**, not by value. `BlockId` is an opaque type
with `DecidableEq`; `Block` itself is then non-recursive:

- `round : ℕ`
- `creator : Validator`
- `refs : Finset BlockId` — pointers to blocks at the preceding round
- `payload : Payload` — opaque, per the notes; inert throughout Phase 1.
  `Payload` is a section variable (§2), so the structure elaborates as
  `Block Payload` and the parameter rides along implicitly everywhere.

This is not merely stylistic. The value-recursive alternative (`refs :
Finset Block`) almost certainly does not elaborate in Lean 4: nested
inductive types may recurse through `List`, but `Finset` is built on
`Multiset`, itself a quotient of `List`, and the nested-inductive
construction does not support recursion through a quotient. Indirection via
ids sidesteps that, and matches real implementations where a `BlockId` is a
hash of the block.

The cost is that a `BlockId` means nothing on its own — it must be resolved
through a lookup function to yield a `Block`, so validity (§3.2) and causal
history (§3.4) both take that lookup as a parameter. The benefit is that
"same block" becomes **same id**, which is what every uniqueness claim below
(non-equivocation, T1, T5) actually wants; content equality is strictly
weaker and never needed.

**(assumption)** Ids are *not* assumed collision-free — `U.block` need not
be injective on `U.ids`. Real ids are content hashes so injectivity would be
realistic, but nothing below needs it and omitting it keeps the theorems
strictly stronger. See §5 Q4.

**(assumption)** Only "strong" edges to the immediately preceding round are
modeled — no weak edges to older rounds. Real Mysticeti has weak edges (to
avoid dropping blocks that missed the quorum cutoff); omitting them keeps
Phase 1 simpler and does not affect persistence.

**(assumption)** Round-0 blocks are genesis blocks with no refs. Nothing
constrains how many a validator has beyond ordinary non-equivocation (§3.3),
which already gives correct validators at most one; a Byzantine validator
may have several, and no theorem cares.

### 3.2 Block validity

Validity dereferences refs, so it takes a **lookup function**
`blk : BlockId → Block`, not a universe. This is forced: §3.3 makes "every
member is valid" a field of `BlockUniverse`, and a structure field cannot
mention the structure being defined. With `blk` as the parameter that field
reads `∀ i ∈ ids, ValidWrt block (block i)`, referring only to siblings.

Two notations for "the validators behind a set of ids", split so that one
set of lemmas serves both blocks and bare id-sets:

```lean
creatorsOf blk (s : Finset BlockId) : Finset Validator :=
  s.image (fun i => (blk i).creator)

creators blk b : Finset Validator := creatorsOf blk b.refs
```

The generalized form is not cosmetic. T3's hypothesis, T4's commit rule, and
T0' all quantify over id-sets that are *not* any block's refs; a block-only
`creators` would force each of them to inline the image by hand and would
leave T0' unusable at every one of its call sites.

Then `ValidWrt blk b` holds iff:

- **Predecessor:** `∀ i ∈ b.refs, (blk i).round + 1 = b.round`
- **Distinct creators:**
  `∀ i j ∈ b.refs, (blk i).creator = (blk j).creator → i = j`
- **Quorum:** `b.round > 0 → 2 * F.f + 1 ≤ (creators blk b).card`

Three notes on the shape.

**Predecessor is stated additively**, not as `(blk i).round = b.round - 1`.
That avoids ℕ-subtraction entirely, and makes the genesis case *derivable*
rather than a separate branch: if `b.round = 0` then `(blk i).round + 1 = 0`
is impossible, so `b.refs = ∅` falls out. Only the quorum condition needs a
round guard.

**Quorum is stated on the creator set**, not on `b.refs.card`. This is the
form every downstream proof wants, and it is the more faithful reading of
"2f+1 blocks from the previous round" — the protocol means 2f+1
*validators*. Stating it directly makes `Valid.creators_quorum` definitional
rather than a lemma, and removes any `card_creators` bridge from the
critical path. With distinctness also present `b.refs.card ≥ 2f+1` still
follows, so nothing is lost.

**Distinct creators earns its keep only at T5.** It is a genuine protocol
rule — a block must not cite the same author twice — but it is worth being
precise about where it is needed, because the natural guess is wrong. T3
does *not* use it: the validator extracted from a quorum intersection is
**correct** by construction, and universe-level non-equivocation (§3.3)
already makes that validator's block unique. Distinctness is needed only in
T5's Byzantine-leader branch, where the equivocating author is precisely the
one non-equivocation says nothing about.

### 3.3 Block universe

Non-equivocation constrains *what correct validators ever author*, not what
a particular DAG happens to contain. Stating it per-DAG would be too weak:
two DAGs could each satisfy "at most one block per correct validator per
round" while containing *different* such blocks — a correct validator
equivocating, with both DAGs looking well-formed. That would silently break
T5. So the constraint lives one level up.

A **`BlockUniverse` `U`** is every block that exists, authored by anyone:

- `ids : Finset BlockId` — which blocks exist;
- `block : BlockId → Block` — what each one is;

subject to:

- **Complete:** `∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids`.
- **Valid:** `∀ i ∈ ids, ValidWrt block (block i)` (§3.2) — mentions only
  sibling fields, which is why §3.2 takes a lookup function.
- **Correct validators do not equivocate:** for `v ∈ Correct` and any round
  `r`, at most one `i ∈ ids` has `(block i).creator = v` and
  `(block i).round = r`. Byzantine validators are unconstrained.

**(assumption)** `block` is *total*, with junk outside `ids`, rather than
`BlockId → Option Block`. Every theorem quantifies over `i ∈ ids`, so the
junk is never observed, and this avoids `Option`-unwrapping throughout.

**(assumption)** Non-equivocation is a universe field rather than (a) an
ambient hypothesis over all inhabitants of `BlockId`, or (b) a structural
`authored : Validator → ℕ → Option BlockId` map. Option (b) makes
Byzantine equivocation awkward to express, which we need; (a) detaches the
constraint from any carrier set.

### 3.4 Causal history

`Reaches U c b` — "`b` is in the causal history of `c`" — the
reflexive-transitive closure of `refs` resolved through `U`, and the target
relation for T3.

Since refs are ids this is a relation on `BlockId × BlockId` indexed by `U`,
definable via `Relation.ReflTransGen` on
`fun i j => j ∈ (U.block i).refs`. The predecessor condition (§3.2) makes
`round` strictly decrease along `refs`, supplying the induction T3 needs.

### 3.5 Views (Phase 2)

Phase 1 needs no views — T0–T3 are all universe-level. They first matter at
T4/T5, where committing is a decision an individual validator makes from its
own local DAG.

A **view** is a `V : Finset BlockId` with `V ⊆ U.ids`, itself complete:
`∀ i ∈ V, ∀ j ∈ (U.block i).refs, j ∈ V`. Views share `U.block` — they
disagree about *which* blocks they hold, never about what an id means — and
inherit validity and non-equivocation from `U`. Different correct validators
may hold different views; that asymmetry is the entire point of T5.

## 4. Theorem roadmap

### Phase 1

- **T0 — Quorum intersection.** Any two `Q₁ Q₂ : Finset Validator` with
  `card ≥ 2f+1` (out of `3f+1` total) satisfy `(Q₁ ∩ Q₂).card ≥ f + 1`,
  hence contain a correct validator by `exists_correct_of_card` (§2). Pure
  `Finset`/`Fintype` cardinality — likely close to a one-liner from
  `Finset.card_inter_add_card_union` or similar.

  Corollary **T0'**, stated on **id-sets** rather than blocks: for
  `s t : Finset BlockId` with `2 * F.f + 1 ≤ (creatorsOf blk s).card` and
  likewise for `t`, some correct validator lies in
  `creatorsOf blk s ∩ creatorsOf blk t`.

  That generality is required, not incidental: T3 intersects a block's refs
  with the arbitrary set `Q`, and T5 intersects `Q₁` with `Q₂` — neither of
  which is any block's refs. A block-level phrasing would fit none of the
  three call sites. For a block, apply it with `s := b.refs` and discharge
  the quorum hypothesis from validity (§3.2, definitional).

- **T1 — Non-equivocation as id equality.** For `v ∈ Correct`, any two ids
  `i j ∈ U.ids` with creator `v` at the same round satisfy `i = j`.
  Immediate from §3.3, but it is what lets a quorum-intersection argument
  land on a *single concrete id* instead of an existential.

- **T2 — Causal history composes and runs downward.** `Reaches U` is
  reflexive, closed under single reference steps, and transitive — all three
  inherited from `Relation.ReflTransGen`. The content is
  `round_le_of_reaches`: following a reference strictly decreases the round
  (§3.2's predecessor condition), so causal history never climbs.

  Earlier drafts called this "well-founded", which overstates it. T3 inducts
  on the round *number*, an ordinary `ℕ`, not on `Reaches`; no
  `WellFoundedRelation` instance is needed, only the fact that a block's
  references sit at a strictly smaller round. Supporting lemmas:
  `mem_ids_of_reaches` (completeness propagates along a walk) and
  `eq_of_reaches_of_refs_empty` (genesis blocks are causal-history leaves).

- **T3 — Persistence (the theorem from the notes).** Precise statement:

  > Let `b ∈ U.ids` with `(U.block b).round = r`. Suppose `Q ⊆ U.ids` is a
  > set of ids at round `r+1`, all of which reference `b`
  > (`∀ q ∈ Q, b ∈ (U.block q).refs`), and whose creator set is a quorum:
  > `2 * F.f + 1 ≤ (creatorsOf U.block Q).card`. Then for every `c ∈ U.ids` with
  > `(U.block c).round ≥ r + 2`, `Reaches U c b`.

  **The bound is `r + 2`, and it is tight.** A round-`(r+1)` block outside
  `Q` need not reach `b` at all, so the naive "every block after round `r`"
  reading is false. Counterexample: `f = 1`, validators `{A,B,C,D}`, quorum
  3. Let `b` be A's round-`r` block and `Q` the round-`(r+1)` blocks of
  `A,B,C`, all referencing `b`. D's round-`(r+1)` block must reference 3
  round-`r` blocks and may pick `{B,C,D}`, omitting `b`; all its refs sit at
  round `r`, so `b` is not in its causal history. Quorum intersection needs
  *two* ref-quorums to compare, and `r+2` is the first round that has them.

  The hypothesis is on `Q`'s *creator set*, not `Q.card`: `Q` is an
  arbitrary id set here, not one block's refs, so it carries no distinctness
  invariant of its own and `Q.card` would be the wrong measure. In every
  application `Q` does come from distinct validators, so this costs nothing
  at call sites.

  Proof sketch — induction on `(U.block c).round`, with the quorum argument
  in the **base case only**:

  - **Base, `round c = r + 2`.** `c`'s refs carry a validator quorum (§3.2,
    definitional), so T0' applied to `(c.refs, Q)` yields a **correct** `v`
    in `creators U.block (U.block c) ∩ creatorsOf U.block Q`. Unfolding both
    memberships with `Finset.mem_image` gives `i ∈ c.refs` and `q ∈ Q`, each
    authored by `v` and each at round `r+1` — the first by the predecessor
    condition, the second by hypothesis. T1 makes them **the same id**, and
    that id references `b` directly. Compose by T2.
  - **Step, `round c = n + 1` with `n ≥ r + 2`.** No intersection needed:
    `c`'s refs are nonempty (the quorum is `≥ 2f+1 ≥ 1`, and the image of
    `∅` is `∅`) and sit at round `n ≥ r + 2`, so the IH applies to any one
    of them; compose by T2.

  Above the base layer, height is carried by transitivity alone — quorum
  intersection and non-equivocation fire exactly once, at `r+2`.

  **Distinctness (§3.2) is not used in this proof.** The validator extracted
  from the intersection is correct, so T1 alone supplies the uniqueness
  identifying `i` with `q`. What the induction does rely on across rounds is
  completeness (so refs land in `U.ids` and the IH applies) plus the quorum
  and predecessor conditions at every intervening round — all supplied by
  §3.3's validity field.

### Phase 2

- **T4 — Round leaders and the commit rule.** A deterministic
  `leader : ℕ → Validator` (mechanism TBD — round-robin is simplest to
  formalize first). Define **directly committed in a view**:
  `DirectlyCommittedIn U V r i` — note it takes the universe *and* the view,
  since the predicate dereferences ids through `U.block` while quantifying
  over `V` — holds when `i ∈ V` is a round-`r` block by `leader r`, and the
  *support set* `Q := {q ∈ V | (U.block q).round = r+1 ∧ i ∈ (U.block q).refs}`
  satisfies `2 * F.f + 1 ≤ (creatorsOf U.block Q).card`. That is T3's hypothesis
  instantiated at the leader block and evaluated inside `V`.

  The predicate must be **view-relative**: committing is a decision an
  individual validator makes from its own local DAG. Were it universe-level,
  T5 would have nothing to compare.

- **T5 — Commit agreement.** If `DirectlyCommittedIn U V₁ r i₁` and
  `DirectlyCommittedIn U V₂ r i₂` for two complete views of the *same*
  universe `U`, then `i₁ = i₂`. This is *no-conflicting-commit*, not "both decide" — a
  validator whose view lacks the quorum simply has not decided yet, which is
  not disagreement.

  **One uniform proof — no case split on whether the leader is honest.**
  Let `Q₁, Q₂` be the two support sets. Their creator sets are quorums, so
  T0' gives a correct `v` in both. Unfolding, `v` authored some `q₁ ∈ Q₁`
  and some `q₂ ∈ Q₂`, both at round `r+1` and both in `U.ids`; since `v` is
  correct, T1 forces `q₁ = q₂ =: q`. Then `(U.block q).refs` contains both
  `i₁` and `i₂`, which are round-`r` ids with the **same creator**
  (`leader r`, by definition of `DirectlyCommittedIn`). Distinctness (§3.2)
  gives `i₁ = i₂`.

  Note where the leader's honesty would have entered and does not: the
  argument never asks whether `leader r` equivocates, only that `i₁` and
  `i₂` share a creator — which the commit rule guarantees outright. A
  correct leader *also* yields `i₁ = i₂` directly from non-equivocation, but
  that is a shortcut, not a required branch.

  So commit agreement holds even against an equivocating leader, and it is
  **distinctness** rather than non-equivocation that buys it — the one place
  in the development where that invariant is load-bearing.

### Phase 3 (stretch)

- **T6a — Causal history is view-closed.** For a complete view `V` and
  `i ∈ V`, `Reaches U i j` implies `j ∈ V`, and reachability computed inside
  `V` coincides with reachability in `U`. Not needed for T3 or T5, both of
  which stay universe-level; it becomes necessary once conclusions of the
  form "and therefore `b` is in *my* view" are wanted, i.e. for ordering.

- **T6 — Total order safety.** The sequence of committed leaders, and blocks
  ordered via their causal history, is agreed upon by all correct
  validators. The actual end-to-end safety property; T5 is close but total
  order needs one more step (ordering non-leader blocks relative to
  committed leaders).

- **T7 — Liveness.** Under partial synchrony, leaders eventually get
  committed. Needs timing/network axioms, not just DAG structure — an
  explicit decision to include or drop, not an oversight.

## 5. Open questions

1. Weak edges (§3.1) — include now or defer?
2. Leader selection for T4 — round-robin, stake-weighted, or left abstract
   as an arbitrary function?
3. Is Phase 3 in scope, or is T5 the practical finish line?
4. Should ids be assumed collision-free (`U.block` injective on `U.ids`),
   modeling a content hash? Currently *not* assumed, so the theorems stay
   maximally general. Revisit only if a proof demands it.

## 6. Layout

- `LeanDag/Validators.lean` — §2 (`card_correct`, `exists_correct_of_card`),
  T0
- `LeanDag/Block.lean` — §3.1 (`Block`), §3.2 (`creatorsOf`, `creators`,
  `ValidWrt`), T0'
- `LeanDag/BlockDag.lean` — §3.3 (universe), T1
- `LeanDag/CausalHistory.lean` — §3.4, T2
- `LeanDag/Persistence.lean` — T3
- `LeanDag/Commit.lean` — §3.5 (views), T4–T5 (Phase 2)
- `LeanDagTest/` — concrete models confirming the definitions are
  satisfiable. Built by default, so a change that empties `ValidWrt` or
  `BlockUniverse` fails the build rather than silently making every theorem
  vacuously true. Worth extending with a model at each new layer.

Parameterizing validity by the lookup function (§3.2) keeps `ValidWrt`,
`creatorsOf`, and T0' free of any `BlockUniverse` dependency — T0' quantifies
over bare `Finset BlockId`s and never mentions a universe — so all of them
sit beside `Block` rather than being pushed into `BlockDag.lean` to dodge a
circular import. `BlockDag.lean` is left holding only what genuinely needs
the universe: the structure itself and T1.

**Order of attack.** `Validators.lean` first — T0 is self-contained `Finset`
cardinality and a good calibration exercise for how much Mathlib does for
you. `Block.lean` is then definitions plus T0', which is just T0 with the
quorum hypotheses discharged. `BlockDag.lean` and `CausalHistory.lean` are
mostly definitional, with T1 falling straight out of the universe fields.
T3 is the first substantial proof.

Dependencies run strictly downward in that list — worth confirming as you
go, since the §3.2 lookup-function choice is what keeps it acyclic.

**What Phase 1 actually requires.** Completeness, the predecessor condition,
the creator-set quorum, and non-equivocation — four conditions. Not
distinctness, not views, not view-closure. Useful as a check while
implementing: if a Phase 1 proof reaches for any of those three, something
has gone sideways.
