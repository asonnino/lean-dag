import LeanDag.Support
import LeanDag.History

/-!
# Black Marlin — the commit rule

The rule of `delivery(r)` (Algorithm 2, L14–L17) of *DAG it off: Latency
Prefers No Common Coins* (arXiv:2508.14716v3), `black-marlin.md` §2. One
anchor is elected per round; the anchor of round `r` is committed when it
carries a quorum of support at round `r + 1`, **and** the anchor of round
`r + 1` both references it and carries a quorum of support at round
`r + 2`. Three rounds, no certificate round, and no threshold above
`n − f`, so the committee is the core's `n ≥ 3f + 1`.

**The DAG layer is consumed unchanged.** The paper's validity predicate
`V` — a quorum of distinct authors from the round below, all signed — is
`ValidWrt` (`spec.md` §3.2), and the paper's `supp` is the core's
`supporters`: `supp` excludes a supporter that references two blocks of
one author and round, which `ValidWrt.distinct_creators` already forbids.
The one addition the core makes is `ValidWrt.self_parent`, which the
paper does not require; it restricts the universes the results below
range over and is used by none of them (`black-marlin.md` §5).

**Strong references only.** A Black Marlin block carries a second,
time-bounded set of weak references to earlier rounds, and `past` follows
both while `strong` follows the first alone. The commit rule reads
`strong`, so the arc is stated over the core's `refs` and the paper's
`strong(B)` is `Reaches U B` less its reflexive step. Weak references
bear on delivery completeness rather than on the rule, and are not
modelled.

**Trusted core of the arc: definitions only.** No theorem lives in this
file or in `Decision.lean`; the `Decidable` instances are definitions by
`inferInstanceAs` and carry no proof content. Results are stated in
`<Result>/Statement.lean` and proved in the neighbouring `Proof.lean`,
after the partition the Mahi-Mahi arc introduced (`mahi-mahi.md` §9).
-/

namespace LeanDag

namespace BlackMarlin

/-- **The anchor rotation.** Black Marlin elects one anchor per round —
the paper's `RR(r)`, round-robin in a deployment.

A class of its own rather than the core's `Slots`, because the protocol
is indexed by rounds and not by slots: every rule below names round
`r + 1` explicitly, which under `Slots` would be a hypothesis
`slotRound (k + 1) = slotRound k + 1` carried through every statement.
The two are reconciled once, by `RotationIsSchedule`
(`Safety/Statement.lean`): under the pipelined schedule
`Slots.uniformSingle 1` an anchor of round `r` is a leader block of slot
`r`, so the arc's anchors are the core's candidates. -/
class Rotation (Validator : Type*) where
  /-- The validator elected to anchor round `r`. -/
  anchor : ℕ → Validator

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **`L` is an anchor block of round `r`**: a block of the universe, at
that round, by the validator the rotation elected for it.

A predicate rather than a function, because `RR` "returns both blocks"
when the elected validator equivocates: an anchor round has one elected
*author* but may hold several anchor *blocks*, and the uniqueness the
rule needs is a theorem about supported anchors, not a property of the
rotation. -/
def IsAnchor (U : BlockUniverse Validator BlockId Payload) (r : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = r ∧ (U.block L).creator = Rot.anchor r

instance (r : ℕ) (L : BlockId) : Decidable (IsAnchor U r L) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- **`supp(L) ≥ n − f`** for a block proposed at round `r`: a quorum of
distinct validators reference `L` from round `r + 1`.

The core's `supporters` counts authors rather than blocks, which is what
makes the count a quorum: an equivocator contributes one either way. The
paper's side condition — a supporter's block references no second block
of `L`'s author and round — is `ValidWrt.distinct_creators` and needs no
restatement here. -/
def Supported (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (supporters U L (r + 1)).card

instance (L : BlockId) (r : ℕ) : Decidable (Supported U L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- **The anchors of round `r + 1` that link `L` to the round above**:
the second clause of L16, as the set of blocks that witness it.

A `Finset` rather than a bare existential, so that the rule is decidable
on a concrete DAG and can be settled by `decide` — the same reason the
core keeps `certificates` as a `Finset`. The filter over `blocksAt` is
the paper's `∃B' ∈ DAG(r − 1)`; membership recovers `IsAnchor`
unchanged, since `blocksAt` already pins the round and the universe. -/
def linkers (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (r + 1)).filter
    (fun L' => (U.block L').creator = Rot.anchor (r + 1) ∧ L ∈ (U.block L').refs ∧
      Supported U L' (r + 1))

/-- **`L` is linked**: some anchor of the round above references it and is
itself supported.

Reference rather than reachability, which at a one-round gap is the same
thing: the paper writes `B ∈ strong(B')`, and every reference of a valid
block sits in the round immediately below it. -/
def Linked (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  (linkers U L r).Nonempty

instance (L : BlockId) (r : ℕ) : Decidable (Linked U L r) :=
  inferInstanceAs (Decidable (Finset.Nonempty _))

/-- **The commit rule** (L14–L17). The anchor of round `r` is committed
when it is supported and linked.

Three conjuncts, in the order the paper's line reads them. The rule is
the whole of what safety consumes: `commit(B)`'s recursion over
`strong(B) \ D`, and the deterministic sort of `past(B)`, decide the
*order* in which blocks are delivered, but every block they deliver lies
in the causal history of a block this rule admitted — which is why the
chain and prefix results below are stated about `history` rather than
about the sort (`black-marlin.md` §4). -/
def Committed (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  IsAnchor U r L ∧ Supported U L r ∧ Linked U L r

instance (L : BlockId) (r : ℕ) : Decidable (Committed U L r) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

end BlackMarlin

end LeanDag
