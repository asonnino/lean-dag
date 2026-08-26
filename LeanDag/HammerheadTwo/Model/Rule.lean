import LeanDag.Mysticeti
import LeanDag.Causality

/-!
# Hammerhead 2.0: the base-protocol interface

The paper abstracts the protocol it runs on as four assumptions, A1–A4
(`hammerhead-two.md` §0.1): rounds and slots, causal completeness, a
direct decision predicate, and safety and liveness for every fixed
configuration. `BaseRule` is that abstraction as a Lean structure — its
data — and `BaseRule.Laws` the proposition the data must satisfy. The
arc never counts anything and never inspects a quorum: the leader-count
mechanism is stated over an arbitrary `BaseRule` satisfying `Laws`, and
the three commit rules of this development — Mysticeti, Odontoceti (the
paper's Blue Bottle) and Nemo — are each shown to, as a result with a
`Statement` and a `Proof` (`Mysticeti/`, and Phase 5's two).

The universe and view types are *fields*, bundled in `Type`, because
the three rules do not share them: the Byzantine rules use
`BlockUniverse` and `View`, the crash rule its own `Nemo.Universe` and
`Nemo.View`. Bundling puts each rule's fault class on its instantiation
and nothing on the interface, which is what lets Nemo — whose safety
needs no fault class at all — instantiate it without one.

The schedule is an explicit argument of `Decided` rather than an
instance: the arc's whole subject is several `Slots` instances on one
validator type, one per configuration, and every use names its schedule.

Liveness is not here. What the paper's A4 asks of a fixed configuration
beyond agreement is stated in Phase 3 as a clause on a schedule, over a
structure extending this one, so that this file is not reopened.

**Trusted core of the arc: definitions only.** No theorem and no proof
term lives in this file; the `Decidable` instances are definitions by
`inferInstanceAs` or field projections and carry no proof content. Results are stated in
`<Result>/Statement.lean` files and proved in their `Proof.lean`
(`hammerhead-two.md` §10).
-/

namespace LeanDag

namespace HammerheadTwo

/-- **The base protocol, as the paper assumes it — the data.** A universe
of blocks with its views, the direct decision predicate, and a decision
relation parametric in the schedule. The laws these must satisfy are
`BaseRule.Laws` below, a proposition each instantiation is proved to
meet in its own `Statement`/`Proof` pair.

`historyView` is the view a validator measures on — the anchor's causal
history, which the paper's `GetSubDag` computes. An instantiation may
build it however it likes: the law `historyView_ids` pins its ids to
`historyFrom`, the shared history function of `Causality.lean`, so that
the window is a function of the universe and the anchor alone. -/
structure BaseRule (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (BlockId : Type) [DecidableEq BlockId] (Payload : Type) where
  /-- The universe type of the base development. -/
  Universe : Type
  /-- The view type, indexed by universe. -/
  View : Universe → Type
  /-- The block an id denotes: round, creator and references. -/
  block : Universe → BlockId → Block Validator BlockId Payload
  /-- The ids of the universe. -/
  ids : Universe → Finset BlockId
  /-- The ids a view holds. -/
  viewIds : ∀ {U : Universe}, View U → Finset BlockId
  /-- The full view: every block of the universe. -/
  full : ∀ U : Universe, View U
  /-- The causal history of a block of the universe, as a view. -/
  historyView : ∀ (U : Universe) (A : BlockId), A ∈ ids U → View U
  /-- **A3.** The length of a wave: the rounds the direct rule reads from a
  slot's proposal. Three for Mysticeti, two for the two-round rules. -/
  waveLength : ℕ
  /-- **A3.** The direct commit predicate, as judged from a view: block `L`
  proposed at round `r` is directly committed. -/
  DirectCommitIn : ∀ {U : Universe}, View U → BlockId → ℕ → Prop
  /-- The direct predicate is decidable, so a validator — and a witness —
  can compute the window count. -/
  decDirect : ∀ {U : Universe} (V : View U) (L : BlockId) (r : ℕ),
    Decidable (DirectCommitIn V L r)
  /-- The decision relation under a schedule: on view `V`, slot `k` is
  decided with verdict `v` — `some L` a commit, `none` a skip. -/
  Decided : Slots Validator → ∀ {U : Universe}, View U → ℕ → Option BlockId → Prop

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

namespace BaseRule

/-- The rule's own decidability of the direct predicate, as an instance. -/
instance instDecidableDirectCommitIn (R : BaseRule Validator BlockId Payload)
    {U : R.Universe} (V : R.View U) (L : BlockId) (r : ℕ) :
    Decidable (R.DirectCommitIn V L r) :=
  R.decDirect V L r

/-- `L` is a candidate block for slot `k` of schedule `S`: the right round,
the right author. The same conjunction every rule of this development
states, here over the interface's `block` and `ids` so that the arc has
one candidate predicate for all three. -/
def IsLeaderBlock (R : BaseRule Validator BlockId Payload) (S : Slots Validator)
    (U : R.Universe) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ R.ids U ∧ (R.block U L).round = S.slotRound k ∧ (R.block U L).creator = S.leader k

instance instDecidableIsLeaderBlock (R : BaseRule Validator BlockId Payload)
    (S : Slots Validator) (U : R.Universe) (k : ℕ) (L : BlockId) :
    Decidable (R.IsLeaderBlock S U k L) :=
  inferInstanceAs (Decidable (L ∈ R.ids U ∧ (R.block U L).round = S.slotRound k ∧
    (R.block U L).creator = S.leader k))

/-- **The laws of a base rule** — what the leader-count mechanism
consumes of the protocol, and what each instantiation is proved to
satisfy. `view_subset` and `view_complete` are the paper's A2 (a
validator holds a block only with its whole causal history); `agree` is
the safety half of A4 (for a fixed schedule, verdicts agree across
views); `decided_of_directCommitIn` ties the direct predicate to the
relation, which is what makes the window count a count of *verdicts*:
two directly committed candidates of one slot are one block, by
`agree`. The liveness half of A4 is stated in Phase 3 over an extension
of the data. -/
structure Laws (R : BaseRule Validator BlockId Payload) : Prop where
  /-- A view holds only blocks of the universe. -/
  view_subset : ∀ {U : R.Universe} (V : R.View U), R.viewIds V ⊆ R.ids U
  /-- **A2.** A view is closed downward: it holds what its blocks reference. -/
  view_complete : ∀ {U : R.Universe} (V : R.View U),
    ∀ i ∈ R.viewIds V, ∀ j ∈ (R.block U i).refs, j ∈ R.viewIds V
  /-- The full view holds exactly the universe. -/
  full_ids : ∀ U, R.viewIds (R.full U) = R.ids U
  /-- The history view holds exactly the history. -/
  historyView_ids : ∀ U A (hA : A ∈ R.ids U),
    R.viewIds (R.historyView U A hA) = historyFrom (R.block U) A
  /-- **A4, safety.** For a fixed schedule, verdicts agree across views. -/
  agree : ∀ (S : Slots Validator) {U : R.Universe} (V₁ V₂ : R.View U) (k : ℕ)
    (v₁ v₂ : Option BlockId), R.Decided S V₁ k v₁ → R.Decided S V₂ k v₂ → v₁ = v₂
  /-- A directly committed candidate of a slot is a commit verdict. -/
  decided_of_directCommitIn : ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U)
    (k : ℕ) (L : BlockId), R.IsLeaderBlock S U k L →
    R.DirectCommitIn V L (S.slotRound k) → R.Decided S V k (some L)

end BaseRule

/-- **An update rule**: from the current leader count and back-off, the
universe and the anchor block, the next count and back-off. Safety is
stated for every such function (`hammerhead-two.md` §0); the paper's
AIMD rule is one instance (`Model/Window.lean`). -/
abbrev UpdateRule (R : BaseRule Validator BlockId Payload) : Type :=
  ℕ → ℕ → R.Universe → BlockId → ℕ × ℕ

end HammerheadTwo

end LeanDag
