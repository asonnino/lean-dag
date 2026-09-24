import LeanDag.Steelhead.Model.RulePair
/-!
# Steelhead — the liveness clauses a rule supplies

The paper states Theorem 2 for any rule of its interface, not for the
Mysticeti and Mahi-Mahi pair alone. The descent, the floor chain and the
round-robin count read a rule only through three facts about it, and
this file names them, so that the generic statements in
`Liveness/Statement.lean` quantify over any anchored rule that has them
and the two pairs of `Model/Pair.lean` become instances:

* **`CommitsUnderSync`**, the paper's clause A4 on the DAG: once a
  reliable quorum has synchronised and populated the rounds up to a
  slot's decision round, a reliably led slot is directly committed in
  every view that holds them;
* **`SkipsSilent`**: a slot whose leader has no block at its round is
  directly skipped in every view holding its decision round, once a
  quorum populates the rounds above the slot up to it;
* **`LeastLinked`**: every nonempty rung has a tie-break choice, which is
  what the indirect commit needs to fire.

`FloorHopOf` is the hop of the floor chain at a rule: `FloorHop`
(`Model/Decision.lean`) read through the rule's own wave offset rather
than through a wavelength function.

Each clause is a statement about one rule on one universe. For a
composite (`Model/Compose.lean`) the first two hold as soon as they hold
for every rule of the family, since the composite's decision round and
direct predicates at a slot are the slot's rule's (`Liveness/Statement.lean`,
SH6a and SH6c).

Theorem 3 reads four more, which the chain and the period sequence need:

* **`CommitLaws`** and **`ViewLaws`**: a commit is witnessed in the view
  it is taken in, a direct commit putting its candidate there and a link
  putting it in the anchor's history; `ViewLaws` adds that a direct skip
  rests on a block of the view at or above the slot's round. What reading
  an anchor's history inside the view that found it needs;
* **`GoodCommits`**: the good set of a round, the validators whose
  round-`r` block the asynchronous rule directly commits, commits in every
  view holding the round's decision round. The counting lemma of each
  rule bounds that set from below;
* **`RunWithin`**, the paper's clause A5 in its run form: in every window
  of `c` slots below a horizon, a run of `d` consecutive slots whose
  leaders are good.

The coin reads one more, and a bundle:

* **`GoodFloor`**, the counting lemma as the coin reads it: on the records
  a population hypothesis holds of, the good set of a round holds at
  least `floor` validators;
* **`RulePair.Lawful`**: both rules of a pair satisfy the laws, their
  verdicts are witnessed in their views, and their tie-breaks have a
  choice.

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [S : Slots Validator]

/-- **Clause A4 on the DAG**: once a reliable quorum has synchronised from `R₀` and populated the
rounds up to a slot's decision round, a reliably led slot at or past `R₀` is directly committed, by
the rule of its own kind, in every view holding that round. -/
def CommitsUnderSync (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (R₀ N k : ℕ),
    -- T is a reliable set: correct, and a quorum
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- T is synchronised from R₀ and populates every round from R₀ to the horizon N
    SynchronisedOn U T R₀ → (∀ r, R₀ ≤ r → r ≤ N → PopulatedOn U T r) →
    -- the slot lies at or past R₀ and decides at or below N, which the view holds
    R₀ ≤ S.slotRound k → R.decisionRound k ≤ N → V.CoversUpto N →
    -- then a reliably led slot commits its candidate in that view, by the direct rule
    S.leader k ∈ T → ∃ L, IsLeaderBlock U k L ∧ R.Commit U V L (S.slotRound k) (S.kind k)

/-- **A silent leader is skipped**: a slot whose leader has no block at the slot's round is
directly skipped in every view holding its decision round, once a quorum populates every round
above the slot up to that one. The rounds are the whole range because rules read the skip at
different rounds: Mahi-Mahi at its vote round, Odontoceti and Async BlueBottle at the decision
round. -/
def SkipsSilent (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (k : ℕ),
    -- T is a quorum
    quorumCard Validator ≤ T.card →
    -- the leader has no block at the slot's round
    (∀ L ∈ U.ids, (U.block L).round = S.slotRound k → (U.block L).creator ≠ S.leader k) →
    -- T populates every round above the slot up to its decision round, which the view holds
    (∀ r, S.slotRound k < r → r ≤ R.decisionRound k → PopulatedOn U T r) →
    V.CoversUpto (R.decisionRound k) →
    -- then the slot is directly skipped in that view
    R.Skip U V S k

omit S in
/-- **Every nonempty rung has a tie-break choice**: whenever some candidate of a slot is linked
at a rung from an anchor, one of them is the tie-break's choice there. What the indirect commit
needs to fire; a rule with no tie has it outright, and a rule whose tie is the order has the
least linked candidate. -/
def LeastLinked (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ {S : Slots Validator} {U : BlockUniverse Validator BlockId Payload} {A : BlockId} {i k : ℕ},
    i < R.rungs → (∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k) →
    ∃ L, IsLeaderBlock (S := S) U k L ∧ R.Link i U A L S k ∧ R.Least (S := S) U A i k L

/-- **A hop of the floor chain at a rule**: from slot `x`, the anchor search passes over every
slot the view skips and stops at the first slot past `x`'s decision round that it does not, which
is `y`. One slot per round, as Theorem 2 reads the chain; `FloorHop` at a wavelength function of
one round or more is this at `steelheadAnchored`. -/
def FloorHopOf (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
    (x y : ℕ) : Prop :=
  x + R.waveAt (S.kind x) + 1 ≤ y ∧
    (∀ j, x + R.waveAt (S.kind x) + 1 ≤ j → j < y → R.Decided U V j none) ∧
    ¬ R.Decided U V y none

omit S in
/-- **A rule's commits are witnessed in the view they are taken in**: a direct commit puts its
candidate in the view, and a link puts its candidate in the anchor's history. A view is closed
under references, so an anchor the view holds brings the linked candidate with it. -/
structure CommitLaws (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop where
  /-- A direct commit puts its candidate in the view. -/
  commit_mem : ∀ {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {L : BlockId} {r κ : ℕ},
    R.Commit U V L r κ → L ∈ V.ids
  /-- A link puts its candidate in the anchor's history. -/
  link_reaches : ∀ {i : ℕ} {U : BlockUniverse Validator BlockId Payload} {A L : BlockId}
    {S : Slots Validator} {k : ℕ}, R.Link i U A L S k → Reaches U A L

omit S in
/-- **A rule's verdicts are witnessed in the view they are taken in**: its commits are
(`CommitLaws`), and a direct skip rests on a block of the view at or above the slot's round. -/
structure ViewLaws (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop
    extends CommitLaws R where
  /-- A direct skip rests on a block of the view at or above the slot's round. -/
  skip_round : ∀ {S : Slots Validator} {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {k : ℕ},
    R.Skip U V S k → ∃ b ∈ V.ids, S.slotRound k ≤ (U.block b).round

omit [LinearOrder BlockId] S in
/-- **The good set commits**: every validator in `good U r` has a block at round `r` that the rule
directly commits, at every kind, in every view holding the decision round of that kind. -/
def GoodCommits (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (r : ℕ) (v : Validator), v ∈ good U r →
    ∃ L ∈ U.ids, (U.block L).round = r ∧ (U.block L).creator = v ∧
      ∀ (κ : ℕ) (V : View Validator BlockId Payload U), V.CoversUpto (r + R.waveAt κ) →
        R.Commit U V L r κ

omit [LinearOrder BlockId] in
/-- **Clause A5, the run form**, at the schedule in scope: in every window of `c` slots below the
horizon `N`, a run of `d` consecutive slots whose leaders are good at their rounds. The bound
reads the last slot of the latest possible run, so that a small universe is not covered for
free. -/
def RunWithin (R : AnchoredRule Validator BlockId Payload ValidWrt Correct)
    (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (U : BlockUniverse Validator BlockId Payload) (c d N : ℕ) : Prop :=
  ∀ k, R.decisionRound (k + c + d - 1) ≤ N →
    ∃ k', k ≤ k' ∧ k' < k + c ∧ ∀ i, i < d → S.leader (k' + i) ∈ good U (S.slotRound (k' + i))

omit [LinearOrder BlockId] S in
/-- **The counting lemma, as the coin reads it**: on a record and a set of validators the
population hypothesis `Pop` holds of at round `r`, the good set of the round holds at least `floor`
validators. -/
def GoodFloor (good : BlockUniverse Validator BlockId Payload → ℕ → Finset Validator)
    (Pop : BlockUniverse Validator BlockId Payload → Finset Validator → ℕ → Prop) (floor : ℕ) :
    Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (T : Finset Validator) (r : ℕ), Pop U T r →
    floor ≤ (good U r).card

omit S in
/-- **A lawful pair**: both rules satisfy the anchored relation's laws, their verdicts are
witnessed in their views, and their tie-breaks have a choice at every nonempty rung. -/
structure RulePair.Lawful (p : RulePair Validator BlockId Payload) : Prop where
  /-- The synchronous rule's laws. -/
  sync_laws : p.sync.Laws
  /-- The asynchronous rule's laws. -/
  async_laws : p.async.Laws
  /-- The synchronous rule's verdicts are witnessed in their views. -/
  sync_view : ViewLaws p.sync
  /-- The asynchronous rule's verdicts are witnessed in their views. -/
  async_view : ViewLaws p.async
  /-- The synchronous rule's tie-break has a choice. -/
  sync_least : LeastLinked p.sync
  /-- The asynchronous rule's tie-break has a choice. -/
  async_least : LeastLinked p.async

end Steelhead

end LeanDag
