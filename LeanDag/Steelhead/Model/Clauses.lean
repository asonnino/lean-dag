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

Theorem 3 reads two more, which the chain needs:

* **`GoodCommits`**: the good set of a round, the validators whose
  round-`r` block the asynchronous rule directly commits, commits in every
  view holding the round's decision round. The counting lemma of each
  rule bounds that set from below;
* **`RunWithin`**, the paper's clause A5 in its run form: in every window
  of `c` slots below a horizon, a run of `d` consecutive slots whose
  leaders are good.

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

end Steelhead

end LeanDag
