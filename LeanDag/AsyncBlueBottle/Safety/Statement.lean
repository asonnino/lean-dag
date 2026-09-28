import LeanDag.AsyncBlueBottle.Model.Decision
import LeanDag.MahiMahi.Model.Rules
/-!
# Safety — statement

The rules never disagree about a slot (`async-bluebottle.md` §4):
ABB1 (commit excludes skip), ABB1′ (two commits name one block), ABB2
(a skipped slot's candidate passes the weak test nowhere), ABB3
(propagation: a commit passes it from every block three rounds up),
ABB4′ (a commit is the only candidate that passes it) and ABB5
(agreement across views), with ABB1″ pinning the blame as Mahi-Mahi's at
the merged decision round. ABB1 and ABB1′ hold already at `n ≥ 3f+1`;
ABB2 and ABB4′ are where `n ≥ 5f+1` is required. There is no
conservativity conjunct onto a rule of the tree, since none decides at
`r + 2` by a single count: Odontoceti decides at `r + 1`, and Mahi-Mahi
at `w = 3` is the core's certificate rule.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace AsyncBlueBottle

namespace Safety

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **ABB1, commit excludes skip**: a directly committed candidate's slot
is not directly skipped, since a quorum of voters and a quorum of
blamers at the decision round would share a correct validator whose one
block cannot both vote for the candidate and hold none. -/
def CommitExcludesSkip (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L : BlockId) (r : ℕ),
    (U.block L).round = r → DirectCommit U L r →
    ¬ DirectSkip U (U.block L).creator r

/-- **ABB1′, commit uniqueness**: two directly committed blocks of one
author and round are equal — universe-level, no views. Two voter
quorums share a correct validator, whose one decision-round block votes
for the least candidate of that author and round, and only for it. -/
def CommitUnique (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (r : ℕ) (L₁ L₂ : BlockId),
    DirectCommit U L₁ r → DirectCommit U L₂ r →
    (U.block L₁).creator = (U.block L₂).creator →
    (U.block L₁).round = (U.block L₂).round →
    L₁ = L₂

/-- **ABB2, skip excludes link**: a directly skipped slot's candidate
passes the weak test against no anchor: its supporters number at most
`2f`, below `n − 3f`. -/
def SkipExcludesLink (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (a : Validator) (r : ℕ) (L A : BlockId),
    DirectSkip U a r → (U.block L).creator = a → (U.block L).round = r →
    ¬ WeakLink U A L r

/-- **ABB3, propagation**: a directly committed candidate passes the weak
test from every block three or more rounds above its proposal — the
anchor floor — so every anchor's cone holds its weak certificate, and no
anchor can skip it indirectly (the paper's Lemma 21). -/
def Propagation (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L : BlockId) (r : ℕ) (A : BlockId),
    DirectCommit U L r → A ∈ U.ids → r + 3 ≤ (U.block A).round →
    WeakLink U A L r

/-- **ABB4′, a commit excludes every rival**: a directly committed block
is the only block of its author and round that passes the weak test at
any anchor, since `n − f` voters and `n − 3f` in-cone voters would
share a correct validator voting for two twins. -/
def CommitExcludesRival (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (r : ℕ) (L₁ L₂ A : BlockId),
    DirectCommit U L₁ r → WeakLink U A L₂ r →
    (U.block L₁).creator = (U.block L₂).creator →
    (U.block L₁).round = (U.block L₂).round →
    L₁ = L₂

/-- **ABB1″, the blame is Mahi-Mahi's**: a slot is directly skipped here
exactly when Mahi-Mahi's rule at wave `4`, whose voting round is also
`r + 2`, skips it — the half of the arc that is a transcription of
Mahi-Mahi, on the record. -/
def SkipIsMahiMahi (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (a : Validator) (r : ℕ), DirectSkip U a r ↔ MahiMahi.DirectSkip U 4 a r

/-- **ABB5, agreement**: two views deciding one slot agree on the
verdict, whatever routes each took — the paper's Lemmas 22 and 23, with
the canonical candidate the indirect rule commits doing the work
Observation 4 assumes away. -/
def Agreement (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (v₁ v₂ : Option BlockId),
    Decided U V₁ k v₁ → Decided U V₂ k v₂ → v₁ = v₂

/-- Safety, over every fault configuration, schedule and block universe
the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload),
    CommitExcludesSkip U ∧ CommitUnique U ∧ SkipExcludesLink U ∧ Propagation U ∧
      CommitExcludesRival U ∧ SkipIsMahiMahi U ∧ Agreement U

end Safety

end AsyncBlueBottle

end LeanDag
