import LeanDag.MahiMahi.Model.Decision

/-!
# Safety at wave `w` — statement

The rules at wave `w` never disagree about a slot. Four claims
(`mahi-mahi.md` §3), each stated on the universe where the counting
happens and on views where the protocol runs:

* **MM1a, skip excludes certificates** — a directly skipped slot has no
  certificate for any of its candidates, anywhere;
* **MM1b, certificate uniqueness** — two certified candidates of one
  author and round are the same block;
* **MM1c, agreement** — two views deciding one slot reach the same
  verdict, by any routes;
* **MM1d, conservativity** — at `w = 3` every derivation of the
  relation is a derivation of the core's, and the direct predicates
  coincide with the core's. A statement about definitions: that the
  three-round instance of this arc *is* Mysticeti's rule, not that
  anything commits at three rounds — which, without synchrony, it does
  not (`mahi-mahi.md` §4.2).

All claims assume `3 ≤ w`: below three rounds the voting round is not
above the proposal round and the rule is not the one this arc models.

On MM1d, one direction only. The core's `directSkip` quantifies over
the candidates — a quorum of blames *per twin* — where this arc's, like
the implementation's `enough_leader_blame`, blames the *slot*: a quorum
of voting blocks that support no twin at all. The arc's premise is the
stronger one, so its derivations are the core's; the converse fails when
a leader equivocates and the blaming quorums of its twins differ. The
two coincide for any slot with at most one candidate, which the direct
skip claim below states.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace MahiMahi

namespace Safety

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
  [S : Slots Validator]

/-- **MM1a, skip excludes certificates**: a directly skipped slot `(a, r)`
has no certificate for any block of that author and round. The quorum of
blamers and the quorum of voters behind a certificate would share a
correct validator, whose unique voting block cannot both hold a
candidate in its cone and hold none. -/
def SkipExcludesCertificates (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (a : Validator) (r : ℕ) (L : BlockId),
    3 ≤ w → DirectSkip U w a r →
    L ∈ U.ids → (U.block L).creator = a → (U.block L).round = r →
    certificates U w L r = ∅

/-- **MM1b, certificate uniqueness**: two certified blocks of one author
and round are equal — universe-level, no views. Two voter quorums share
a correct validator, whose unique voting block votes for the least
candidate of that author and round, and only for it. -/
def CertificateUniqueness (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (r : ℕ) (L₁ L₂ : BlockId),
    3 ≤ w →
    (certificates U w L₁ r).Nonempty → (certificates U w L₂ r).Nonempty →
    (U.block L₁).creator = (U.block L₂).creator →
    (U.block L₁).round = (U.block L₂).round →
    L₁ = L₂

/-- **MM1c, agreement**: two views deciding one slot agree on the verdict,
whatever routes each took — the core's M6 at wave `w`. -/
def Agreement (U : BlockUniverse Validator BlockId Payload) (w : ℕ) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k : ℕ) (v₁ v₂ : Option BlockId),
    3 ≤ w → Decided w U V₁ k v₁ → Decided w U V₂ k v₂ → v₁ = v₂

/-- **MM1d, conservativity of the relation**: at `w = 3` a derivation of
this arc's `Decided` is a derivation of the core's. A statement about
the two definitions, not about any verdict occurring: it says the
three-round instance of the wave-`w` relation *is* Mysticeti's, as
`uniformSingle_spacing` says for the schedule generalisation. Whether
anything commits is a liveness question, and at `w = 3` the answer
needs the core's synchrony hypothesis (`mahi-mahi.md` §4.2). -/
def DecidedConservative (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (k : ℕ) (v : Option BlockId),
    Decided 3 U V k v → LeanDag.Decided U V k v

/-- **MM1d, conservativity of direct commit**: at `w = 3` the two direct
commit predicates coincide on every candidate at its own round — a
round-`(r+1)` block's candidates at `(a, r)` are its references by `a`.
An equivalence of predicates on a given DAG, true whether or not either
side holds; it does not assert that a direct commit occurs. -/
def DirectCommitConservative (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (L : BlockId) (r : ℕ),
    L ∈ U.ids → (U.block L).round = r →
    (DirectCommit U 3 L r ↔ LeanDag.DirectCommit U L r)

/-- **MM1d, conservativity of direct skip**: at `w = 3` this arc's skip
implies the core's for every candidate of the slot, and the two coincide
on a slot with at most one candidate. -/
def DirectSkipConservative (U : BlockUniverse Validator BlockId Payload) : Prop :=
  (∀ (a : Validator) (r : ℕ),
    DirectSkip U 3 a r →
    ∀ L ∈ U.ids, (U.block L).creator = a → (U.block L).round = r →
      LeanDag.DirectSkip U L r) ∧
  (∀ (a : Validator) (r : ℕ) (L : BlockId),
    L ∈ U.ids → (U.block L).creator = a → (U.block L).round = r →
    (∀ L' ∈ U.ids, (U.block L').creator = a → (U.block L').round = r → L' = L) →
    (DirectSkip U 3 a r ↔ LeanDag.DirectSkip U L r))

/-- Safety of the rule at wave `w`, over every fault configuration,
schedule, block universe and wave length the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload) (w : ℕ),
    SkipExcludesCertificates U w ∧ CertificateUniqueness U w ∧ Agreement U w ∧
      DecidedConservative U ∧ DirectCommitConservative U ∧ DirectSkipConservative U

end Safety

end MahiMahi

end LeanDag
