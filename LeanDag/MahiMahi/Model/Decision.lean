import LeanDag.MahiMahi.Model.Rules

/-!
# Mahi-Mahi — the decision relation at wave `w`

The slot-indexed layer: eligibility, the view-relative direct rules, the
indirect test, and `Decided`. Everything is the core's
(`Mysticeti.lean`, Stages B and C) with the wave length substituted —
which is what the core's `decisionRound` docstring anticipated — and one
deliberate departure recorded at `Decided.directSkip`.

**Definitions only**, as in `Rules.lean`. `CertifiedIn` and `Decided`
have no `Decidable` instance, as in the core: the witnesses build
`Decided` by its constructors, discharging each decidable premise by
`decide` and exhibiting a certificate for the indirect test.

**No canonicity clause.** The Odontoceti arc's indirect rule commits the
`≤`-least passing candidate because two twins can both pass its test.
Here the indirect test is "a certificate in the anchor's cone", and two
certificates at one slot name the same candidate (`mahi-mahi.md` §3,
MM1b), exactly as in the core; `[LinearOrder BlockId]` is consumed by
`Votes` alone.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## View-relative direct rules

A validator applies the direct rules to what it holds. Stated on a
`View` by intersecting with `V.ids`, so that a view can only
under-report the universe-level rule. -/

/-- The certificates for `L` that a view holds. -/
def certificatesIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (w : ℕ) (L : BlockId) (r : ℕ) : Finset BlockId :=
  certificates U w L r ∩ V.ids

/-- Direct commit, as judged from a single view. -/
def DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (w : ℕ) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (creatorsOf U.block (certificatesIn U V w L r)).card

/-- The blamers of the slot `(a, r)` whose voting block a view holds. -/
def blamersIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (w : ℕ) (a : Validator) (r : ℕ) : Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (votingRound w r)).filter (fun q => Blames U q a r)) ∩ V.ids)

/-- Direct skip, as judged from a single view. -/
def DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (w : ℕ) (a : Validator) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blamersIn U V w a r).card

instance (V : View Validator BlockId Payload U) (w : ℕ) (L : BlockId) (r : ℕ) :
    Decidable (DirectCommitIn U V w L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance (V : View Validator BlockId Payload U) (w : ℕ) (a : Validator) (r : ℕ) :
    Decidable (DirectSkipIn U V w a r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-- **The indirect test**: a certificate for `L` lies in the causal
history of the anchor `A`. The core's `CertifiedIn` at wave `w`. Not
decidable as stated — `Reaches` is a `Prop` — and not made so: the
witnesses exhibit the certificate. -/
def CertifiedIn (U : BlockUniverse Validator BlockId Payload)
    (w : ℕ) (A L : BlockId) (r : ℕ) : Prop :=
  ∃ C ∈ certificates U w L r, Reaches U A C

/-! ## Slots, eligibility, and the decision relation -/

section Slots

variable [S : Slots Validator]

variable (Validator) in
/-- The round at which slot `k`'s direct rules are settled: its
certificates live at `slotRound k + w − 1`. `Validator` is explicit for
the reason the core gives — the result is a bare `ℕ`. -/
def decisionRound (w k : ℕ) : ℕ := S.slotRound k + w - 1

variable (Validator) in
/-- **`j` may anchor `k`**: `j`'s proposal lies past `k`'s decision
round. A predicate on the pair of slots and the wave length alone, which
is what makes agreement go through: two validators deciding one slot
agree on which slots may anchor it. -/
def Eligible (w k j : ℕ) : Prop := decisionRound Validator w k < S.slotRound j

instance (w k j : ℕ) : Decidable (Eligible Validator w k j) :=
  inferInstanceAs (Decidable (decisionRound Validator w k < S.slotRound j))

/-- **The decision relation at wave `w`** — the verdicts a validator
holding view `V` may reach on slot `k`. `Decided w U V k (some L)`: the
validator may commit `L` at `k`; `Decided w U V k none`: it may skip
the slot; *undecided* is the absence of any derivation.

The relation is order-free between constructors: the implementation
tries the direct rule before the indirect one, but any justifiable
verdict is derivable here, and the safety results prove the routes
never disagree. The anchor premises follow `try_indirect_decide`: the
anchor is the **nearest eligible committed** slot — `Decided … j (some
A)` with every eligible slot strictly between decided `none` (a skipped
slot cannot anchor; a committed one would be the nearer anchor).
"Stop at the first undecided slot" needs no encoding: an undecided slot
in between leaves no derivation.

The one departure from the core: `directSkip` takes the slot's blame
directly, `DirectSkipIn U V w (S.leader k) (S.slotRound k)`, where the
core quantifies `∀ L, IsLeaderBlock U k L → DirectSkipIn U V L …`. The
skip rule is on the slot in the paper and in the implementation, and at
`w = 3` the two readings agree, which the conservativity result MM1d
states (`mahi-mahi.md` §3). -/
inductive Decided (w : ℕ) (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate: a quorum of certificates in
  view. -/
  | directCommit {k : ℕ} {L : BlockId} :
      -- L is a candidate for slot k: its round and author are the slot's
      IsLeaderBlock U k L →
      -- a quorum of distinct validators certify L at the decision round,
      -- among the blocks the view holds
      DirectCommitIn U V w L (S.slotRound k) →
      Decided w U V k (some L)
  /-- The direct rule skips the slot: a quorum of blames in view (covers
  the case of no candidate at all — blames target the slot). -/
  | directSkip {k : ℕ} :
      -- a quorum of distinct validators hold a voting-round block whose
      -- cone contains no block of the slot's leader at the slot's round
      DirectSkipIn U V w (S.leader k) (S.slotRound k) →
      Decided w U V k none
  /-- Anchored on the nearest eligible committed slot, a certificate for
  `L` is in the anchor's reach. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      -- the anchor slot lies ahead of k
      k < j →
      -- ... proposed past k's decision round, slotRound k + w − 1
      Eligible Validator w k j →
      -- slot j committed A, by any route
      Decided w U V j (some A) →
      -- j is the NEAREST such slot: every eligible slot in between skipped
      -- (an undecided one in between leaves this underivable — the
      -- implementation's "stop at the first undecided slot")
      (∀ i, k < i → i < j → Eligible Validator w k i → Decided w U V i none) →
      -- L is a candidate for slot k
      IsLeaderBlock U k L →
      -- a certificate for L lies in the anchor's cone
      CertifiedIn U w A L (S.slotRound k) →
      Decided w U V k (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate has a
  certificate in the anchor's reach. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      -- the anchor slot lies ahead of k
      k < j →
      -- ... proposed past k's decision round
      Eligible Validator w k j →
      -- slot j committed A, by any route
      Decided w U V j (some A) →
      -- j is the nearest such slot (as in indirectCommit)
      (∀ i, k < i → i < j → Eligible Validator w k i → Decided w U V i none) →
      -- no candidate of slot k has a certificate in the anchor's cone:
      -- only then skip
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U w A L (S.slotRound k)) →
      Decided w U V k none

end Slots

end MahiMahi

end LeanDag
