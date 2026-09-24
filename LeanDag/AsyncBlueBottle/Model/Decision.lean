import LeanDag.AsyncBlueBottle.Model.Rules
import LeanDag.Common.Anchored.Bounded
/-!
# Async BlueBottle — the decision relation

The slot-indexed layer: the view-relative direct rules, the anchored
rule at Async BlueBottle's data, and `Decided`. Definitions only. As in
the Odontoceti arc, the indirect commit carries a canonicity clause:
two equivocating candidates can both pass `WeakLink` at one anchor at
`n = 5f+1`, and the implementation's digest tie-break is what
arbitrates (`async-bluebottle.md` §4).
-/

namespace LeanDag

namespace AsyncBlueBottle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## View-relative direct rules

A validator applies the direct rules to what it holds. Stated on a
`View` by intersecting with `V.ids`, so that a view can only
under-report the universe-level rule. -/

/-- Direct commit, as judged from a single view: the view holds
decision-round votes for `L` from a quorum of distinct validators. -/
abbrev DirectCommitIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  HoldsAtLeast U V (quorumCard Validator) (voters U L r)

/-- Direct skip, as judged from a single view: the view holds
decision-round blocks blaming the slot `(a, r)` from a quorum of
distinct validators. -/
abbrev DirectSkipIn (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (a : Validator) (r : ℕ) : Prop :=
  HoldsAtLeast U V (quorumCard Validator) (blamerBlocks U a r)

/-! ## The relation -/

/-- **Async BlueBottle as an anchored rule**: `waveAt = 2` — the decision
round `r + 2`, the protocol's three-round wave less one, as Mahi-Mahi's
`w − 1` — the cone-vote quorum direct commit, the slot-level direct skip,
and one rung of link, `WeakLink`, with the **least** linked candidate
committed. -/
def asyncBlueBottleAnchored (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults5 Validator] [LinearOrder BlockId] :
    AnchoredRule Validator BlockId Payload ValidWrt Correct where
  waveAt := fun _ => 2
  Commit := fun U V L r _ => DirectCommitIn U V L r
  decCommit := fun _ _ _ _ _ => inferInstance
  Skip := fun U V S k => DirectSkipIn U V (S.leader k) (S.slotRound k)
  rungs := 1
  Link := fun _ U A L S k => WeakLink U A L (S.slotRound k)
  tie := fun _ L L' => L < L'

section Slots

variable [S : Slots Validator]

/-- **The decision relation**: the anchored relation at Async
BlueBottle's data. `Decided U V k (some L)`: a validator holding `V` may
commit `L` at `k`; `Decided U V k none`: it may skip the slot;
*undecided* is the absence of any derivation. -/
abbrev Decided (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop :=
  (asyncBlueBottleAnchored Validator BlockId Payload).Decided (S := S) U V

namespace Decided
export AnchoredRule.Decided (directCommit directSkip indirectCommit indirectSkip)
end Decided

/-- **The bounded relation**, at Async BlueBottle's data. -/
abbrev DecidedWithin (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (B : ℕ) : ℕ → Option BlockId → Prop :=
  (asyncBlueBottleAnchored Validator BlockId Payload).DecidedWithin (S := S) U V B

namespace DecidedWithin
export AnchoredRule.DecidedWithin (directCommit directSkip indirectCommit indirectSkip)
end DecidedWithin

instance {V : View Validator BlockId Payload U} (L : BlockId) (r κ : ℕ) :
    Decidable ((asyncBlueBottleAnchored Validator BlockId Payload).Commit U V L r κ) :=
  inferInstanceAs (Decidable (DirectCommitIn U V L r))

instance {V : View Validator BlockId Payload U} (k : ℕ) :
    Decidable ((asyncBlueBottleAnchored Validator BlockId Payload).Skip U V S k) :=
  inferInstanceAs (Decidable (DirectSkipIn U V (S.leader k) (S.slotRound k)))

instance (i : ℕ) (A L : BlockId) (S : Slots Validator) (k : ℕ) :
    Decidable ((asyncBlueBottleAnchored Validator BlockId Payload).Link i U A L S k) :=
  inferInstanceAs (Decidable (WeakLink U A L (S.slotRound k)))

end Slots

end AsyncBlueBottle

end LeanDag
