import LeanDag.Odontoceti.Rules
import LeanDag.MahiMahi.Model.Rules
/-!
# Async BlueBottle — the rule layer

**A commit rule** (`Protocols`), asynchronous, at `n ≥ 5f+1`, on the
core's universes and validity. The rule is `asyncBlueBottleAnchored`
(`Model/Decision.lean`); the carrier and properties are
`Properties.lean`; the record witness is `Record.lean`.

BB-Core's two-round rule stretched to a three-round wave with merged
certificates (`async-bluebottle.md` §1): a candidate proposed at round
`r` is decided at round `r + 2`, and a round-`(r + 2)` block votes for
it through its **causal cone** — Mahi-Mahi's `Votes` — rather than by a
direct reference. The thresholds are Odontoceti's, `n − f` for the direct
rules and `n − 3f` for the indirect test, and the anchor floor is
`r + 3`. Definitions only — results live in `<Result>/Statement.lean`
and `Proof.lean`.
-/

namespace LeanDag

namespace AsyncBlueBottle

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-! ## The rounds of a wave -/

/-- The round at which a candidate proposed at `r` is voted on and
decided — the same round, there being no certificate stage
(`merged_certificates`). Named with the suffix because `decisionRound`,
on slots, is the name the core's schedule layer uses. -/
def decisionRoundAt (r : ℕ) : ℕ := r + 2

/-! ## Voters and blamers at the decision round -/

/-- The decision-round blocks whose cone-vote is `L`: the blocks at
`r + 2` for which `L` is the canonical block of its author and round in
the block's causal history (`MahiMahi.Votes`). The vote reads `L`'s own
round, so `r` is not pinned to it here; every consumer goes through
`IsLeaderBlock`, which pins it (`async-bluebottle.md` §9). -/
def voters (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (decisionRoundAt r)).filter (fun q => MahiMahi.Votes U q L)

/-- The validators whose decision-round block votes for `L`. -/
def supporters (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block (voters U L r)

/-- The decision-round blocks that blame the slot `(a, r)`: no block of
that author and round lies in their cone (`MahiMahi.Blames`), the
implementation's `find_support = None`. -/
def blamerBlocks (U : BlockUniverse Validator BlockId Payload) (a : Validator) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (decisionRoundAt r)).filter (fun q => MahiMahi.Blames U q a r)

/-- The validators whose decision-round block blames the slot `(a, r)`. -/
def blamers (U : BlockUniverse Validator BlockId Payload) (a : Validator) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block (blamerBlocks U a r)

/-! ## The direct rules -/

/-- **Direct commit** (the paper's strong certificate): a quorum of
distinct validators vote for `L` at the decision round. -/
def DirectCommit (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (supporters U L r).card

/-- **Direct skip**: a quorum of distinct validators blame the slot
`(a, r)` at the decision round. On the slot rather than on a block, as
`enough_leader_blame` has it: a blame is the absence of any supported
block, not a vote against a particular twin. -/
def DirectSkip (U : BlockUniverse Validator BlockId Payload) (a : Validator) (r : ℕ) : Prop :=
  quorumCard Validator ≤ (blamers U a r).card

instance {U : BlockUniverse Validator BlockId Payload} (L : BlockId) (r : ℕ) :
    Decidable (DirectCommit U L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

instance {U : BlockUniverse Validator BlockId Payload} (a : Validator) (r : ℕ) :
    Decidable (DirectSkip U a r) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ## The indirect test -/

/-- The validators whose decision-round vote for `L` lies in the anchor
`A`'s cone — by distinct authors, the count equivocation cannot
inflate. -/
def coneSupporters (U : BlockUniverse Validator BlockId Payload) (A L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((voters U L r).filter (fun q => q ∈ history U A))

/-- **The indirect test** (the paper's weak certificate in the anchor's
history): at least `n − 3f` distinct authors of decision-round votes for
`L` in the anchor's cone. At `n = 5f+1` this is the paper's `2f+1`. -/
def WeakLink (U : BlockUniverse Validator BlockId Payload) (A L : BlockId) (r : ℕ) : Prop :=
  Fintype.card Validator - 3 * F.f ≤ (coneSupporters U A L r).card

instance {U : BlockUniverse Validator BlockId Payload} (A L : BlockId) (r : ℕ) :
    Decidable (WeakLink U A L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

end AsyncBlueBottle

end LeanDag
