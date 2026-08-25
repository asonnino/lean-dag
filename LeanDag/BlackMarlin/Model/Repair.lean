import LeanDag.BlackMarlin.Model.Descent

/-!
# Black Marlin — the descent, repaired

The execution of `black-marlin.md` §13 turns on the descent taking an
unsupported twin where the rule had committed the supported one. This
file states the condition that excludes it and a descent that meets the
condition (`black-marlin.md` §14). Nothing already in the model is
altered: `descend`, `flushRecord` and everything proved of them stand,
and what is added sits beside them.

**The condition.** A record is *support-preferring* when, at any round
where some anchor carries a quorum of support, what it flushes there is
supported. BM1 makes the supported anchor of a round unique, so two
support-preferring records cannot part at such a round.

**The descent that meets it.** `descendSupp` filters the candidates of
L21–L24 to those the rule could commit, and falls back to L24 only where
none is. By BM1 the filter never leaves more than one candidate, so where
it bites there is nothing left to break ties over. A step never stalls
and never moves to another round; a chain through a different block does
descend through a different cone, so the rounds a whole record flushes at
may differ.

**What this is not.** `Supported` here is a fact about the universe, and
a validator computes support from its own view, which under-reports. So
the condition states a repair rather than supplies one: an implementation
would have to establish that the support it needs is in view, and this
file does not.

**Trusted core of the arc: definitions only.** No theorem lives in this
file.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The candidates of L21–L24 that the rule could commit. -/
def suppCandidates (U : BlockUniverse Validator BlockId Payload) (B : BlockId) :
    Finset BlockId :=
  (maxAnchor U (strongOf U B)).filter (fun A => Supported U A (U.block A).round)

/-- **The repaired choice**: a supported candidate where there is one,
and L21–L24 otherwise. -/
def descendSupp (U : BlockUniverse Validator BlockId Payload) (B : BlockId) :
    Option BlockId :=
  if (suppCandidates U B).Nonempty then pick (suppCandidates U B) else descend U B

/-- The repaired descent, with fuel, as `descentUpto` is. -/
def descentSuppUpto (U : BlockUniverse Validator BlockId Payload) :
    ℕ → BlockId → ℕ → Option BlockId
  | 0, B, ρ => if (U.block B).round = ρ then some B else none
  | (n + 1), B, ρ =>
      if (U.block B).round = ρ then some B
      else (descendSupp U B).bind (fun A => descentSuppUpto U n A ρ)

/-- The record the repaired descent leaves. -/
def flushRecordSupp (U : BlockUniverse Validator BlockId Payload) (B : BlockId) (ρ : ℕ) :
    Option BlockId :=
  descentSuppUpto U ((U.block B).round) B ρ

/-- **The side-condition.** Where a round has a supported anchor, the
record flushes a supported one. -/
def SupportPreferring (U : BlockUniverse Validator BlockId Payload) (f : Flush U) : Prop :=
  ∀ (ρ : ℕ) (L : BlockId), f.block ρ = some L →
    (∃ A, IsAnchor U ρ A ∧ Supported U A ρ) → Supported U L ρ

end BlackMarlin

end LeanDag
