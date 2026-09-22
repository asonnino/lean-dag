import LeanDag.Steelhead.Model.Pair
import LeanDag.Steelhead.Properties
/-!
# The `3f + 1` pair — statement

The interface (SH16a, SH16b) instantiated at Mysticeti and Mahi-Mahi,
the pair Steelhead ships (`steelhead.md` §3). Two claims:

* **SH16c, Steelhead is a composite** — `steelheadAnchored w` is the
  composite of `mahiMahiPair w`, Mahi-Mahi's rule read at `w κ`, by
  definition, so SH2 is an instance of SH16b;
* **SH19, the periodic class** — the paper's dial `w(r) = wa` at every
  `k`-th round and `ws` elsewhere, read as `wavelength ws wa` at the
  kinds `periodicKind k` assigns (SH4), for any two waves of two rounds
  or more, is a wavelength function the results above take: every
  kind's wave is at least two and at most the larger wave, so an
  identity-round schedule spans at that wave; agreement, the extension
  laws persistence rests on, and the support's locality, coverage and
  commit laws hold at it, the same way they hold at any wavelength
  function of two rounds or more, coverage asking three; and at
  `ws ≠ wa` the two kinds read two waves, which a period of two or more
  both assigns, so what `waveAt` being a function of the kind admits is
  a wave that varies, not a constant in disguise.

The sibling `BlueBottlePair/` states the same instantiation at
BlueBottle's pair, where the two rules are not one family read at two
numbers.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **SH16c, Steelhead is a composite.** -/
def SteelheadComposes (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [LinearOrder BlockId] : Prop :=
  ∀ w : ℕ → ℕ,
    steelheadAnchored Validator BlockId Payload w =
      compose (mahiMahiPair Validator BlockId Payload w)

/-- **SH19, the periodic class.** -/
def PeriodicClass (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] : Prop :=
  ∀ ws wa k : ℕ, 2 ≤ ws → 2 ≤ wa →
    -- every kind's wave is at least two and at most the larger wave ...
    (∀ κ, 2 ≤ wavelength ws wa κ) ∧ (∀ κ, wavelength ws wa κ ≤ max ws wa) ∧
    -- ... so an identity-round schedule spans at that wave
    (∀ [S : Slots Validator], (∀ s, S.slotRound s = s) →
      (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).SpansEligible (S := S)
        (max ws wa)) ∧
    -- the wave varies: at two distinct waves the two kinds read two wave offsets ...
    (ws ≠ wa →
      (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).waveAt 0 ≠
        (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).waveAt 1) ∧
    -- ... and a period of two or more assigns both kinds, so no constant wave reads as the
    -- paper's dial does
    (2 ≤ k → ∃ r r', periodicKind k r ≠ periodicKind k r') ∧
    -- and the laws hold at it: agreement, the extension laws persistence rests on, the support's
    -- locality and commits, and its coverage law at waves of three or more
    Properties.Agree (SteelheadProperties.steelheadRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload) (wavelength ws wa)) ∧
    (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).ExtendLaws ∧
    Properties.Support.Local (R := SteelheadProperties.steelheadRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload) (wavelength ws wa))
      (SteelheadProperties.shSupport (wavelength ws wa)) ∧
    Properties.Support.Commits (R := SteelheadProperties.steelheadRule (Validator := Validator)
      (BlockId := BlockId) (Payload := Payload) (wavelength ws wa))
      (SteelheadProperties.shSupport (wavelength ws wa)) (coreReliability Validator) ∧
    (3 ≤ ws → 3 ≤ wa →
      Timed.OfCoverage (R := SteelheadProperties.steelheadRule (Validator := Validator)
        (BlockId := BlockId) (Payload := Payload) (wavelength ws wa))
        (SteelheadProperties.shSupport (wavelength ws wa)) (coreReliability Validator))

/-- The `3f + 1` pair, over every fault configuration the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId],
    SteelheadComposes Validator BlockId Payload ∧ PeriodicClass Validator BlockId Payload

end MahiMahiPair

end Steelhead

end LeanDag
