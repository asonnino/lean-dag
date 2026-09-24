import LeanDag.Steelhead.MahiMahiPair.Statement
import LeanDag.Steelhead.Helpers.Compose
/-!
# Helpers — the `3f + 1` pair

Generated lemma infrastructure for `MahiMahiPair/Statement.lean`; not
part of the audit surface. SH-MM16c is definitional. The periodic class
reads its bounds off the two waves, its spanning off the identity rounds,
and its laws off the ones `Properties.lean` proves at any wavelength
function of two rounds or more.
-/

namespace LeanDag

namespace Steelhead

/-- **SH-MM16c.** Field by field, by definition. -/
theorem steelheadAnchored_eq_compose {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [LinearOrder BlockId] (w : ℕ → ℕ) :
    steelheadAnchored Validator BlockId Payload w =
      compose (mahiMahiPair Validator BlockId Payload w) :=
  rfl

/-- **The `3f + 1` pair's rules are the family** at the pair's wavelength: Mahi-Mahi's rule at the
wave of each kind. -/
theorem mmPair_rules {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [LinearOrder BlockId] (ws wa : ℕ) :
    (mmPair Validator BlockId Payload ws wa).rules =
      mahiMahiPair Validator BlockId Payload (wavelength ws wa) := by
  funext κ
  exact (apply_ite (MahiMahi.mahiMahiAnchored Validator BlockId Payload) (κ = 0) ws wa).symm

/-- **Steelhead at the `3f + 1` pair is `steelheadAnchored`** at the pair's wavelength. -/
theorem steelheadAt_mmPair {Validator BlockId Payload : Type} [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] [LinearOrder BlockId] (ws wa : ℕ) :
    steelheadAt (mmPair Validator BlockId Payload ws wa) =
      steelheadAnchored Validator BlockId Payload (wavelength ws wa) :=
  congrArg compose (mmPair_rules ws wa)

/-! ## SH-MM19, the periodic class -/

/-- **A period of two or more assigns both kinds**: round `0` is asynchronous and round `1` is
not. -/
theorem periodicKind_not_const {k : ℕ} (hk : 2 ≤ k) :
    ∃ r r', periodicKind k r ≠ periodicKind k r' := by
  refine ⟨0, 1, ?_⟩
  unfold periodicKind
  rw [Nat.zero_mod, if_pos rfl, Nat.mod_eq_of_lt (by omega : 1 < k), if_neg (by omega)]
  decide

section PeriodicClass

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator] [Faults Validator]
  {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **The pair's wave varies with the kind**: at two distinct waves the two kinds' wave offsets
differ. -/
theorem wavelength_waveAt_ne {ws wa : ℕ} (hws : 2 ≤ ws) (hwa : 2 ≤ wa) (hne : ws ≠ wa) :
    (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).waveAt 0 ≠
      (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).waveAt 1 := by
  simp only [steelheadAnchored_waveAt, wavelength_zero, wavelength_one]
  omega

/-- **SH-MM19.** The bounds are the waves', the spanning is `spansEligible_of_le`, and the laws are
`Properties.lean`'s at the pair's wavelength. -/
theorem periodicClass : MahiMahiPair.PeriodicClass Validator BlockId Payload := by
  intro ws wa k hws hwa
  refine ⟨wavelength_two_le hws hwa, wavelength_le_max ws wa, ?_,
    fun hne => wavelength_waveAt_ne hws hwa hne, fun hk => periodicKind_not_const hk,
    SteelheadProperties.agree (wavelength_two_le hws hwa),
    SteelheadProperties.steelheadExtendLaws (wavelength_two_le hws hwa),
    SteelheadProperties.shSupport_local (wavelength_two_le hws hwa),
    SteelheadProperties.shSupport_commits (wavelength_two_le hws hwa),
    fun hws3 hwa3 => SteelheadProperties.shSupport_ofCoverage (wavelength_three_le hws3 hwa3)⟩
  intro S hid
  refine spansEligible_of_le (S := S) (fun s => ?_) hid
  have := wavelength_le_max ws wa (S.kind s)
  have := wavelength_two_le hws hwa (S.kind s)
  simp only [steelheadAnchored_waveAt]
  omega

end PeriodicClass

end Steelhead

end LeanDag
