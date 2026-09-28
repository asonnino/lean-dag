import LeanDag.Steelhead.BlueBottlePair.Coin.Statement
import LeanDag.Steelhead.Helpers.Coin
import LeanDag.Steelhead.Helpers.BlueBottlePair.Period
import LeanDag.AsyncBlueBottle.Helpers.Counting
/-!
# Helpers — the `5f + 1` pair's coin

Generated lemma infrastructure for `BlueBottlePair/Coin/Statement.lean`;
not part of the audit surface. ABB7 (`goodCard`) is the counting lemma's
floor, `n − 3f` on a reliable quorum populating the two rounds above a
round; `bbPair` is lawful from Odontoceti's and Async BlueBottle's laws;
every claim is then the generic one of `Helpers/Coin.lean` at that floor
and at `wa = 3`, the agreed output read at `blueBottlePairAnchored`,
which is `steelheadAt bbPair` by definition.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

open Filter Topology
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-! ## ABB7 as the counting lemma's floor -/

/-- **ABB7 as a count**: at least `n − 3f` validators are committed at round `r`. -/
theorem card_goodAt_of_populated {U : BlockUniverse Validator BlockId Payload}
    {T : Finset Validator} {r : ℕ} (h : Coin.Populated U T r) :
    Fintype.card Validator - 3 * F.f ≤ (AsyncBlueBottle.goodAt U r).card := by
  have hg := AsyncBlueBottle.goodCard h.1 h.2.1 h.2.2.1 h.2.2.2
  have := Finset.card_le_card (Finset.inter_subset_left (s₁ := AsyncBlueBottle.goodAt U r)
    (s₂ := (Correct : Finset Validator)))
  omega

/-- **ABB7 is the floor `n − 3f`.** -/
theorem goodFloor_asyncBlueBottle :
    GoodFloor (fun (U : BlockUniverse Validator BlockId Payload) r => AsyncBlueBottle.goodAt U r)
      Coin.Populated (Fintype.card Validator - 3 * F.f) :=
  fun _ _ _ h => card_goodAt_of_populated h

variable (Validator) in
/-- The committee exceeds `3f`, so ABB7's floor is positive. -/
theorem floor_pos : 0 < Fintype.card Validator - 3 * F.f := by
  have := F.card_validators5
  omega

/-- **The `5f + 1` pair is lawful.** -/
theorem bbPair_lawful : (bbPair Validator BlockId Payload).Lawful :=
  ⟨Odontoceti.odontocetiLaws, AsyncBlueBottle.asyncBlueBottleLaws, viewLaws_odontoceti,
    viewLaws_asyncBlueBottle, leastLinked_odontoceti, leastLinked_asyncBlueBottle⟩

/-! ## SH-BB11 and SH-BB11a -/

/-- **SH-BB11.** -/
theorem coinHypotheses : Coin.CoinHypotheses Validator BlockId Payload :=
  ⟨bbPair_lawful, goodCommits_asyncBlueBottle, goodFloor_asyncBlueBottle, floor_pos Validator,
    Nat.sub_le _ _, by change 1 ≤ 2; omega, rfl⟩

/-- **SH-BB11a.** SH11a at ABB7's floor. -/
theorem floor_le_commitProb {U : BlockUniverse Validator BlockId Payload} {T : Finset Validator}
    {r : ℕ} (h : Coin.Populated U T r) :
    ((Fintype.card Validator - 3 * F.f : ℕ) : ℝ≥0∞) / Fintype.card Validator ≤
      commitProb (AsyncBlueBottle.goodAt U) r :=
  Steelhead.floor_le_commitProb goodFloor_asyncBlueBottle h

/-! ## SH-BB11j, the search at period one -/

/-- **SH-BB11j, first half.** SH11j at ABB7's floor and `wa = 3`. -/
theorem expected_firstGoodBlock_le {U : BlockUniverse Validator BlockId Payload}
    {T : Finset Validator} {b M : ℕ}
    (hpop : ∀ (j : Fin M) (i : Fin 3), Coin.Populated U T (b + j * 3 + i)) :
    (∑ g : Fin M → Fin 3 → Validator, PMF.uniformOfFintype (Fin M → Fin 3 → Validator) g *
        ((firstGoodBlock (AsyncBlueBottle.goodAt U) 3 b g + 1 : ℕ) : ℝ≥0∞)) ≤
      ((Fintype.card Validator : ℝ≥0∞) /
        ((Fintype.card Validator - 3 * F.f : ℕ) : ℝ≥0∞)) ^ 3 :=
  Steelhead.expected_firstGoodBlock_le goodFloor_asyncBlueBottle (Nat.sub_le _ _) hpop

/-- **SH-BB11j, second half.** SH11j's second half at `bbPair`. -/
theorem decided_of_firstGoodBlock {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {d : Validator} {s b M : ℕ} (hs : s < b)
    {g : Fin M → Fin 3 → Validator} (hM : firstGoodBlock (AsyncBlueBottle.goodAt U) 3 b g < M)
    (hV : V.CoversUpto (b + (firstGoodBlock (AsyncBlueBottle.goodAt U) 3 b g + 1) * 3 - 1 + 2)) :
    ∃ v, (blueBottlePairAnchored Validator BlockId Payload).Decided
      (S := chainSlots (coinOfBlocksFrom b g d)) U V s v :=
  Steelhead.decided_of_firstGoodBlock (p := bbPair Validator BlockId Payload)
    leastLinked_odontoceti leastLinked_asyncBlueBottle goodCommits_asyncBlueBottle rfl (d := d) hs
    hM hV

/-! ## SH-BB15a and SH-BB15e, the tail -/

/-- **SH-BB15a.** SH15a at `bbPair`, ABB7's floor. -/
theorem undecidedProb_le {U : BlockUniverse Validator BlockId Payload} {I q K : ℕ} [NeZero K]
    (hKI : K ≤ I) (hwaI : 3 ≤ I) (hq : 3 * K ≤ q * I) {T : Finset Validator}
    {upd : UpdateRule BlockId} {k₀ : ℕ} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K)
    {known : ℕ → Validator} {d : Validator} {s M : ℕ} (h₁ : 1 ≤ s)
    (hpop : ∀ (j : Fin M) (i : Fin (3 * K)),
      Coin.Populated U T (blockRound I q (intervalOf I s) j i)) :
    undecidedProb U (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload)
        (blueBottlePairAnchored Validator BlockId Payload) 3 I q K upd k₀ known d s M ≤
      2 * Steelhead.Coin.badBlockBoundAt Validator (Fintype.card Validator - 3 * F.f)
        (3 * K) ^ (M / 2) :=
  Steelhead.undecidedProb_le (p := bbPair Validator BlockId Payload) bbPair_lawful
    goodCommits_asyncBlueBottle goodFloor_asyncBlueBottle (by change 1 ≤ 2; omega) rfl hKI hwaI
    hq (upd := upd) (known := known) (d := d) h₀ hK hupd h₁ hpop

/-- **SH-BB15e.** SH15e at `bbPair`, ABB7's floor. -/
theorem decidedAlmostSurely [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    {I q K : ℕ} [NeZero K] (hKI : K ≤ I) (hwaI : 3 ≤ I) (hq : 3 * K ≤ q * I)
    {U : ℕ → BlockUniverse Validator BlockId Payload} {T : Finset Validator}
    {upd : ℕ → UpdateRule BlockId} {k₀ : ℕ} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K)
    {known : ℕ → Validator} {s : ℕ} (h₁ : 1 ≤ s)
    (hpop : ∀ (m : ℕ) (j : Fin m) (i : Fin (3 * K)),
      Coin.Populated (U m) T (blockRound I q (intervalOf I s) j i)) :
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (U m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q 3 K (intervalOf I s) m) →
        Matches I K (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload)
          (blueBottlePairAnchored Validator BlockId Payload) coin known (upd m) k₀ (U m) V per →
        Settles I K (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload)
          (blueBottlePairAnchored Validator BlockId Payload) coin known (upd m) k₀ (U m) V per s :=
  Steelhead.decidedAlmostSurely (p := bbPair Validator BlockId Payload) bbPair_lawful
    goodCommits_asyncBlueBottle goodFloor_asyncBlueBottle (floor_pos Validator)
    (by change 1 ≤ 2; omega) rfl hKI hwaI hq (upd := upd) (known := known) h₀ hK hupd h₁ hpop

end BlueBottlePair

end Steelhead

end LeanDag
