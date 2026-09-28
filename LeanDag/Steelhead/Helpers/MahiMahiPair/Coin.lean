import LeanDag.Steelhead.MahiMahiPair.Coin.Statement
import LeanDag.Steelhead.Helpers.Coin
import LeanDag.Steelhead.Helpers.MahiMahiPair.Period
import LeanDag.MahiMahi.Helpers.Counting
import LeanDag.MahiMahi.Properties
/-!
# Helpers — the `3f + 1` pair's coin

Generated lemma infrastructure for `MahiMahiPair/Coin/Statement.lean`;
not part of the audit surface. MM2 (`goodCard`) is the counting lemma's
floor, `n − f − b` at `wa ≥ 5` on a quorum populating rounds `r + 3` and
the decision round, and one at `wa ≥ 4` on rounds `r + 2` and the
decision round; the pair `mmPair ws wa` is lawful at waves of two rounds
or more; every claim is then the generic one of `Helpers/Coin.lean` at
that floor, the agreed output read at `steelheadAnchored (wavelength ws
wa)`, which is `steelheadAt (mmPair ws wa)`.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

open Filter Topology
open scoped ENNReal

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-! ## MM2 as the counting lemma's floor -/

/-- The population MM2 reads at `wa ≥ 5`: a quorum populating round `r + 3` and the decision
round. -/
abbrev mmPop (wa : ℕ) (U : BlockUniverse Validator BlockId Payload) (T : Finset Validator)
    (r : ℕ) : Prop :=
  quorumCard Validator ≤ T.card ∧ PopulatedOn U T (r + 3) ∧
    PopulatedOn U T (MahiMahi.decisionRoundAt wa r)

/-- The population MM2's wave-four form reads: a quorum populating round `r + 2` and the
decision round. -/
abbrev mmPopFour (wa : ℕ) (U : BlockUniverse Validator BlockId Payload) (T : Finset Validator)
    (r : ℕ) : Prop :=
  quorumCard Validator ≤ T.card ∧ PopulatedOn U T (r + 2) ∧
    PopulatedOn U T (MahiMahi.decisionRoundAt wa r)

/-- **MM2 as a count**: at least `n − f − b` validators are committed at round `r`. -/
theorem card_goodAt_of_populated {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 5 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r : ℕ}
    (hpop₃ : PopulatedOn U T (r + 3)) (hpopd : PopulatedOn U T (MahiMahi.decisionRoundAt wa r)) :
    Fintype.card Validator - F.f - F.byzantine.card ≤ (MahiMahi.goodAt U wa r).card := by
  have h := MahiMahi.goodCard hwa hcard hpop₃ hpopd
  have := Finset.card_le_card (Finset.inter_subset_left (s₁ := MahiMahi.goodAt U wa r)
    (s₂ := (Correct : Finset Validator)))
  change Fintype.card Validator - F.f ≤ _ at h
  omega

/-- **MM2 is the floor `n − f − b`** at `wa ≥ 5`. -/
theorem goodFloor_mahiMahi {wa : ℕ} (hwa : 5 ≤ wa) :
    GoodFloor (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
      (MahiMahi.goodAt · wa) (mmPop wa) (Fintype.card Validator - F.f - F.byzantine.card) :=
  fun _ _ _ h => card_goodAt_of_populated hwa h.1 h.2.1 h.2.2

/-- **MM2's wave-four form as a count**: one committed candidate at round `r`. -/
theorem one_le_card_goodAt_of_populated {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 4 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r : ℕ}
    (hpop₂ : PopulatedOn U T (r + 2)) (hpopd : PopulatedOn U T (MahiMahi.decisionRoundAt wa r)) :
    1 ≤ (MahiMahi.goodAt U wa r).card :=
  Finset.card_pos.mpr
    ((MahiMahi.goodNonempty hwa hcard hpop₂ hpopd).mono Finset.inter_subset_left)

/-- **MM2's wave-four form is the floor one** at `wa ≥ 4`. -/
theorem goodFloor_mahiMahi_four {wa : ℕ} (hwa : 4 ≤ wa) :
    GoodFloor (Validator := Validator) (BlockId := BlockId) (Payload := Payload)
      (MahiMahi.goodAt · wa) (mmPopFour wa) 1 :=
  fun _ _ _ h => one_le_card_goodAt_of_populated hwa h.1 h.2.1 h.2.2

variable (Validator) in
/-- The committee exceeds `f + b`, so MM2's floor is positive. -/
theorem floor_pos : 0 < Fintype.card Validator - F.f - F.byzantine.card := by
  have := F.card_validators
  have := F.card_byzantine
  omega

/-- The pair's block bound is the generic one at MM2's floor. -/
theorem badBlockBound_eq (K : ℕ) :
    Coin.badBlockBound Validator K =
      Steelhead.Coin.badBlockBoundAt Validator
        (Fintype.card Validator - F.f - F.byzantine.card) K :=
  rfl

omit [DecidableEq Validator] F in
/-- The pair's wave-four block bound is the generic one at the floor one. -/
theorem badBlockBoundOne_eq (K : ℕ) :
    Coin.badBlockBoundOne Validator K = Steelhead.Coin.badBlockBoundAt Validator 1 K := by
  unfold Coin.badBlockBoundOne Steelhead.Coin.badBlockBoundAt
  rw [one_pow]

/-- `n − (n − f − b) = f + b`. -/
theorem card_sub_floor :
    Fintype.card Validator - (Fintype.card Validator - F.f - F.byzantine.card) =
      F.f + F.byzantine.card := by
  have := F.card_validators
  have := F.card_byzantine
  omega

/-- **The `3f + 1` pair is lawful** at waves of two rounds or more. -/
theorem mmPair_lawful {ws wa : ℕ} (hws : 2 ≤ ws) (hwa : 2 ≤ wa) :
    (mmPair Validator BlockId Payload ws wa).Lawful :=
  ⟨MahiMahi.mahiMahiLaws hws, MahiMahi.mahiMahiLaws hwa, viewLaws_mahiMahi hws,
    viewLaws_mahiMahi hwa, leastLinked_mahiMahi ws, leastLinked_mahiMahi wa⟩

/-! ## SH-MM11 — one coin, many coins -/

/-- **SH11a, first half.** -/
theorem ratio_le_commitProb {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 5 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r : ℕ}
    (hpop₃ : PopulatedOn U T (r + 3)) (hpopd : PopulatedOn U T (MahiMahi.decisionRoundAt wa r)) :
    ((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator ≤
      commitProb (MahiMahi.goodAt U wa) r := by
  rw [commitProb_eq]
  exact ENNReal.div_le_div_right (Nat.cast_le.mpr (card_goodAt_of_populated hwa hcard hpop₃ hpopd))
    _

/-- `(n − f − b) / n ≥ 1/3` at `n ≥ 3f + 1` and `b ≤ f`. -/
theorem third_le_ratio :
    (3 : ℝ≥0∞)⁻¹ ≤
      ((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator := by
  have hn : (Fintype.card Validator : ℝ≥0∞) ≠ 0 := by
    have := F.card_validators
    exact_mod_cast (by omega : Fintype.card Validator ≠ 0)
  rw [ENNReal.le_div_iff_mul_le (Or.inl hn) (Or.inl (ENNReal.natCast_ne_top _))]
  rw [← ENNReal.div_eq_inv_mul, ENNReal.div_le_iff (by norm_num) (by norm_num)]
  have := F.card_validators
  have := F.card_byzantine
  exact_mod_cast (by omega : Fintype.card Validator ≤
    (Fintype.card Validator - F.f - F.byzantine.card) * 3)

/-- **SH11a, second half.** -/
theorem third_le_commitProb {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 5 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r : ℕ}
    (hpop₃ : PopulatedOn U T (r + 3)) (hpopd : PopulatedOn U T (MahiMahi.decisionRoundAt wa r)) :
    (3 : ℝ≥0∞)⁻¹ ≤ commitProb (MahiMahi.goodAt U wa) r :=
  le_trans third_le_ratio (ratio_le_commitProb hwa hcard hpop₃ hpopd)

/-- **SH11b.** MM2's wave-four form names one committed correct candidate, so `1 ≤ |goodAt|`. -/
theorem inv_card_le_commitProb {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 4 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r : ℕ}
    (hpop₂ : PopulatedOn U T (r + 2)) (hpopd : PopulatedOn U T (MahiMahi.decisionRoundAt wa r)) :
    (Fintype.card Validator : ℝ≥0∞)⁻¹ ≤ commitProb (MahiMahi.goodAt U wa) r := by
  rw [commitProb_eq, ← one_div]
  exact ENNReal.div_le_div_right
    (by exact_mod_cast one_le_card_goodAt_of_populated hwa hcard hpop₂ hpopd) _

/-- **SH-MM11e.** A good coin's block is directly committed, and a view holding the decision round
holds its certificates. -/
theorem chainCommit_of_mem_goodAt {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    {S' : Slots Validator} {coin : ℕ → Validator} {V : View Validator BlockId Payload U} {i r : ℕ}
    (hr : S'.slotRound i = r) (hlead : S'.leader i = coin r) (h : coin r ∈ MahiMahi.goodAt U wa r)
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa r)) :
    ∃ L, IsLeaderBlock (S := S') U i L ∧ MahiMahi.Decided (S := S') wa U V i (some L) := by
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp h
  subst hr
  refine ⟨L, ⟨hL, hLr, hLc.trans hlead.symm⟩, MahiMahi.Decided.directCommit (S := S')
    ⟨hL, hLr, hLc.trans hlead.symm⟩ ?_⟩
  exact MahiMahiProperties.directCommitIn_of_coversUpto hdc hV

/-- **SH-MM11d.** SH11d at MM2's floor. -/
theorem runProb_ge {U : BlockUniverse Validator BlockId Payload} {wa : ℕ} (hwa : 5 ≤ wa)
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r₀ m : ℕ}
    (hpop : ∀ i : Fin m, PopulatedOn U T (r₀ + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (r₀ + i))) :
    ((((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞) /
      Fintype.card Validator) ^ m) ≤ runProb (MahiMahi.goodAt U wa) r₀ m :=
  Steelhead.runProb_ge (goodFloor_mahiMahi hwa) fun i => ⟨hcard, (hpop i).1, (hpop i).2⟩

/-- **A committed candidate's slot is not skipped**: the view decides a slot one way, and a good
coin commits it (SH11e). -/
theorem not_skip_of_mem_goodAt {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    {coin : ℕ → Validator} {V : View Validator BlockId Payload U} {r : ℕ} (hwa : 2 ≤ wa)
    (h : coin r ∈ MahiMahi.goodAt U wa r) (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa r)) :
    ¬ MahiMahi.Decided (S := chainSlots coin) wa U V r none := by
  intro hskip
  obtain ⟨L, -, hdec⟩ := chainCommit_of_mem_goodAt (S' := chainSlots coin) rfl rfl h hV
  have := AnchoredRule.decided_agree (S := chainSlots coin) (MahiMahi.mahiMahiLaws hwa) trivial
    hdec hskip
  simp at this

/-- **The hop stops at the floor** when the view does not skip the slot there. -/
theorem floorLanding_eq_floor [S : Slots Validator] {w : ℕ → ℕ}
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U} {k : ℕ}
    (h : ¬ Decided w U V (k + w (S.kind k)) none) : floorLanding w U V k = k + w (S.kind k) := by
  classical
  have hex : ∃ y, k + w (S.kind k) ≤ y ∧ ¬ Decided w U V y none := ⟨_, le_rfl, h⟩
  rw [floorLanding, dif_pos hex]
  exact Nat.le_antisymm (Nat.find_le ⟨le_rfl, h⟩) (Nat.find_spec hex).1

/-- **The hop never lands below the floor.** -/
theorem floor_le_floorLanding [S : Slots Validator] {w : ℕ → ℕ}
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U} {k : ℕ} :
    k + w (S.kind k) ≤ floorLanding w U V k := by
  classical
  by_cases hex : ∃ y, k + w (S.kind k) ≤ y ∧ ¬ Decided w U V y none
  · rw [floorLanding, dif_pos hex]
    exact (Nat.find_spec hex).1
  · rw [floorLanding, dif_neg hex]

/-- **A landing the view does not skip is the least such slot above the floor**: the fallback of
`floorLanding` is skipped, so a landing that is not fixes the search's value. -/
theorem floorLanding_least [S : Slots Validator] {w : ℕ → ℕ}
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U} {k : ℕ}
    (h : ¬ Decided w U V (floorLanding w U V k) none) :
    ∀ y, k + w (S.kind k) ≤ y → ¬ Decided w U V y none → floorLanding w U V k ≤ y := by
  classical
  have hex : ∃ y, k + w (S.kind k) ≤ y ∧ ¬ Decided w U V y none := by
    by_contra hno
    exact h (by rw [floorLanding, dif_neg hno] at h ⊢; exact absurd ⟨_, le_rfl, h⟩ hno)
  intro y hy hyskip
  rw [floorLanding, dif_pos hex]
  exact Nat.find_le ⟨hy, hyskip⟩

/-- **SH-MM11f.** SH11f at MM2's floor, `n − (n − f − b) = f + b`. -/
theorem noCommitProb_le {U : BlockUniverse Validator BlockId Payload} {wa : ℕ} (hwa : 5 ≤ wa)
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {r₀ m : ℕ}
    (hpop : ∀ i : Fin m, PopulatedOn U T (r₀ + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (r₀ + i))) :
    noCommitProb (MahiMahi.goodAt U wa) r₀ m ≤
      (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m := by
  have h := Steelhead.noCommitProb_le (goodFloor_mahiMahi hwa) (T := T)
    fun i => ⟨hcard, (hpop i).1, (hpop i).2⟩
  rwa [card_sub_floor] at h

/-- **SH-MM11g.** SH11g at MM2's floor. -/
theorem tail_tendsto_zero :
    Tendsto (fun m : ℕ => (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ m)
      atTop (𝓝 0) := by
  have h := Steelhead.tail_tendsto_zero (Validator := Validator) (floor_pos Validator)
  rwa [card_sub_floor] at h

/-! ## SH-MM15 — the tail -/

/-- **SH-MM15a.** SH15a at `mmPair ws wa`, MM2's floor. -/
theorem undecidedProb_le {U : BlockUniverse Validator BlockId Payload} {ws wa I q K : ℕ}
    [NeZero K] (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 5 ≤ wa) (hKI : K ≤ I) (hwaI : wa ≤ I)
    (hq : wa * K ≤ q * I)
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {upd : UpdateRule BlockId}
    {k₀ : ℕ} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K)
    {known : ℕ → Validator} {d : Validator} {s M : ℕ} (h₁ : 1 ≤ s)
    (hpop : ∀ (j : Fin M) (i : Fin (wa * K)),
      PopulatedOn U T (blockRound I q (intervalOf I s) j i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (blockRound I q (intervalOf I s) j i))) :
    undecidedProb U (MahiMahi.mahiMahiAnchored _ _ _ wa)
        (steelheadAnchored _ _ _ (wavelength ws wa)) wa I q K upd k₀ known d s M ≤
      2 * Coin.badBlockBound Validator (wa * K) ^ (M / 2) := by
  have h := Steelhead.undecidedProb_le (p := mmPair Validator BlockId Payload ws wa)
    (mmPair_lawful hws (by omega)) (goodCommits_mahiMahi wa) (goodFloor_mahiMahi hwa)
    (by change ws - 1 ≤ wa - 1; omega) (by change wa - 1 + 1 = wa; omega) hKI hwaI hq (T := T)
    (upd := upd) (known := known) (d := d) h₀ hK hupd h₁
    fun j i => ⟨hcard, (hpop j i).1, (hpop j i).2⟩
  rw [steelheadAt_mmPair] at h
  exact h

/-- **SH-MM15b.** SH15b at `mmPair ws wa`. -/
theorem undecidedProb_le_adaptive {ws wa I q K : ℕ} [NeZero K] (hws : 2 ≤ ws) (hle : ws ≤ wa)
    (hwa : 5 ≤ wa) (hKI : K ≤ I) (hwaI : wa ≤ I) (hq : wa * K ≤ q * I) {upd : UpdateRule BlockId}
    {k₀ : ℕ} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K)
    {known : ℕ → Validator} {d : Validator} {s M : ℕ}
    {σ : (Fin M → Fin (wa * K) → Validator) → BlockUniverse Validator BlockId Payload}
    {G : (Fin M → Fin (wa * K) → Validator) → Fin M → Fin (wa * K) → Finset Validator} (h₁ : 1 ≤ s)
    (hσ : NonAnticipating σ G (MahiMahi.goodAt · wa) I q (intervalOf I s))
    (hc : ∀ g j i, Fintype.card Validator - F.f - F.byzantine.card ≤ (G g j i).card) :
    undecidedProbAgainst (MahiMahi.mahiMahiAnchored _ _ _ wa)
        (steelheadAnchored _ _ _ (wavelength ws wa)) wa I q σ upd k₀ known d s ≤
      2 * Coin.badBlockBound Validator (wa * K) ^ (M / 2) := by
  have h := Steelhead.undecidedProb_le_adaptive (p := mmPair Validator BlockId Payload ws wa)
    (mmPair_lawful hws (by omega)) (goodCommits_mahiMahi wa)
    (by change ws - 1 ≤ wa - 1; omega) (by change wa - 1 + 1 = wa; omega) hKI hwaI hq
    (upd := upd) (known := known) (d := d) h₀ hK hupd h₁ hσ hc
  rw [steelheadAt_mmPair] at h
  exact h

/-- **SH-MM15c.** SH15c at MM2's floor. -/
theorem undecided_tail_tendsto_zero {K : ℕ} :
    Tendsto (fun M : ℕ => 2 * Coin.badBlockBound Validator K ^ (M / 2)) atTop (𝓝 0) :=
  Steelhead.undecided_tail_tendsto_zero (floor_pos Validator)

/-- **SH-MM15d.** SH15a at `mmPair ws wa` and the floor one. -/
theorem undecidedProb_le_four {U : BlockUniverse Validator BlockId Payload} {ws wa I q K : ℕ}
    [NeZero K] (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 4 ≤ wa) (hKI : K ≤ I) (hwaI : wa ≤ I)
    (hq : wa * K ≤ q * I)
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {upd : UpdateRule BlockId}
    {k₀ : ℕ} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K)
    {known : ℕ → Validator} {d : Validator} {s M : ℕ} (h₁ : 1 ≤ s)
    (hpop : ∀ (j : Fin M) (i : Fin (wa * K)),
      PopulatedOn U T (blockRound I q (intervalOf I s) j i + 2) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (blockRound I q (intervalOf I s) j i))) :
    undecidedProb U (MahiMahi.mahiMahiAnchored _ _ _ wa)
        (steelheadAnchored _ _ _ (wavelength ws wa)) wa I q K upd k₀ known d s M ≤
      2 * Coin.badBlockBoundOne Validator (wa * K) ^ (M / 2) := by
  have h := Steelhead.undecidedProb_le (p := mmPair Validator BlockId Payload ws wa)
    (mmPair_lawful hws (by omega)) (goodCommits_mahiMahi wa) (goodFloor_mahiMahi_four hwa)
    (by change ws - 1 ≤ wa - 1; omega) (by change wa - 1 + 1 = wa; omega) hKI hwaI hq (T := T)
    (upd := upd) (known := known) (d := d) h₀ hK hupd h₁
    fun j i => ⟨hcard, (hpop j i).1, (hpop j i).2⟩
  rw [steelheadAt_mmPair] at h
  rw [badBlockBoundOne_eq]
  exact h

/-- **SH-MM15d, the vanishing.** SH15c at the floor one. -/
theorem undecided_tail_four_tendsto_zero {K : ℕ} :
    Tendsto (fun M : ℕ => 2 * Coin.badBlockBoundOne Validator K ^ (M / 2)) atTop (𝓝 0) := by
  simp only [badBlockBoundOne_eq]
  exact Steelhead.undecided_tail_tendsto_zero one_pos

/-- **SH-MM15g.** SH15g at `mmPair ws wa`. -/
theorem decidedAlmostSurely_adaptive [MeasurableSpace Validator]
    [MeasurableSingletonClass Validator] {ws wa I q K : ℕ} [NeZero K] (hws : 2 ≤ ws)
    (hle : ws ≤ wa) (hwa : 5 ≤ wa) (hKI : K ≤ I) (hwaI : wa ≤ I) (hq : wa * K ≤ q * I)
    {σ : ∀ m : ℕ, (Fin m → Fin (wa * K) → Validator) → BlockUniverse Validator BlockId Payload}
    {G : ∀ m : ℕ, (Fin m → Fin (wa * K) → Validator) → Fin m → Fin (wa * K) → Finset Validator}
    {upd : ℕ → UpdateRule BlockId} {k₀ : ℕ} (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K)
    {known : ℕ → Validator} {s : ℕ} (h₁ : 1 ≤ s)
    (hσ : ∀ m, NonAnticipating (σ m) (G m) (MahiMahi.goodAt · wa) I q (intervalOf I s))
    (hc : ∀ (m : ℕ) (g : Fin m → Fin (wa * K) → Validator) (j : Fin m) (i : Fin (wa * K)),
      Fintype.card Validator - F.f - F.byzantine.card ≤ (G m g j i).card) :
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload
          (σ m (blockCoins I q (intervalOf I s) m (wa * K) coin)))
        (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K (MahiMahi.mahiMahiAnchored _ _ _ wa)
            (steelheadAnchored _ _ _ (wavelength ws wa)) coin known (upd m) k₀
          (σ m (blockCoins I q (intervalOf I s) m (wa * K) coin)) V per →
        Settles I K (MahiMahi.mahiMahiAnchored _ _ _ wa)
            (steelheadAnchored _ _ _ (wavelength ws wa)) coin known (upd m) k₀
          (σ m (blockCoins I q (intervalOf I s) m (wa * K) coin)) V per s := by
  have h := Steelhead.decidedAlmostSurely_adaptive (p := mmPair Validator BlockId Payload ws wa)
    (mmPair_lawful hws (by omega)) (goodCommits_mahiMahi wa) (floor_pos Validator)
    (by change ws - 1 ≤ wa - 1; omega) (by change wa - 1 + 1 = wa; omega) hKI hwaI hq
    (upd := upd) (known := known) h₀ hK hupd h₁ hσ hc
  rw [steelheadAt_mmPair] at h
  exact h

/-- **SH-MM15e.** SH15e at `mmPair ws wa`, MM2's floor. -/
theorem decidedAlmostSurely [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    {ws wa I q K : ℕ} [NeZero K] (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 5 ≤ wa) (hKI : K ≤ I)
    (hwaI : wa ≤ I) (hq : wa * K ≤ q * I)
    {U : ℕ → BlockUniverse Validator BlockId Payload} {T : Finset Validator}
    (hcard : quorumCard Validator ≤ T.card) {upd : ℕ → UpdateRule BlockId} {k₀ : ℕ}
    (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K) (hupd : ∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K)
    {known : ℕ → Validator} {s : ℕ} (h₁ : 1 ≤ s)
    (hpop : ∀ (m : ℕ) (j : Fin m) (i : Fin (wa * K)),
      PopulatedOn (U m) T (blockRound I q (intervalOf I s) j i + 3) ∧
      PopulatedOn (U m) T (MahiMahi.decisionRoundAt wa (blockRound I q (intervalOf I s) j i))) :
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (U m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K (MahiMahi.mahiMahiAnchored _ _ _ wa)
            (steelheadAnchored _ _ _ (wavelength ws wa)) coin known (upd m) k₀ (U m) V per →
        Settles I K (MahiMahi.mahiMahiAnchored _ _ _ wa)
            (steelheadAnchored _ _ _ (wavelength ws wa)) coin known (upd m) k₀ (U m) V per s := by
  have h := Steelhead.decidedAlmostSurely (p := mmPair Validator BlockId Payload ws wa)
    (mmPair_lawful hws (by omega)) (goodCommits_mahiMahi wa) (goodFloor_mahiMahi hwa)
    (floor_pos Validator)
    (by change ws - 1 ≤ wa - 1; omega) (by change wa - 1 + 1 = wa; omega) hKI hwaI hq (U := U)
    (T := T) (upd := upd) (known := known) h₀ hK hupd h₁
    fun m j i => ⟨hcard, (hpop m j i).1, (hpop m j i).2⟩
  rw [steelheadAt_mmPair] at h
  exact h

/-- **SH-MM15f.** SH15f at `mmPair ws wa`, MM2's floor. -/
theorem anchoredAlmostSurely [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    {ws wa I q K : ℕ} [NeZero K] (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 5 ≤ wa) (hKI : K ≤ I)
    (hwaI : wa ≤ I) (hq : wa * K ≤ q * I)
    {U : ℕ → BlockUniverse Validator BlockId Payload} {T : Finset Validator}
    (hcard : quorumCard Validator ≤ T.card) {upd : ℕ → UpdateRule BlockId} {k₀ : ℕ}
    (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K) (hupd : ∀ m A k, 1 ≤ k → k ≤ K → 1 ≤ upd m A k ∧ upd m A k ≤ K)
    {known : ℕ → Validator} {s : ℕ} (h₁ : 1 ≤ s)
    (hpop : ∀ (m : ℕ) (j : Fin m) (i : Fin (wa * K)),
      PopulatedOn (U m) T (blockRound I q (intervalOf I s) j i + 3) ∧
      PopulatedOn (U m) T (MahiMahi.decisionRoundAt wa (blockRound I q (intervalOf I s) j i))) :
    ∀ᵐ coin ∂(coinMeasure Validator), ∃ m,
      ∀ (V : View Validator BlockId Payload (U m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K (MahiMahi.mahiMahiAnchored _ _ _ wa)
            (steelheadAnchored _ _ _ (wavelength ws wa)) coin known (upd m) k₀ (U m) V per →
        Anchored I K (MahiMahi.mahiMahiAnchored _ _ _ wa)
            (steelheadAnchored _ _ _ (wavelength ws wa)) coin known (upd m) k₀ (U m) V per s := by
  have h := Steelhead.anchoredAlmostSurely (p := mmPair Validator BlockId Payload ws wa)
    (mmPair_lawful hws (by omega)) (goodCommits_mahiMahi wa) (goodFloor_mahiMahi hwa)
    (floor_pos Validator)
    (by change ws - 1 ≤ wa - 1; omega) (by change wa - 1 + 1 = wa; omega) hKI hwaI hq (U := U)
    (T := T) (upd := upd) (known := known) h₀ hK hupd h₁
    fun m j i => ⟨hcard, (hpop m j i).1, (hpop m j i).2⟩
  rw [steelheadAt_mmPair] at h
  exact h

/-- **SH-MM15h.** SH15h at `mmPair ws wa`, MM2's floor. -/
theorem allDecidedAlmostSurely [MeasurableSpace Validator] [MeasurableSingletonClass Validator]
    {ws wa I q K : ℕ} [NeZero K] (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 5 ≤ wa) (hKI : K ≤ I)
    (hwaI : wa ≤ I) (hq : wa * K ≤ q * I)
    {U : ℕ → ℕ → BlockUniverse Validator BlockId Payload} {T : Finset Validator}
    (hcard : quorumCard Validator ≤ T.card) {upd : ℕ → ℕ → UpdateRule BlockId} {k₀ : ℕ}
    (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K)
    (hupd : ∀ s m A k, 1 ≤ k → k ≤ K → 1 ≤ upd s m A k ∧ upd s m A k ≤ K)
    {known : ℕ → Validator}
    (hpop : ∀ (s m : ℕ) (j : Fin m) (i : Fin (wa * K)),
      PopulatedOn (U s m) T (blockRound I q (intervalOf I s) j i + 3) ∧
      PopulatedOn (U s m) T (MahiMahi.decisionRoundAt wa (blockRound I q (intervalOf I s) j i))) :
    ∀ᵐ coin ∂(coinMeasure Validator), ∀ s, 1 ≤ s → ∃ m,
      ∀ (V : View Validator BlockId Payload (U s m)) (per : ℕ → ℕ),
        V.CoversUpto (blocksHorizon I q wa K (intervalOf I s) m) →
        Matches I K (MahiMahi.mahiMahiAnchored _ _ _ wa)
            (steelheadAnchored _ _ _ (wavelength ws wa)) coin known (upd s m) k₀ (U s m) V per →
        Settles I K (MahiMahi.mahiMahiAnchored _ _ _ wa)
            (steelheadAnchored _ _ _ (wavelength ws wa)) coin known (upd s m) k₀ (U s m) V per
            s := by
  have h := Steelhead.allDecidedAlmostSurely (p := mmPair Validator BlockId Payload ws wa)
    (mmPair_lawful hws (by omega)) (goodCommits_mahiMahi wa) (goodFloor_mahiMahi hwa)
    (floor_pos Validator)
    (by change ws - 1 ≤ wa - 1; omega) (by change wa - 1 + 1 = wa; omega) hKI hwaI hq (U := U)
    (T := T) (upd := upd) (known := known) h₀ hK hupd
    fun s m j i => ⟨hcard, (hpop s m j i).1, (hpop s m j i).2⟩
  rw [steelheadAt_mmPair] at h
  exact h

/-! ## SH-MM11i to SH-MM11m — the search and the scans -/

/-- **SH-MM11i.** SH11i at `mmPair ws wa`, MM2's floor. -/
theorem undecidedAtPeriodOne_le {U : BlockUniverse Validator BlockId Payload} {ws wa : ℕ}
    (hwa : 5 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card)
    {V : View Validator BlockId Payload U} {d : Validator} {s b M : ℕ} (hs : s < b)
    (hpop : ∀ (j : Fin M) (i : Fin wa), PopulatedOn U T (b + j * wa + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (b + j * wa + i)))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + M * wa - 1))) :
    (PMF.uniformOfFintype (Fin M → Fin wa → Validator)).toOuterMeasure
        {g | ∀ v, ¬ Decided (S := chainSlots (coinOfBlocksFrom b g d)) (wavelength ws wa) U V s v}
      ≤ Coin.badBlockBound Validator wa ^ M := by
  have h := Steelhead.undecidedAtPeriodOne_le (p := mmPair Validator BlockId Payload ws wa)
    (leastLinked_mahiMahi ws) (leastLinked_mahiMahi wa) (goodCommits_mahiMahi wa)
    (goodFloor_mahiMahi hwa) (by change wa - 1 + 1 = wa; omega) (T := T) (d := d) hs
    (fun j i => ⟨hcard, (hpop j i).1, (hpop j i).2⟩)
    (hV.mono (by unfold MahiMahi.decisionRoundAt; omega))
  rw [steelheadAt_mmPair] at h
  exact h

/-- **SH-MM11j, second half.** SH11j's second half at `mmPair ws wa`. -/
theorem decided_of_firstGoodBlock {U : BlockUniverse Validator BlockId Payload} {ws wa : ℕ}
    {V : View Validator BlockId Payload U} {d : Validator} {s b M : ℕ} (hwa : 1 ≤ wa)
    (hs : s < b) {g : Fin M → Fin wa → Validator}
    (hM : firstGoodBlock (MahiMahi.goodAt U wa) wa b g < M)
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa
      (b + (firstGoodBlock (MahiMahi.goodAt U wa) wa b g + 1) * wa - 1))) :
    ∃ v, Decided (S := chainSlots (coinOfBlocksFrom b g d)) (wavelength ws wa) U V s v := by
  have hV' : V.CoversUpto
      (b + (firstGoodBlock (MahiMahi.goodAt U wa) wa b g + 1) * wa - 1 + (wa - 1)) :=
    hV.mono (by unfold MahiMahi.decisionRoundAt; omega)
  obtain ⟨v, hv⟩ := Steelhead.decided_of_firstGoodBlock
    (p := mmPair Validator BlockId Payload ws wa) (leastLinked_mahiMahi ws)
    (leastLinked_mahiMahi wa) (goodCommits_mahiMahi wa) (by change wa - 1 + 1 = wa; omega)
    (d := d) hs hM hV'
  exact ⟨v, decided_mmPair_iff (S := chainSlots (coinOfBlocksFrom b g d)) |>.mp hv⟩

/-- **SH-MM11j, first half.** SH11j at MM2's floor. -/
theorem expected_firstGoodBlock_le {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 5 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {b M : ℕ}
    (hpop : ∀ (j : Fin M) (i : Fin wa), PopulatedOn U T (b + j * wa + i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (b + j * wa + i))) :
    (∑ g : Fin M → Fin wa → Validator, PMF.uniformOfFintype (Fin M → Fin wa → Validator) g *
        ((firstGoodBlock (MahiMahi.goodAt U wa) wa b g + 1 : ℕ) : ℝ≥0∞)) ≤
      ((Fintype.card Validator : ℝ≥0∞) /
        ((Fintype.card Validator - F.f - F.byzantine.card : ℕ) : ℝ≥0∞)) ^ wa :=
  Steelhead.expected_firstGoodBlock_le (goodFloor_mahiMahi hwa) (by omega) (T := T)
    fun j i => ⟨hcard, (hpop j i).1, (hpop j i).2⟩

/-- **SH-MM11k, first half.** SH11j at the floor one. -/
theorem expected_firstGoodBlock_le_four {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 4 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {b M : ℕ}
    (hpop : ∀ (j : Fin M) (i : Fin wa), PopulatedOn U T (b + j * wa + i + 2) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (b + j * wa + i))) :
    (∑ g : Fin M → Fin wa → Validator, PMF.uniformOfFintype (Fin M → Fin wa → Validator) g *
        ((firstGoodBlock (MahiMahi.goodAt U wa) wa b g + 1 : ℕ) : ℝ≥0∞)) ≤
      (Fintype.card Validator : ℝ≥0∞) ^ wa := by
  have := F.card_validators
  have h := Steelhead.expected_firstGoodBlock_le (goodFloor_mahiMahi_four hwa) (by omega)
    (T := T) fun j i => ⟨hcard, (hpop j i).1, (hpop j i).2⟩
  rwa [Nat.cast_one, div_one] at h

/-- **SH-MM11l.** SH11l at MM2's floor, `n − (n − f − b) = f + b`. -/
theorem noCommitProbOn_le {U : BlockUniverse Validator BlockId Payload} {wa : ℕ} (hwa : 5 ≤ wa)
    {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {c : ℕ} {ρ : Fin c → ℕ}
    (hpop : ∀ i : Fin c, PopulatedOn U T (ρ i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (ρ i))) :
    noCommitProbOn (MahiMahi.goodAt U wa) ρ ≤
      (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ c := by
  have h := Steelhead.noCommitProbOn_le (goodFloor_mahiMahi hwa) (T := T)
    fun i => ⟨hcard, (hpop i).1, (hpop i).2⟩
  rwa [card_sub_floor] at h

/-- **SH-MM11m.** SH11m at MM2's floor. -/
theorem expected_firstGoodInterval_le {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 5 ≤ wa) {T : Finset Validator} (hcard : quorumCard Validator ≤ T.card) {M c : ℕ}
    {ρ : Fin M → Fin c → ℕ}
    (hpop : ∀ (j : Fin M) (i : Fin c), PopulatedOn U T (ρ j i + 3) ∧
      PopulatedOn U T (MahiMahi.decisionRoundAt wa (ρ j i))) :
    (∑ g : Fin M → Fin c → Validator, PMF.uniformOfFintype (Fin M → Fin c → Validator) g *
        ((firstGoodInterval (MahiMahi.goodAt U wa) ρ g + 1 : ℕ) : ℝ≥0∞)) ≤
      (1 - (((F.f + F.byzantine.card : ℕ) : ℝ≥0∞) / Fintype.card Validator) ^ c)⁻¹ := by
  have h := Steelhead.expected_firstGoodInterval_le (goodFloor_mahiMahi hwa) (T := T)
    fun j i => ⟨hcard, (hpop j i).1, (hpop j i).2⟩
  rwa [card_sub_floor] at h

/-! ## SH-MM15i -/

/-- **SH-MM15i.** SH15i at the pair's rules, lawful at waves of two rounds or more. -/
theorem matchingPer_matches {I K wa : ℕ} [NeZero K] {ws : ℕ} (hws : 2 ≤ ws) (hwa : 3 ≤ wa)
    {coin known : ℕ → Validator} {upd : UpdateRule BlockId} {k₀ : ℕ}
    {U : BlockUniverse Validator BlockId Payload} {V : View Validator BlockId Payload U} :
    Matches I K (MahiMahi.mahiMahiAnchored _ _ _ wa) (steelheadAnchored _ _ _ (wavelength ws wa))
      coin known upd k₀ U V
      (Steelhead.matchingPer I K (MahiMahi.mahiMahiAnchored _ _ _ wa)
        (steelheadAnchored _ _ _ (wavelength ws wa)) coin known upd k₀ U V) := by
  have hw2 := wavelength_two_le hws (by omega : 2 ≤ wa)
  exact Steelhead.matchingPer_matches (MahiMahi.mahiMahiLaws (by omega)) (steelheadLaws hw2)
    (viewLaws_steelhead hw2)

end MahiMahiPair

end Steelhead

end LeanDag
