import LeanDag.Barnacle.Model.Heads
import LeanDag.Barnacle.Helpers.Schedule
import Mathlib.Data.Finset.Prod

/-!
# Heads helpers

Not part of the audit surface. The head arithmetic under `Sched m`; the
stretch descent from `indirect` alone; a slot is decided once the head
a wave above it is committed; heads decide the rounds below them; the
liveness clause from a run of heads; the pigeonhole for round-robin;
and round-robin's liveness.
-/

namespace LeanDag

namespace Barnacle

section HeadArith

variable {Validator : Type}
variable (getLeader : ℕ → Validator) {W : ℕ} (hk : Keyed getLeader W)
  (m : ℕ) (hm : 0 < m) (hmax : m ≤ W)

/-- The head of round `ρ` is slot `m * ρ`. -/
theorem Sched_slotRound_head (ρ : ℕ) :
    (Sched getLeader hk m hm hmax).slotRound (m * ρ) = ρ := by
  rw [Sched_slotRound, Nat.mul_div_cancel_left ρ hm]

/-- The head of round `ρ` is led by `getLeader ρ`, whatever the count. -/
theorem Sched_leader_head (ρ : ℕ) :
    (Sched getLeader hk m hm hmax).leader (m * ρ) = getLeader ρ := by
  rw [Sched_leader, Nat.mul_div_cancel_left ρ hm, Nat.mul_mod_right, Nat.add_zero]

/-- A slot below the head of `ρ` sits at a round below `ρ`. -/
theorem Sched_slotRound_lt_of_lt_head {κ ρ : ℕ} (h : κ < m * ρ) :
    (Sched getLeader hk m hm hmax).slotRound κ < ρ := by
  rw [Sched_slotRound]; exact Nat.div_lt_of_lt_mul h

/-- A slot at a round below `ρ` sits below the head of `ρ`. -/
theorem Sched_lt_head_of_slotRound_lt {κ ρ : ℕ}
    (h : (Sched getLeader hk m hm hmax).slotRound κ < ρ) : κ < m * ρ := by
  rw [Sched_slotRound] at h
  rw [Nat.mul_comm]; exact (Nat.div_lt_iff_lt_mul hm).mp h

/-- **What BN9b needs.** For a slot `κ` at round `r` and the head `h := m * (r + w)` of round
`r + w`: `κ`'s round plus `w` is exactly `h`'s round, `κ < h`, and every slot strictly between
is *not* a full wave above `κ` — so `indirect`'s intermediate hypothesis is vacuous. -/
theorem Sched_head_above (w' : ℕ) (hw : 0 < w') (κ : ℕ) :
    let S := Sched getLeader hk m hm hmax
    S.slotRound κ + w' = S.slotRound (m * (S.slotRound κ + w')) ∧
    κ < m * (S.slotRound κ + w') ∧
    ∀ i', κ < i' → i' < m * (S.slotRound κ + w') →
      ¬ (S.slotRound κ + w' ≤ S.slotRound i') := by
  intro S
  refine ⟨(Sched_slotRound_head getLeader hk m hm hmax _).symm, ?_, ?_⟩
  · exact Sched_lt_head_of_slotRound_lt getLeader hk m hm hmax (by omega)
  · intro i' _ hi' hle
    have := Sched_slotRound_lt_of_lt_head getLeader hk m hm hmax hi'
    omega


end HeadArith

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section Heads

variable {R : LiveRule Validator BlockId Payload} {slack : ℕ}

/-- **BN9a, the stretch descent.** -/
theorem stretchDescent (hD : R.Descent slack) (S : Slots Validator) {U : R.Universe}
    (V : R.View U) {b top : ℕ}
    (hspan : ∀ i, i < b → S.slotRound i + R.waveLength ≤ S.slotRound top)
    (hdec : ∀ j, b ≤ j → j ≤ top → ∃ v, R.Decided S V j v)
    (htop : ∃ B, R.Decided S V top (some B)) :
    ∀ i, i < b → ∃ v, R.Decided S V i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, R.Decided S V i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      have hex : ∃ j, S.slotRound i + R.waveLength ≤ S.slotRound j ∧
          ∃ B, R.Decided S V j (some B) := ⟨top, hspan i hi, htop⟩
      have hle : Nat.find hex ≤ top := Nat.find_min' hex ⟨hspan i hi, htop⟩
      obtain ⟨hgap, B, hB⟩ := Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < Nat.find hex →
          S.slotRound i + R.waveLength ≤ S.slotRound i' → R.Decided S V i' none := by
        intro i' h1 h2 h3
        have hnc : ¬ ∃ C, R.Decided S V i' (some C) := fun hc => Nat.find_min hex h2 ⟨h3, hc⟩
        have hdec' : ∃ v, R.Decided S V i' v := by
          by_cases hi'b : i' < b
          · exact ih i' hi'b (by omega)
          · exact hdec i' (by omega) (by omega)
        obtain ⟨v, hv⟩ := hdec'
        cases v with
        | none => exact hv
        | some C => exact absurd ⟨C, hv⟩ hnc
      exact hD.indirect S V i (Nat.find hex) B hgap hB hmid
  intro i hi
  exact key (b - i) i hi (le_refl _)

variable (getLeader : ℕ → Validator) {W : ℕ} (hk : Keyed getLeader W)
  (m : ℕ) (hm : 0 < m) (hmax : m ≤ W)

/-- A slot is decided once the head a wave above it is committed: the intermediates are
vacuous. From `indirect` alone. -/
theorem decided_of_head_committed (hD : R.Descent slack)
    {U : R.Universe} (V : R.View U) (κ : ℕ)
    (hhead : ∃ L, R.Decided (Sched getLeader hk m hm hmax) V
      (m * ((Sched getLeader hk m hm hmax).slotRound κ + R.waveLength)) (some L)) :
    ∃ v, R.Decided (Sched getLeader hk m hm hmax) V κ v := by
  obtain ⟨L, hL⟩ := hhead
  refine hD.indirect _ V κ _ L ?_ hL ?_
  · simp only [Sched_slotRound]
    rw [Nat.mul_div_cancel_left _ hm]
  · intro i' _ hi' hle
    simp only [Sched_slotRound] at hi' hle
    have := Nat.div_lt_of_lt_mul hi'
    omega

/-- **BN9b.** Heads of rounds `ρ + w, …, ρ + 2w − 1` `T`-led (with `T` from `goodLeaders`)
and their waves under `N`: every slot at rounds `[ρ, ρ + w)` is decided and the head of `ρ + w`
is committed, on the full view. -/
theorem headsDecide (hD : R.Descent slack) (hw : 0 < R.waveLength)
    {U : R.Universe} {Rnd N : ℕ} {T : Finset Validator}
    (hT : ∀ (S : Slots Validator) (κ : ℕ), Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
      S.leader κ ∈ T → ∃ L, R.Decided S (R.full U) κ (some L))
    (ρ : ℕ) (hRnd : Rnd ≤ ρ + R.waveLength)
    (hN : ρ + R.waveLength + R.waveLength + R.waveLength ≤ N + 1)
    (hheads : ∀ i, i < R.waveLength → getLeader (ρ + R.waveLength + i) ∈ T) :
    (∀ κ, ρ ≤ (Sched getLeader hk m hm hmax).slotRound κ →
      (Sched getLeader hk m hm hmax).slotRound κ < ρ + R.waveLength →
      ∃ v, R.Decided (Sched getLeader hk m hm hmax) (R.full U) κ v) ∧
    ∃ L, R.Decided (Sched getLeader hk m hm hmax) (R.full U) (m * (ρ + R.waveLength)) (some L) := by
  -- the head of any round `ρ + w + i`, `i < w`, is committed
  have hhead : ∀ i, i < R.waveLength →
      ∃ L, R.Decided (Sched getLeader hk m hm hmax) (R.full U)
        (m * (ρ + R.waveLength + i)) (some L) := by
    intro i hi
    refine hT _ _ ?_ ?_ ?_
    · rw [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
    · rw [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
    · rw [Sched_leader, Nat.mul_div_cancel_left _ hm, Nat.mul_mod_right, Nat.add_zero]
      exact hheads i hi
  refine ⟨?_, by simpa using hhead 0 hw⟩
  intro κ hlo hhi
  apply decided_of_head_committed getLeader hk m hm hmax hD
  have := hhead ((Sched getLeader hk m hm hmax).slotRound κ - ρ) (by omega)
  rwa [show ρ + R.waveLength + ((Sched getLeader hk m hm hmax).slotRound κ - ρ)
    = (Sched getLeader hk m hm hmax).slotRound κ + R.waveLength by omega] at this


/-- **BN9b′, subtraction-free.** Heads of rounds `ρ, …, ρ + w − 1` `T`-led, waves under `N`:
every slot at a round `r` with `r < ρ ≤ r + w` is decided, and the head of `ρ` is committed. -/
theorem headsDecide_at (hD : R.Descent slack) (hw : 0 < R.waveLength)
    {U : R.Universe} {Rnd N : ℕ} {T : Finset Validator}
    (hT : ∀ (S : Slots Validator) (κ : ℕ), Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
      S.leader κ ∈ T → ∃ L, R.Decided S (R.full U) κ (some L))
    (ρ : ℕ) (hRnd : Rnd ≤ ρ) (hN : ρ + R.waveLength + R.waveLength ≤ N + 1)
    (hheads : ∀ i, i < R.waveLength → getLeader (ρ + i) ∈ T) :
    (∀ κ, (Sched getLeader hk m hm hmax).slotRound κ < ρ →
      ρ ≤ (Sched getLeader hk m hm hmax).slotRound κ + R.waveLength →
      ∃ v, R.Decided (Sched getLeader hk m hm hmax) (R.full U) κ v) ∧
    ∃ L, R.Decided (Sched getLeader hk m hm hmax) (R.full U) (m * ρ) (some L) := by
  have hhead : ∀ i, i < R.waveLength →
      ∃ L, R.Decided (Sched getLeader hk m hm hmax) (R.full U) (m * (ρ + i)) (some L) := by
    intro i hi
    refine hT _ _ ?_ ?_ ?_
    · rw [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
    · rw [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
    · rw [Sched_leader, Nat.mul_div_cancel_left _ hm, Nat.mul_mod_right, Nat.add_zero]
      exact hheads i hi
  refine ⟨?_, by simpa using hhead 0 hw⟩
  intro κ hlo hhi
  apply decided_of_head_committed getLeader hk m hm hmax hD
  have := hhead ((Sched getLeader hk m hm hmax).slotRound κ + R.waveLength - ρ) (by omega)
  rwa [show ρ + ((Sched getLeader hk m hm hmax).slotRound κ + R.waveLength - ρ)
    = (Sched getLeader hk m hm hmax).slotRound κ + R.waveLength by omega] at this

/-- **BN9c′ at gap `c₀`**: `HeadsRun` called at `r + 1`. -/
theorem liveOn_of_headsRun (hD : R.Descent slack) (hw : 0 < R.waveLength)
    (hheads : ∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack →
      HeadsRun getLeader T R.waveLength c₀) :
    R.LiveOn (Sched getLeader hk m hm hmax) c₀ := by
  intro U Rnd N hgood
  obtain ⟨T, hcardT, hT⟩ := hD.goodLeaders U Rnd N hgood
  have hrun := hheads T hcardT
  refine ⟨?_, ?_⟩
  · intro κ hRnd hN
    set S := Sched getLeader hk m hm hmax with hS
    obtain ⟨ρ', hρ'lo, hρ'hi, hled⟩ := hrun (S.slotRound κ + 1)
    obtain ⟨hdec, htop⟩ := headsDecide_at getLeader hk m hm hmax hD hw hT ρ'
      (by omega) (by omega) hled
    by_cases hcase : ρ' ≤ S.slotRound κ + R.waveLength
    · exact hdec κ (by omega) hcase
    · refine stretchDescent hD S (R.full U) (b := m * (ρ' - R.waveLength)) (top := m * ρ')
        ?_ ?_ htop κ ?_
      · intro i hi
        simp only [Sched_slotRound] at hi ⊢
        rw [Nat.mul_div_cancel_left _ hm]
        have := Nat.div_lt_of_lt_mul hi
        omega
      · intro j hlo hhi
        rcases Nat.lt_or_eq_of_le hhi with hlt | heq
        · refine hdec j ?_ ?_
          · simp only [Sched_slotRound]; exact Nat.div_lt_of_lt_mul hlt
          · simp only [Sched_slotRound]
            have : ρ' - R.waveLength ≤ j / m :=
              (Nat.le_div_iff_mul_le hm).mpr (by rw [Nat.mul_comm]; exact hlo)
            omega
        · subst heq; obtain ⟨L, hL⟩ := htop; exact ⟨some L, hL⟩
      · simp only [Sched_slotRound] at hcase ⊢
        rw [Nat.mul_comm]; exact (Nat.div_lt_iff_lt_mul hm).mp (by omega)
  · intro r hRnd hN
    obtain ⟨ρ', hρ'lo, hρ'hi, hled⟩ := hrun r
    refine ⟨m * ρ', ?_, ?_, ?_⟩
    · rw [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; exact hρ'lo
    · rw [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
    · refine hT _ _ ?_ ?_ ?_
      · rw [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
      · rw [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
      · rw [Sched_leader, Nat.mul_div_cancel_left _ hm, Nat.mul_mod_right, Nat.add_zero]
        simpa using hled 0 hw

#print axioms liveOn_of_headsRun

end Heads

/-- **The pigeonhole.** If no window of `g` consecutive residues starting
in a cycle lay inside `T`, choosing for each start a residue outside `T`
within its window would inject `Fin n` into `Fin g × Tᶜ`. -/
theorem roundRobin_headsRun (n : ℕ) (hn : 0 < n) (T : Finset (Fin n)) (slack g : ℕ)
    (hT : n ≤ T.card + slack) (hbound : g * slack + 1 ≤ n) :
    HeadsRun (roundRobin n hn) T g (n + g - 1) := by
  intro r
  by_contra hcon
  push Not at hcon
  have hwin : ∀ x : Fin n, ∃ i, i < g ∧ roundRobin n hn (r + x + i) ∉ T := by
    intro x
    obtain ⟨i, hi, hiT⟩ := hcon (r + x) (by omega) (by omega)
    exact ⟨i, hi, hiT⟩
  choose k hk using hwin
  let φ : Fin n → Fin g × Fin n := fun x => (⟨k x, (hk x).1⟩, roundRobin n hn (r + x + k x))
  have hmaps : Set.MapsTo φ ↑(Finset.univ : Finset (Fin n))
      ↑((Finset.univ : Finset (Fin g)) ×ˢ Tᶜ) := by
    intro x _
    simp only [Finset.coe_product, Set.mem_prod, Finset.mem_coe, Finset.mem_univ, true_and,
      Finset.mem_compl]
    exact (hk x).2
  have hinj : Set.InjOn φ ↑(Finset.univ : Finset (Fin n)) := by
    intro x _ y _ hxy
    simp only [φ, Prod.mk.injEq, Fin.mk.injEq] at hxy
    obtain ⟨hkxy, hres⟩ := hxy
    have hres' : (r + x + k x) % n = (r + y + k y) % n := congrArg Fin.val hres
    rw [hkxy] at hres'
    have h2 : (↑x : ℕ) % n = ↑y % n :=
      Nat.ModEq.add_left_cancel' r (Nat.ModEq.add_right_cancel' (k y) hres')
    rw [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] at h2
    exact Fin.ext h2
  have hcard := Finset.card_le_card_of_injOn φ hmaps hinj
  rw [Finset.card_univ, Fintype.card_fin, Finset.card_product, Finset.card_univ, Fintype.card_fin,
    Finset.card_compl, Fintype.card_fin] at hcard
  have hcompl : n - T.card ≤ slack := by omega
  have := Nat.mul_le_mul_left g hcompl
  omega


/-- **Round-robin is live** at every count, with gap `n + waveLength − 1`. -/
theorem liveOn_roundRobin {n : ℕ} (hn : 0 < n) {BlockId : Type} [DecidableEq BlockId]
    {Payload : Type} (R : LiveRule (Fin n) BlockId Payload) {slack : ℕ} (hD : R.Descent slack)
    (hw : 0 < R.waveLength) (hbound : R.waveLength * slack + 1 ≤ n)
    {W : ℕ} (hk : Keyed (roundRobin n hn) W) (m : ℕ) (hm : 0 < m) (hmax : m ≤ W) :
    R.LiveOn (Sched (roundRobin n hn) hk m hm hmax) (n + R.waveLength - 1) :=
  liveOn_of_headsRun (roundRobin n hn) hk m hm hmax hD hw fun T hT =>
    roundRobin_headsRun n hn T slack R.waveLength (by simpa using hT) hbound

end Barnacle

end LeanDag
