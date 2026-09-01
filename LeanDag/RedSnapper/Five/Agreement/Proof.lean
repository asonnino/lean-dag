import LeanDag.RedSnapper.Five.Agreement.Statement
import LeanDag.RedSnapper.Five.RecoverySafety.Proof
import LeanDag.RedSnapper.Five.FullCertSafety.Proof

/-!
# 5f+1 agreement — proof

Generated proof layer; not part of the audit surface. Route-pair
analysis, as in Theorem safety-5f: the certificate pairs close by RS6
(`FullCertSafety.commitExcludesUnlock`, `fullCertUniqueness`); the
certificate-versus-recovery pairs by RS7's reflection (the round
condition of the paper's miscited step — finding 9 — never arises,
because the reflection claim is round-unconditional); the
recovery-versus-unlock pair by the `⊥` core against the winner's frozen
supporters; the recovery pairs by resolution uniqueness and
antisymmetry.
-/

namespace LeanDag

namespace RedSnapper

namespace FiveAgreement

open RecoverySafety FullCertSafety

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj} {A : Anchors U}

omit [DecidableEq BlockId] in
/-- An eligible transaction's frozen supporters exclude a full unlock
certificate for the object, at any round: before the resolution the `⊥`
core would persist into the markers, after it the markers persist into
the votes. -/
private theorem no_unlock_of_eligible (hmove : MoveDiscipline U)
    (hfd : FreezeDiscipline U) {aₖ a : BlockId} {o : Obj} {tx : Tx} (ha : a ∈ U.ids)
    (helig : EligibleFive U aₖ a o tx) : ∀ C' ∈ U.ids, ¬ IsFullUnlockCert U C' o := by
  intro C' hC' hunlock
  obtain ⟨⟨hown, hcand⟩, w, hw, hwcard⟩ := helig
  have hn := F.card_validators
  obtain ⟨S, hS, hk, hall, hex⟩ := correct_core_exists hC' hunlock
  have hρ : 0 < (U.block C').round := round_pos_of_atLeast hC' quorum_pos hunlock
  have hcount : Fintype.card Validator < S.card + half Validator := by
    unfold quorum at hk
    unfold half
    omega
  have hpersist : ∀ v ∈ S, ∀ b ∈ U.ids, (U.block b).author = v →
      (U.block C').round ≤ (U.block b).round + 1 →
      StanceIs U v o b (some Stance.bot) := by
    intro v hv b hb hab hr
    refine stance_persists (ρ₀ := (U.block C').round - 1) hmove hS hcount
      (fun x hx e he hae hre => ?_) hv hb hab (by omega)
    exact hae ▸ hall x hx e he hae (by omega)
  refine not_atLeastV_of_disjoint hcount (fun v hP hvS => ?_) ⟨w, hw, hwcard⟩
  obtain ⟨hfr, hst⟩ := hP
  have hvc : v ∈ (Correct : Finset Validator) := hS hvS
  obtain ⟨m, hm, ham, hrm, hmk⟩ := hfr
  have hcm : (U.block m).author ∈ (Correct : Finset Validator) := ham.symm ▸ hvc
  obtain ⟨s, hds, hsta⟩ := stance_at_of_frozen hfd hm ha hcm hrm hmk
  have hs : s = Stance.ack tx := Option.some.inj (stanceIs_unique (ham ▸ hsta) hst)
  subst hs
  rcases le_or_gt (U.block C').round ((U.block m).round + 1) with hcase | hcase
  · -- the ⊥ core persists into the marker, which declares an ACK
    have hbot := hpersist v hvS m hm ham hcase
    have hself : StanceIs U v o m (some (Stance.ack tx)) :=
      ham ▸ stanceIs_self_of_declares hm hds
    have := stanceIs_unique hbot hself
    simp at this
  · -- the marker precedes the core's votes, which then read the ACK
    obtain ⟨q, hq, haq, hqr, hPq⟩ := hex v hvS
    have hcq : (U.block q).author ∈ (Correct : Finset Validator) := haq.symm ▸ hvc
    have hrqm : Reaches U q m :=
      reaches_own_of_round_le hq hm hcq (ham.trans haq.symm) (by omega)
    obtain ⟨s', hds', hstq⟩ := stance_at_of_frozen hfd hm hq hcm hrqm hmk
    have hss : s' = Stance.ack tx := Option.some.inj (hds' ▸ hds)
    subst hss
    have hbotq : StanceIs U (U.block m).author o q (some Stance.bot) := by
      have := hPq
      rw [haq, ← ham] at this
      exact this
    have := stanceIs_unique hstq hbotq
    simp at this

omit [DecidableEq BlockId] in
/-- No transaction is both finalised and dropped. -/
private theorem fate_exclusive {V V' : View U} {prio : Tx → Tx → Prop}
    (hord : IsLinearOrder Tx prio) (hfive : Five Validator) (hmove : MoveDiscipline U)
    (hfd : FreezeDiscipline U) {tx : Tx}
    (h₁ : VerdictFive U A V prio tx Fate.finalized)
    (h₂ : VerdictFive U A V' prio tx Fate.dropped) : False := by
  cases h₁ with
  | fullFinal hown hC₁ hcert =>
      cases h₂ with
      | fullUnlockDrop hC₂ hunlock hb hcand =>
          exact commitExcludesUnlock hmove _ (V.subset_ids hC₁) _ (V'.subset_ids hC₂)
            tx hcert hunlock
      | recoveryDropLoser hres hlk hla hcand helig' hmin' hne' =>
          obtain ⟨-, huniq⟩ := recoveryReflects_at hmove hfd hfive hres hlk hla
            hown rfl ⟨_, V.subset_ids hC₁, hcert⟩
          exact hne' (huniq _ helig').symm
      | recoveryDropBot hres hlk hla hcand hempty =>
          obtain ⟨helig, -⟩ := recoveryReflects_at hmove hfd hfive hres hlk hla
            hown rfl ⟨_, V.subset_ids hC₁, hcert⟩
          exact hempty tx helig
  | recoveryFinal hres hlk hla helig hmin =>
      cases h₂ with
      | fullUnlockDrop hC₂ hunlock hb hcand =>
          exact no_unlock_of_eligible hmove hfd (anchor_mem hla) helig
            _ (V'.subset_ids hC₂) hunlock
      | recoveryDropLoser hres' hlk' hla' hcand helig' hmin' hne' =>
          obtain ⟨hi, hj⟩ := (resolutionUnique (U := U) (A := A) hord).1
            _ _ _ _ _ hres hres'
          subst hi
          subst hj
          rw [hlk] at hlk'
          rw [hla] at hla'
          rw [← Option.some.inj hlk', ← Option.some.inj hla'] at helig' hmin'
          haveI := hord
          exact hne' (antisymm (hmin' _ helig) (hmin _ helig')).symm
      | recoveryDropBot hres' hlk' hla' hcand hempty =>
          obtain ⟨hi, hj⟩ := (resolutionUnique (U := U) (A := A) hord).1
            _ _ _ _ _ hres hres'
          subst hi
          subst hj
          rw [hlk] at hlk'
          rw [hla] at hla'
          rw [← Option.some.inj hlk', ← Option.some.inj hla'] at hempty
          exact hempty tx helig

omit [DecidableEq BlockId] in
theorem verdictAgreement {prio : Tx → Tx → Prop} (hord : IsLinearOrder Tx prio)
    (hfive : Five Validator) (hmove : MoveDiscipline U) (hfd : FreezeDiscipline U) :
    VerdictAgreement U A prio := by
  intro V V' tx f f' h h'
  cases f <;> cases f'
  · rfl
  · exact absurd (fate_exclusive hord hfive hmove hfd h h') id
  · exact absurd (fate_exclusive hord hfive hmove hfd h' h) id
  · rfl

omit [DecidableEq BlockId] in
theorem noConflictingFinal {prio : Tx → Tx → Prop} (hord : IsLinearOrder Tx prio)
    (hfive : Five Validator) (hmove : MoveDiscipline U) (hfd : FreezeDiscipline U) :
    NoConflictingFinal U A prio := by
  intro V V' tx tx' hconf h₁ h₂
  cases h₁ with
  | fullFinal hown hC₁ hcert =>
      cases h₂ with
      | fullFinal hown' hC₂ hcert' =>
          exact fullCertUniqueness hmove _ (V.subset_ids hC₁) _ (V'.subset_ids hC₂)
            tx tx' hconf hcert hcert'
      | recoveryFinal hres hlk hla helig hmin =>
          obtain ⟨-, huniq⟩ := recoveryReflects_at hmove hfd hfive hres hlk hla
            hown hconf.2 ⟨_, V.subset_ids hC₁, hcert⟩
          exact hconf.1 (huniq _ helig).symm
  | recoveryFinal hres hlk hla helig hmin =>
      cases h₂ with
      | fullFinal hown' hC₂ hcert' =>
          obtain ⟨-, huniq⟩ := recoveryReflects_at hmove hfd hfive hres hlk hla
            hown' hconf.2.symm ⟨_, V'.subset_ids hC₂, hcert'⟩
          exact hconf.1 (huniq _ helig)
      | recoveryFinal hres' hlk' hla' helig' hmin' =>
          rw [← hconf.2] at hres' helig' hmin'
          obtain ⟨hi, hj⟩ := (resolutionUnique (U := U) (A := A) hord).1
            _ _ _ _ _ hres hres'
          subst hi
          subst hj
          rw [hlk] at hlk'
          rw [hla] at hla'
          rw [← Option.some.inj hlk', ← Option.some.inj hla'] at helig' hmin'
          haveI := hord
          exact hconf.1 (antisymm (hmin _ helig') (hmin' _ helig))

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U A prio hord hfive hmove hfd
  exact ⟨verdictAgreement hord hfive hmove hfd, noConflictingFinal hord hfive hmove hfd⟩

end FiveAgreement

end RedSnapper

end LeanDag
