import LeanDag.RedSnapper.Helpers.Verdict
import LeanDag.RedSnapper.Helpers.Chain
import LeanDag.RedSnapper.Model.Liveness
import LeanDag.RedSnapper.Model.HonestVoting

/-!
# Liveness lemmas

Generated infrastructure for the RS4/RS5 proofs: the correct pool
carries both thresholds, per-author blocks assemble into `AtLeast`
witnesses, an unrivalled transaction makes every correct block that
includes it a fast vote, a visible certificate behind a kept ACK is a
certificate at or below the block, and readiness yields resolution at a
least index. Nothing here is part of the audit surface.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [T : Transactions Tx Obj] {U : Universe Validator BlockId Tx Obj}

omit T in
/-- The correct pool is at least a quorum. -/
theorem quorum_le_card_correct :
    quorum Validator ≤ (Correct : Finset Validator).card := by
  have h1 := F.card_byzantine
  have h2 : (Correct : Finset Validator).card =
      Fintype.card Validator - F.byzantine.card := by
    rw [Correct, Finset.card_compl]
  unfold quorum
  omega

omit T in
/-- The correct pool is at least a half. -/
theorem half_le_card_correct :
    half Validator ≤ (Correct : Finset Validator).card := by
  have h1 := F.card_byzantine
  have h2 := F.card_validators
  have h3 : (Correct : Finset Validator).card =
      Fintype.card Validator - F.byzantine.card := by
    rw [Correct, Finset.card_compl]
  unfold half
  omega

omit T in
/-- Per-author blocks assemble into a threshold: if every correct
validator has a `P`-block in `s`, then `s` carries `k` distinct
`P`-authors for any `k ≤ |Correct|`. -/
theorem atLeast_of_correct_blocks {s : Finset BlockId} {P : BlockId → Prop} {k : ℕ}
    (hk : k ≤ (Correct : Finset Validator).card)
    (h : ∀ v ∈ (Correct : Finset Validator), ∃ b ∈ s, (U.block b).author = v ∧ P b) :
    AtLeast U k s P := by
  classical
  refine ⟨s.filter P, Finset.filter_subset _ _,
    fun b hb => (Finset.mem_filter.mp hb).2, ?_⟩
  refine le_trans hk (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨b, hbs, hab, hPb⟩ := h v hv
  exact Finset.mem_image.mpr ⟨b, Finset.mem_filter.mpr ⟨hbs, hPb⟩, hab⟩

/-- With no rival included anywhere, every correct block that includes a
valid transaction is a fast vote for it: `⊥` would need a visible
conflict, and the sole-candidate rule adopts. -/
theorem fast_vote_of_sole (hrule : VotingRule U) {tx : Tx}
    (hval : T.Valid tx)
    (hsole : ∀ tx', T.Valid tx' → Conflict tx tx' → ∀ b ∈ U.ids, ¬ Includes U b tx')
    {b₁ : BlockId} (hb₁ : b₁ ∈ U.ids)
    (hc₁ : (U.block b₁).author ∈ (Correct : Finset Validator))
    (hinc : Includes U b₁ tx) : IsFastVote U b₁ tx := by
  have hcand : IsCandidate U b₁ (T.input tx) tx := ⟨hval, rfl, hinc⟩
  have hsole' : ∀ tx', IsCandidate U b₁ (T.input tx) tx' → tx' = tx := by
    intro tx' h'
    by_contra hne
    exact hsole tx' h'.1 ⟨fun h => hne h.symm, h'.2.1.symm⟩ b₁ hb₁ h'.2.2
  have hnobot : ¬ StanceIs U (U.block b₁).author (T.input tx) b₁ (some Stance.bot) := by
    intro hbot
    obtain ⟨e, he, hae, hre, hde⟩ := exists_bot_declarer hbot
    obtain ⟨t₁, t₂, h₁, h₂, hne⟩ :=
      hrule.bot_conflicted e he (hae.symm ▸ hc₁) (T.input tx) hde
    rcases eq_or_ne t₁ tx with rfl | hne₁
    · exact hsole t₂ h₂.1 ⟨fun h => hne h, h₂.2.1.symm⟩ e he h₂.2.2
    · exact hsole t₁ h₁.1 ⟨fun h => hne₁ h.symm, h₁.2.1.symm⟩ e he h₁.2.2
  exact ⟨hval, hinc, hrule.ack_sole b₁ hb₁ hc₁ (T.input tx) tx hcand hsole' hnobot⟩

/-- A visible certificate behind a fast vote is a certificate at or
below the block. -/
theorem hasCert_of_certVisible_of_fastVote {b : BlockId} {tx : Tx} (hb : b ∈ U.ids)
    (hv : IsFastVote U b tx) (hcv : CertVisible U b tx) : HasCert U b tx := by
  rcases hcv with hq | ⟨p, hp, hcert⟩
  · exact ⟨b, hb, ⟨hv, hq⟩, Reaches.refl⟩
  · exact hasCert_mono (Reaches.single hp) hcert

/-- Readiness resolves at a least index. -/
theorem exists_resolvesAt_of_ready {A : Anchors U} {j : ℕ} {o : Obj}
    (h : ResolveReadyAt U A j o) : ∃ j' ≤ j, ResolvesAt U A j' o := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
      by_cases hbelow : ∃ k < j, ResolveReadyAt U A k o
      · obtain ⟨k, hk, hready⟩ := hbelow
        obtain ⟨j', hj', hres⟩ := ih k hk hready
        exact ⟨j', by omega, hres⟩
      · push Not at hbelow
        exact ⟨j, le_refl _, h, hbelow⟩

end RedSnapper

end LeanDag
