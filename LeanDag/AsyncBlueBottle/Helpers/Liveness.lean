import LeanDag.AsyncBlueBottle.Model.Unpredictable
import LeanDag.AsyncBlueBottle.Helpers.Counting
import LeanDag.AsyncBlueBottle.Helpers.Decision
import LeanDag.MahiMahi.Helpers.Liveness
/-!
# Helpers — the liveness layer

Generated lemma infrastructure for `Liveness/Statement.lean`; not part of
the audit surface. A good leader's commit on any view caught up to the
decision round; the core's descent from a committed run, transcribed;
the local route on the pacing structure with convergence read as
eventual delivery; and the congruences behind measurability, on
Mahi-Mahi's `AgreeUpto`.
-/

namespace LeanDag

namespace AsyncBlueBottle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

section Slots

variable [S : Slots Validator]

/-! ## A good leader commits -/

/-- **ABB9a.** A view caught up to the decision round holds every vote. -/
theorem decided_of_mem_good {k : ℕ} {V : View Validator BlockId Payload U}
    (h : S.leader k ∈ good U k)
    (hV : V.CoversUpto ((asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U V k (some L) := by
  unfold good at h
  rw [mem_goodAt] at h
  obtain ⟨L, hL, hLr, hLc, hcommit⟩ := h
  exact ⟨L, ⟨hL, hLr, hLc⟩,
    Decided.directCommit ⟨hL, hLr, hLc⟩ (directCommitIn_of_coversUpto hcommit hV)⟩

/-! ## The descent from a committed run -/

/-- **ABB9c.** The run form supplies the committed run; the descent does
the rest, each slot of the run committing on a view caught up to the
horizon. A spanning run has at least one slot. -/
theorem allDecidedBelow {c d N : ℕ} {V : View Validator BlockId Payload U}
    (hspan : (asyncBlueBottleAnchored Validator BlockId Payload).SpansEligible d)
    (hrun : UnpredictableRunWithin U c d N) (hV : V.CoversUpto N) (k : ℕ)
    (hk : (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound (k + c + d - 1) ≤ N) :
    ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, Decided U V i v := by
  obtain ⟨k', hk1, hk2, hgood⟩ := hrun k hk
  have hd : 1 ≤ d := by
    have := (asyncBlueBottleAnchored Validator BlockId Payload).lt_of_eligible
      (hspan 1 0 (by omega))
    omega
  refine ⟨k', hk1, AnchoredRule.decided_below_of_run (fun hi h => exists_least hi h) hd hspan
    (Led := fun j => S.leader j ∈ good U j) hgood fun j _ hj2 hj => ?_⟩
  have hcov :
      V.CoversUpto ((asyncBlueBottleAnchored Validator BlockId Payload).decisionRound j) := by
    intro b hb hbr
    refine hV b hb (le_trans hbr ?_)
    have := S.mono (show j ≤ k + c + d - 1 by omega)
    unfold AnchoredRule.decisionRound at hk ⊢
    simp only [asyncBlueBottleAnchored_waveAt] at hk ⊢
    omega
  obtain ⟨L, -, hdec⟩ := decided_of_mem_good hj hcov
  exact ⟨L, hdec⟩

/-! ## The local route -/

/-- **ABB9d.** The counting re-run inside the view: production gives every
reliable validator a decision-round block, the premise makes each a vote,
and eventual delivery puts each in the view. -/
theorem localCommit {T : Finset Validator} {N : ℕ} (pc : PaceCore U T N)
    (hcard : quorumCard Validator ≤ T.card) {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L)
    (hN : (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k ≤ N)
    (hvote : ∀ u ∈ T, ∀ q ∈ U.ids, (U.block q).creator = u →
      (U.block q).round = (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k →
      MahiMahi.Votes U q L) :
    ∀ v ∈ T, Decided U
      (pc.viewAt v
        (max (pc.latest ((asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k))
          pc.gst + pc.delay))
      k (some L) := by
  rw [asyncBlueBottleAnchored_decisionRound] at hN hvote ⊢
  have hpop := pc.populatedOn hcard _ hN
  intro v hv
  refine Decided.directCommit hL (le_trans hcard (Finset.card_le_card ?_))
  intro u hu
  obtain ⟨q, hq, hqc, hqr⟩ := hpop u hu
  exact mem_heldAuthors.mpr ⟨q, mem_voters.mpr ⟨hq, hqr, hvote u hu q hq hqc hqr⟩,
    pc.mem_viewAt (MahiMahi.holds_roundBlocks_eventually pc hN v hv q hq (hqc ▸ hu) hqr), hqc⟩

end Slots

/-! ## Measurability: agreement below a round -/

section Agree

variable {U₁ U₂ : BlockUniverse Validator BlockId Payload} {d : ℕ}

theorem AgreeUpto.voters_eq (h : MahiMahi.AgreeUpto U₁ U₂ d) {L : BlockId} {r : ℕ}
    (hd : r + 2 ≤ d) (hL : L ∈ U₁.ids) (hLr : (U₁.block L).round ≤ d) :
    voters U₁ L r = voters U₂ L r := by
  unfold voters decisionRoundAt
  rw [h.blocksAt_eq hd]
  apply Finset.filter_congr
  intro q hq
  obtain ⟨hq₂, hqr₂⟩ := mem_blocksAt.mp hq
  obtain ⟨hq₁, hqr₁⟩ := (h.ids q).mpr ⟨hq₂, by omega⟩
  exact h.votes_iff hq₁ hqr₁ hL hLr

theorem AgreeUpto.directCommit_iff (h : MahiMahi.AgreeUpto U₁ U₂ d) {L : BlockId} {r : ℕ}
    (hd : r + 2 ≤ d) (hL : L ∈ U₁.ids) (hLr : (U₁.block L).round ≤ d) :
    DirectCommit U₁ L r ↔ DirectCommit U₂ L r := by
  unfold DirectCommit supporters
  rw [AgreeUpto.voters_eq h hd hL hLr, h.creatorsOf_eq]
  intro q hq
  obtain ⟨hq₂, hqr₂, -⟩ := mem_voters.mp hq
  exact (h.ids q).mpr ⟨hq₂, by omega⟩

theorem AgreeUpto.goodAt_subset (h : MahiMahi.AgreeUpto U₁ U₂ d) {r : ℕ} (hd : r + 2 ≤ d) :
    goodAt U₁ r ⊆ goodAt U₂ r := by
  intro v hv
  rw [mem_goodAt] at hv ⊢
  obtain ⟨L, hL, hLr, hLc, hcommit⟩ := hv
  obtain ⟨hL₂, -⟩ := (h.ids L).mp ⟨hL, by omega⟩
  have hb := h.block L hL (by omega)
  refine ⟨L, hL₂, by rw [← hb]; exact hLr, by rw [← hb]; exact hLc, ?_⟩
  exact (AgreeUpto.directCommit_iff h hd hL (by omega)).mp hcommit

/-- **ABB9e.** -/
theorem AgreeUpto.goodAt_eq (h : MahiMahi.AgreeUpto U₁ U₂ d) {r : ℕ} (hd : r + 2 ≤ d) :
    goodAt U₁ r = goodAt U₂ r :=
  Finset.Subset.antisymm (AgreeUpto.goodAt_subset h hd) (AgreeUpto.goodAt_subset h.symm hd)

end Agree

end AsyncBlueBottle

end LeanDag
