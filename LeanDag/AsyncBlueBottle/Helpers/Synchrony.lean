import LeanDag.AsyncBlueBottle.Helpers.Counting
import LeanDag.AsyncBlueBottle.Helpers.Decision
import LeanDag.AsyncBlueBottle.Model.Unpredictable
import LeanDag.MahiMahi.Helpers.Synchrony
/-!
# Helpers — partial synchrony

Generated lemma infrastructure for `Synchrony/Statement.lean`; not part
of the audit surface. Coverage at one round places a reliable candidate
in every cone two rounds up — Mahi-Mahi's `reaches_of_synchronisedOn`,
which the wave length never enters — and the counting helpers turn that
into a direct commit.
-/

namespace LeanDag

namespace AsyncBlueBottle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

/-- **ABB10a.** -/
theorem good_of_synchronisedOn {T : Finset Validator} {R k : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k)) (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpopd : PopulatedOn U T ((asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k))
    (hlead : S.leader k ∈ T) : S.leader k ∈ good U k := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop0 (S.leader k) hlead
  rw [asyncBlueBottleAnchored_decisionRound] at hpopd
  unfold good
  rw [mem_goodAt]
  refine ⟨L, hL, hLr, hLc, ?_⟩
  refine directCommit_of_reach hcard hpopd hL (hT (hLc ▸ hlead)) ?_
  intro q hq hqr
  exact MahiMahi.reaches_of_synchronisedOn hT hcard hs hR hpop1 hL hLr (hLc ▸ hlead) q hq
    (by omega)

/-- **ABB10b.** -/
theorem unpredictableWithin_of_synchronisedOn {T : Finset Validator} {c N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T 0) (hpop : ∀ n, n ≤ N → PopulatedOn U T n)
    (fair : FairWithin T c) : UnpredictableWithin U c N := by
  intro k hk
  obtain ⟨k', hk1, hk2, hlead⟩ := fair k
  refine ⟨k', hk1, hk2, ?_⟩
  have hmono : S.slotRound k' ≤ S.slotRound (k + c) := S.mono (by omega)
  have hd : (asyncBlueBottleAnchored Validator BlockId Payload).decisionRound k' ≤ N := by
    unfold AnchoredRule.decisionRound at hk ⊢
    simp only [asyncBlueBottleAnchored_waveAt] at hk ⊢
    omega
  refine good_of_synchronisedOn hT hcard hs (Nat.zero_le _) ?_ ?_ (hpop _ hd) hlead
  · exact hpop _ (by
      unfold AnchoredRule.decisionRound at hd
      simp only [asyncBlueBottleAnchored_waveAt] at hd
      omega)
  · exact hpop _ (by
      unfold AnchoredRule.decisionRound at hd
      simp only [asyncBlueBottleAnchored_waveAt] at hd
      omega)

end AsyncBlueBottle

end LeanDag
