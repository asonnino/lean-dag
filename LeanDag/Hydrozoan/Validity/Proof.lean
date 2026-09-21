import LeanDag.Hydrozoan.Validity.Statement
import LeanDag.Hydrozoan.Helpers.Validity
import LeanDag.Hydrozoan.SlotAgreement.Proof
import LeanDag.Hydrozoan.EventualDecision.Proof
/-!
# Validity — proof

Generated proof layer; not part of the audit surface.
-/

namespace LeanDag

namespace Hydrozoan

namespace Validity

open LeanDag.Hydrozoan.PrefixAgreement (DecidesBelow)
open LeanDag.Hydrozoan.Delivery (delivered authorRound)

variable {Replica BlockId : Type} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica]

/-- The slot's leader block is committed on the full view, and reaches
`x`: direct liveness, then synchrony down to `x`'s round. -/
theorem commit_reaches (U : BlockUniverse Replica BlockId) {T : Finset Replica} {R k : ℕ}
    {x : BlockId} (hT : T ⊆ (Correct : Finset Replica)) (hcard : q Replica ≤ T.card)
    (hsync : SynchronisedOn U T R) (hlead : S.leader k ∈ T) (hx : x ∈ U.ids)
    (hxc : (U.block x).creator ∈ T) (hR : R ≤ (U.block x).round)
    (hlt : (U.block x).round < S.slotRound k)
    (hpop : ∀ r, (U.block x).round < r → r ≤ S.slotRound k + 2 → PopulatedOn U T r) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) ∧ Reaches U L x := by
  obtain ⟨L, hL, -, hdec⟩ :=
    DirectLiveness.holds Replica BlockId U T R k hT hcard hsync (by omega)
      (hpop _ hlt (by omega)) (hpop _ (by omega) (by omega)) (hpop _ (by omega) (by omega))
      hlead (View.full U) (View.coversUpto_full U _)
  refine ⟨L, hL, hdec, ?_⟩
  exact reaches_of_synchronisedOn hsync ⟨_, hlead⟩ hx hxc hR hL.1 (hL.2.2 ▸ hlead)
    (hL.2.1 ▸ hlt) (fun r h1 h2 => hpop r h1 (by rw [hL.2.1] at h2; omega))

theorem runDelivers (U : BlockUniverse Replica BlockId) : RunDelivers U := by
  intro T R k x hT hcard hsync hlead hx hxc hR hlt hpop κ _ key lin hlin V g n hkn hdec
  obtain ⟨L, hL, hdecL, hreach⟩ := commit_reaches U hT hcard hsync hlead hx hxc hR hlt hpop
  have hg : g k = some L :=
    SlotAgreement.holds Replica BlockId U V (View.full U) k (g k) (some L) (hdec k hkn) hdecL
  exact key_delivered_of_commit key hkn hg (hlin L hL.1 x hreach)

theorem deliversBlock (U : BlockUniverse Replica BlockId) : DeliversBlock U := by
  intro T R k x hT hcard hsync hlead hx hxc hR hlt hpop lin hlin hwithin V g n hkn hdec
  obtain ⟨c, hc, hkey⟩ := runDelivers U T R k x hT hcard hsync hlead hx hxc hR hlt hpop _
    (authorRound U.block) lin hlin V g n hkn hdec
  obtain ⟨j, hj, L', hgj, hcL⟩ := exists_commit_of_mem_ledger
    ((Delivery.faithful _ (authorRound U.block) lin g n).1.subset hc)
  have hL' : L' ∈ U.ids := (AnchoredRule.isLeaderBlock_of_decided (hgj ▸ hdec j hj)).1
  have hcx : c = x := eq_of_authorRound_eq hx (hwithin L' hL' c hcL)
    (correct_subset_nonByzantine (hT hxc)) hkey
  exact hcx ▸ hc

theorem holds : Statement := by
  intro Replica BlockId _ _ _ _ _ _ U
  exact ⟨runDelivers U, deliversBlock U⟩

/-- **Every correct block is eventually delivered** (the composed
corollary): under a fair schedule, for every round bound `ρ` there is a
slot `b` such that, in any universe in which `T` is synchronised from `R`
and fills the rounds from `R` to the run's last decision round, any view
caught up to that round has a verdict assignment decided through `b`,
and every such assignment delivers every `T`-block of rounds `R` to
`ρ`. -/
theorem validityProgress :
    ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
      [DecidableEq BlockId] [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica]
      [S : Slots Replica],
    ∀ (T : Finset Replica) (R ρ c : ℕ),
      T ⊆ (Correct : Finset Replica) → q Replica ≤ T.card →
      0 < c → (hydrozoanAnchored Replica BlockId).SpansEligible c →
      FairRunOn T c →
      ∃ b, ρ < S.slotRound b ∧
        ∀ (U : BlockUniverse Replica BlockId),
          SynchronisedOn U T R →
          (∀ r, R ≤ r → r ≤ S.slotRound (b + c - 1) + 2 → PopulatedOn U T r) →
          ∀ V : View U, V.CoversUpto (S.slotRound (b + c - 1) + 2) →
          (∃ g, DecidesBelow U V g (b + 1)) ∧
            ∀ g, DecidesBelow U V g (b + 1) →
            ∀ x ∈ U.ids, (U.block x).creator ∈ T →
              R ≤ (U.block x).round → (U.block x).round ≤ ρ →
            ∀ lin, ListsHistory U lin → ListsWithin U lin →
              x ∈ delivered (authorRound U.block) lin g (b + 1) := by
  intro Replica BlockId _ _ _ _ _ S T R ρ c hT hcard hc hspan hfair
  obtain ⟨b, -, hRb, hlead⟩ := EventualDecision.runsRecur Replica T c 0 (max R (ρ + 1)) hfair
  have hRb' : R ≤ S.slotRound b := le_trans (le_max_left _ _) hRb
  have hρb : ρ < S.slotRound b := lt_of_lt_of_le (by omega) (le_trans (le_max_right _ _) hRb)
  have hmono : S.slotRound b ≤ S.slotRound (b + c - 1) := S.mono (by omega)
  refine ⟨b, hρb, fun U hsync hpop V hcov => ⟨?_, ?_⟩⟩
  · have hbelow := EventualDecision.runDecidesBelow U T R b c hT hcard hsync hc hspan hRb' hlead
      (fun r h1 h2 => hpop r (by omega) h2) V hcov
    obtain ⟨L, -, -, hdecb⟩ :=
      DirectLiveness.holds Replica BlockId U T R b hT hcard hsync hRb'
        (hpop _ hRb' (by omega)) (hpop _ (by omega) (by omega)) (hpop _ (by omega) (by omega))
        (by simpa using hlead 0 hc) V (hcov.mono (by omega))
    have hall : ∀ i, i < b + 1 → ∃ v, Decided U V i v := fun i hi => by
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with h | rfl
      · exact hbelow i h
      · exact ⟨some L, hdecb⟩
    classical
    exact ⟨fun i => if h : i < b + 1 then (hall i h).choose else none,
      fun i hi => by simpa [hi] using (hall i hi).choose_spec⟩
  · intro g hdec x hx hxc hRx hxρ lin hlin hwithin
    exact deliversBlock U T R b x hT hcard hsync (by simpa using hlead 0 hc) hx hxc hRx
      (by omega) (fun r h1 h2 => hpop r (by omega) (by omega)) lin hlin hwithin V g (b + 1)
      (by omega) hdec

end Validity

end Hydrozoan

end LeanDag
