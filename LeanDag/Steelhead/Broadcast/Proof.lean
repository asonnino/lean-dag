import LeanDag.Steelhead.Broadcast.Statement
import LeanDag.Steelhead.Helpers.Broadcast
import LeanDag.MahiMahi.Helpers.Synchrony
/-!
# Atomic broadcast at any lawful rule — proof

Generated proof layer; not part of the audit surface. Every conjunct is
a ledger theorem at the rule's laws, a fact of `Common/Ledger.lean`, or
the propagation of a reliable block through the DAG, which reads no rule:
Mahi-Mahi's `reaches_of_synchronisedOn` under synchrony and
`reaches_of_eventualReference` under the reference rule.
-/

namespace LeanDag

namespace Steelhead

namespace Broadcast

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U R
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro V₁ V₂ n m g₁ g₂ b hl h₁ h₂ hnm hb
    exact ledgerSet_mono hnm
      (AnchoredRule.ledgerSet_agree hl trivial h₁ (fun k hk => h₂ k (by omega)) ▸ hb)
  · intro V n g b k₁ k₂ h
    refine ⟨fun hb => ?_, fun h₁ h₂ => outputAt_unique h₁ h₂⟩
    obtain ⟨k, hk, L, hL, hr⟩ := hb
    exact mem_ids_of_reaches (AnchoredRule.isLeaderBlock_of_decided (hL ▸ h k hk)).1 hr
  · intro T V n k r g b L h hk hg hT hcard hs hpop hb hbr hbT hkr
    have hL := AnchoredRule.isLeaderBlock_of_decided (hg ▸ h k hk)
    exact ledgerSet_mono (by omega) (mem_ledgerSet_of_some hg
      (MahiMahi.reaches_of_synchronisedOn hT hcard hs le_rfl hpop hb hbr hbT L hL.1
        (by rw [hL.2.1]; exact hkr)))
  · intro T V n k ρ g b L h hk hg hT hcard href hpop hkr
    have hL := AnchoredRule.isLeaderBlock_of_decided (hg ▸ h k hk)
    exact ledgerSet_mono (by omega) (mem_ledgerSet_of_some hg
      (reaches_of_eventualReference hT hcard href hpop L hL.1 (by rw [hL.2.1]; exact hkr)))
  · intro V₁ V₂ n g₁ g₂ b b' k k' hl h₁ h₂ ho ho' hkk hk'
    exact ⟨AnchoredRule.outputAt_agree hl trivial h₁ h₂ (by omega) ho,
      AnchoredRule.outputAt_agree hl trivial h₁ h₂ hk' ho'⟩

end Broadcast

end Steelhead

end LeanDag
