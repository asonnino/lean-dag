import LeanDag.Steelhead.Ledger.Statement
/-!
# The ledger at any lawful rule — proof

Generated proof layer; not part of the audit surface. Every conjunct is
the anchored relation's own ledger theorem at the rule's laws, or a fact
of `Common/Ledger.lean` that reads no rule at all.
-/

namespace LeanDag

namespace Steelhead

namespace Ledger

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U R
  refine ⟨?_, ?_⟩
  · intro V₁ V₂ n g₁ g₂ hl h₁ h₂
    exact ⟨AnchoredRule.commitSeq_agree hl trivial h₁ h₂,
      AnchoredRule.ledgerSet_agree hl trivial h₁ h₂,
      fun _ hm => ledgerSet_mono hm,
      fun _ _ hk ho => AnchoredRule.outputAt_agree hl trivial h₁ h₂ hk ho,
      fun _ _ _ ho₁ ho₂ => outputAt_unique ho₁ ho₂⟩
  · intro V₁ V₂ k₁ k₂ L h₁ h₂
    exact AnchoredRule.slot_eq_of_decided_commit h₁ h₂

end Ledger

end Steelhead

end LeanDag
