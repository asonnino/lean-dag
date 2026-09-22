import LeanDag.AsyncBlueBottle.Liveness.Statement
import LeanDag.AsyncBlueBottle.Helpers.Liveness
/-!
# Liveness under the clause — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Liveness.lean`.
-/

namespace LeanDag

namespace AsyncBlueBottle

namespace Liveness

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k V h hV
    exact decided_of_mem_good h hV
  · intro c N V hclause hV k hk
    obtain ⟨k', hk1, hk2, hgood⟩ := hclause k hk
    refine ⟨k', hk1, hk2, decided_of_mem_good hgood ?_⟩
    intro b hb hbr
    refine hV b hb (le_trans hbr ?_)
    have := S.mono (show k' ≤ k + c by omega)
    unfold AnchoredRule.decisionRound at hk ⊢
    simp only [asyncBlueBottleAnchored_waveAt] at hk ⊢
    omega
  · intro c d N V hspan hrun hV k hk
    exact allDecidedBelow hspan hrun hV k hk
  · intro T N pc hcard k L hL hN hvote
    exact localCommit pc hcard hL hN hvote
  · intro U₁ U₂ r h
    exact AgreeUpto.goodAt_eq h le_rfl

end Liveness

end AsyncBlueBottle

end LeanDag
