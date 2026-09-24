import LeanDag.Steelhead.Coin.Statement
import LeanDag.Steelhead.Helpers.Coin
/-!
# The coin at any pair of rules — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Coin.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Coin

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ U R p good Pop floor wa I K _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro T r hgf hpop
    exact floor_le_commitProb hgf hpop
  · exact ⟨byzantine_prob_eq, byzantine_prob_le⟩
  · intro T r₀ m hgf hpop
    exact runProb_ge hgf hpop
  · intro S' coin V i r hgc hr hlead h hV
    exact chainCommit_of_mem_good hgc hr hlead h hV
  · intro T r₀ m hgf hpop
    exact noCommitProb_le hgf hpop
  · exact fun hpos => tail_tendsto_zero hpos
  · intro M c H G hna hc
    exact no_good_block_prob_le_adaptive H G hna hc
  · intro T upd k₀ known d q s M hp hgc hgf hws hwa hKI hwaI hq h₁ h₀ hK hupd hpop
    exact undecidedProb_le hp hgc hgf hws hwa hKI hwaI hq h₀ hK hupd h₁ hpop
  · intro upd k₀ known d q s M σ G hp hgc hws hwa hKI hwaI hq h₁ h₀ hK hupd hσ hc
    exact undecidedProb_le_adaptive hp hgc hws hwa hKI hwaI hq h₀ hK hupd h₁ hσ hc
  · exact fun hpos => undecided_tail_tendsto_zero hpos
  · intro _ _ U T upd k₀ known q s hp hgc hgf hpos hws hwa hKI hwaI hq h₁ h₀ hK hupd hpop
    exact decidedAlmostSurely hp hgc hgf hpos hws hwa hKI hwaI hq h₀ hK hupd h₁ hpop
  · intro _ _ σ G upd k₀ known q s hp hgc hpos hws hwa hKI hwaI hq h₁ h₀ hK hupd hσ hc
    exact decidedAlmostSurely_adaptive hp hgc hpos hws hwa hKI hwaI hq h₀ hK hupd h₁ hσ hc
  · intro T V d s b M hsll hall hgc hgf hwa hs hpop hV
    exact undecidedAtPeriodOne_le hsll hall hgc hgf hwa hs hpop hV
  · intro T V d s b M hsll hall hgc hgf hfl hwa hs hpop
    exact ⟨expected_firstGoodBlock_le hgf hfl hpop,
      fun g hM hV => decided_of_firstGoodBlock hsll hall hgc hwa hs hM hV⟩
  · intro T c ρ hgf hpop
    exact noCommitProbOn_le hgf hpop
  · intro T M c ρ hgf hpop
    exact expected_firstGoodInterval_le hgf hpop
  · intro _ _ U T upd k₀ known q hp hgc hgf hpos hws hwa hKI hwaI hq h₀ hK hupd hpop
    exact allDecidedAlmostSurely hp hgc hgf hpos hws hwa hKI hwaI hq h₀ hK hupd hpop
  · intro _ _ U T upd k₀ known q s hp hgc hgf hpos hws hwa hKI hwaI hq h₁ h₀ hK hupd hpop
    exact anchoredAlmostSurely hp hgc hgf hpos hws hwa hKI hwaI hq h₀ hK hupd h₁ hpop
  · intro coin known upd k₀ V hp
    exact ⟨_, matchingPer_matches hp.async_laws (steelheadAt_laws hp.sync_laws hp.async_laws)
      (viewLaws_steelheadAt hp)⟩

end Coin

end Steelhead

end LeanDag
