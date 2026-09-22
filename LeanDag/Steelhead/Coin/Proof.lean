import LeanDag.Steelhead.Coin.Statement
import LeanDag.Steelhead.Helpers.Coin
/-!
# The coin — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Coin.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Coin

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ U ws wa I K _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · intro T r hwa hcard hpop₃ hpopd
    exact ⟨ratio_le_commitProb hwa hcard hpop₃ hpopd, third_le_commitProb hwa hcard hpop₃ hpopd⟩
  · intro T r hwa hcard hpop₂ hpopd
    exact inv_card_le_commitProb hwa hcard hpop₂ hpopd
  · exact ⟨byzantine_prob_eq, byzantine_prob_le⟩
  · intro T r₀ m hwa hcard hpop
    exact runProb_ge hwa hcard hpop
  · intro S' coin V i r hr hlead h hV
    exact chainCommit_of_mem_goodAt hr hlead h hV
  · intro T r₀ m hwa hcard hpop
    exact noCommitProb_le hwa hcard hpop
  · exact tail_tendsto_zero
  · intro M c H G hna hc
    exact no_good_block_prob_le_adaptive H G hna hc
  · intro T upd k₀ known d q s M hws hle hwa hKI hwaI hq hcard h₁ h₀ hK hupd hpop
    exact undecidedProb_le hws hle hwa hKI hwaI hq hcard h₀ hK hupd h₁ hpop
  · intro upd k₀ known d q s M σ G hws hle hwa hKI hwaI hq h₁ h₀ hK hupd hσ hc
    exact undecidedProb_le_adaptive hws hle hwa hKI hwaI hq h₀ hK hupd h₁ hσ hc
  · exact undecided_tail_tendsto_zero
  · intro T upd k₀ known d q s M hws hle hwa hKI hwaI hq hcard h₁ h₀ hK hupd hpop
    exact undecidedProb_le_four hws hle hwa hKI hwaI hq hcard h₀ hK hupd h₁ hpop
  · exact undecided_tail_four_tendsto_zero
  · intro _ _ U T upd k₀ known q s hws hle hwa hKI hwaI hq hcard h₁ h₀ hK hupd hpop
    exact decidedAlmostSurely hws hle hwa hKI hwaI hq hcard h₀ hK hupd h₁ hpop
  · intro _ _ σ G upd k₀ known q s hws hle hwa hKI hwaI hq h₁ h₀ hK hupd hσ hc
    exact decidedAlmostSurely_adaptive hws hle hwa hKI hwaI hq h₀ hK hupd h₁ hσ hc
  · intro T V d s b M hwa hcard hs hpop hV
    exact undecidedAtPeriodOne_le hwa hcard hs hpop hV
  · intro T V d s b M hwa hcard hs hpop
    exact ⟨expected_firstGoodBlock_le hwa hcard hpop,
      fun g hM hV => decided_of_firstGoodBlock (by omega) hs hM hV⟩
  · intro T V d s b M hwa hcard hs hpop
    exact ⟨expected_firstGoodBlock_le_four hwa hcard hpop,
      fun g hM hV => decided_of_firstGoodBlock (by omega) hs hM hV⟩
  · intro T c ρ hwa hcard _ hpop
    exact noCommitProbOn_le hwa hcard hpop
  · intro T M c ρ hwa hcard _ hpop
    exact expected_firstGoodInterval_le hwa hcard hpop
  · intro _ _ U T upd k₀ known q hws hle hwa hKI hwaI hq hcard h₀ hK hupd hpop
    exact allDecidedAlmostSurely hws hle hwa hKI hwaI hq hcard h₀ hK hupd hpop
  · intro _ _ U T upd k₀ known q s hws hle hwa hKI hwaI hq hcard h₁ h₀ hK hupd hpop
    exact anchoredAlmostSurely hws hle hwa hKI hwaI hq hcard h₀ hK hupd h₁ hpop
  · intro coin known upd k₀ V hws hwa
    exact ⟨_, matchingPer_matches hws hwa⟩

end Coin

end Steelhead

end LeanDag
