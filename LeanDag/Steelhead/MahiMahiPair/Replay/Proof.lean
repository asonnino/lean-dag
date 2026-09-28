import LeanDag.Steelhead.MahiMahiPair.Replay.Statement
import LeanDag.Steelhead.Helpers.MahiMahiPair.Replay
/-!
# The `3f + 1` pair's replay — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/MahiMahiPair/Replay.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

namespace Replay

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ U wa I
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A I r w a hw
    exact ⟨certified_of_commits U A I r w a, not_certified_of_skips U A I r w a hw⟩
  · intro A hA T r hwa hcard hr hpop3 hpopd
    exact window_count hA hwa hcard hr hpop3 hpopd
  · intro A I r w a h
    exact commits_sound h
  · intro C candidates epsilon K k A hc h1 hk
    exact anchorUpdate_range C candidates epsilon A hc h1 hk
  · intro A hA r hwa hr
    exact commitWeight_eq_commitProb hwa hA hr
  · intro C epsilon e K k A hK
    subst hK
    exact ⟨fun c hc => Steelhead.Replay.candidatesUpto_dvd hc,
      fun hk => anchorUpdate_dvd C epsilon A hk⟩

end Replay

end MahiMahiPair

end Steelhead

end LeanDag
