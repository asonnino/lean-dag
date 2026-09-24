import LeanDag.Steelhead.BlueBottlePair.Replay.Statement
import LeanDag.Steelhead.Helpers.BlueBottlePair.Replay
/-!
# The `5f + 1` pair's replay — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/BlueBottlePair/Replay.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Replay

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ U I
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A I r w a
    exact ⟨certified_of_commits A I r w a, not_certified_of_skips A I r w a⟩
  · intro A hA T r hT hcard hr hpop1 hpop2
    exact window_count hA hT hcard hr hpop1 hpop2
  · intro A I r w a h
    exact commits_sound h
  · intro C candidates epsilon K k A hc h1 hk
    exact anchorUpdate_range C candidates epsilon A hc h1 hk
  · intro A hA r hr
    exact commitWeight_eq_commitProb hA hr
  · intro C epsilon e K k A hK
    subst hK
    exact ⟨fun c hc => Steelhead.Replay.candidatesUpto_dvd hc,
      fun hk => anchorUpdate_dvd C epsilon A hk⟩

end Replay

end BlueBottlePair

end Steelhead

end LeanDag
