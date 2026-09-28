import LeanDag.Steelhead.BlueBottlePair.Liveness.Statement
import LeanDag.Steelhead.Helpers.BlueBottlePair.Liveness
/-!
# The `5f + 1` pair's liveness — proof

Generated proof layer; not part of the audit surface. Each conjunct is a
helper of `Helpers/BlueBottlePair/Liveness.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Liveness

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U
  refine ⟨commitsUnderSync_pair U, skipsSilent_pair U, ?_, ?_, pairDecides U, ?_, ?_, ?_, ?_⟩
  · intro T V k L q hk hcard hL huniq hq hqr hqT hqL hs hpop hV
    exact commitsOfDisseminationAsync hk hcard hL huniq hq hqr hqT hqL hs hpop hV
  · intro T V N R k w waits rs hT hcard hgst hto hR hwait hN hV hlead
    exact reactiveCommits rs hT hcard hgst hto hR hwait hN hV hlead
  · intro S' V c N hmono hrun hV k hk
    exact chainAllDecidedBelow hmono hrun hV k hk
  · intro S' T hT hcard hmono fair R k
    exact chainAllDecidedBelowOfSynchrony hmono hT hcard fair R k
  · intro coin V b hgood hV
    exact chainAllDecidedBelowOfRun hgood hV
  · intro V c N hid hone hrun hV r hr
    exact allDecidedBelowAtPeriodOne hid hone hrun hV r hr

end Liveness

end BlueBottlePair

end Steelhead

end LeanDag
