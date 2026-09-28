import LeanDag.Steelhead.Replay.Statement
import LeanDag.Steelhead.Helpers.Replay
/-!
# The replay — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Replay.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Replay

theorem holds : Statement := by
  intro Validator _ _ _
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro candidates scores current epsilon hc
    exact select_mem candidates scores current epsilon hc
  · intro candidates scores current epsilon
    exact select_score_le candidates scores current epsilon
  · intro E C period r hws hwa hr
    exact bounded_timingAt (probeRate_fst_le E C period) hws hwa r hr
  · intro E C period r hws hlt hb hr hdec hcons
    exact async_term_bound hws hlt hb hr hdec hcons
  · intro E C candidates epsilon K k hc h1 hk
    exact update_range E C candidates epsilon hc h1 hk
  · intro E C canary period hcan hcop hp hws hwin
    exact probe_exists hcan hcop hp hws hwin
  · intro candidates scores current epsilon hc
    exact select_hysteresis candidates scores current epsilon hc
  · intro candidates scores current
    exact best_tie_rule candidates scores current
  · intro E C canary K period hcan hodd hmem hp hws hwin
    exact probe_exists_of_odd hcan hodd hmem hp hws hwin
  · intro E C epsilon e K k hK
    subst hK
    exact ⟨fun c hc => candidatesUpto_dvd hc, fun hk => update_dvd E C epsilon hk⟩

end Replay

end Steelhead

end LeanDag
