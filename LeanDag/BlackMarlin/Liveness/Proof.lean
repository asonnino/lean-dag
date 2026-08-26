import LeanDag.BlackMarlin.Helpers.Liveness

/-!
# Black Marlin — liveness, proved

Generated proof layer; not part of the audit surface. Each conjunct is
one helper: `committed_of_run` for BML1, `committedIn_full_iff` for BML2,
`mem_history_of_mem` for BML3, `recurrence` for BML4, and
`roundRobin_fairRun` for BML5.
-/

namespace LeanDag

namespace BlackMarlin

namespace Liveness

theorem holds : Statement := by
  refine ⟨?_, ?_⟩
  · intro Validator BlockId Payload _ _ _ _ _ U
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro T R r hcard hs hR hpop hpop1 hpop2 hlead hlead1
      exact committed_of_run hcard hs hR hpop hpop1 hpop2 hlead hlead1
    · intro L r
      exact committedIn_full_iff
    · intro T R ρ b c hcard hs hR hpop1 hb hbr hbc hc hcr
      exact mem_history_of_mem hcard hs hR hpop1 hb hbr hbc hc hcr
    · intro T R r hcard hfair
      exact recurrence hcard hfair
  · intro n hn _
    exact roundRobin_fairRun n hn

end Liveness

end BlackMarlin

end LeanDag
