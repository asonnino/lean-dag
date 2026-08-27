import LeanDag.HammerheadTwo.Heads.Statement
import LeanDag.HammerheadTwo.Helpers.Heads

/-!
# HH9 — proof

Generated proof layer; not part of the audit surface. Each clause is
one helper of `Helpers/Heads.lean`.
-/

namespace LeanDag

namespace HammerheadTwo

namespace Heads

theorem holds : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Validator BlockId Payload _ _ _ R slack getLeader w hk c₀
    refine ⟨?_, ?_, ?_⟩
    · intro hD S U V b top hspan hdec htop
      exact stretchDescent hD S V hspan hdec htop
    · intro hD hw U Rnd N T hT m hm hmax ρ hRnd hN hheads
      exact headsDecide_at getLeader hk m hm hmax hD hw hT ρ hRnd hN hheads
    · intro hD hw hheads m hm hmax
      exact liveOn_of_headsRun getLeader hk m hm hmax hD hw hheads
  · intro n hn T slack g hT hbound
    exact roundRobin_headsRun n hn T slack g hT hbound
  · intro n hn BlockId Payload _ R slack hD hw hbound w hk m hm hmax
    exact liveOn_roundRobin hn R hD hw hbound hk m hm hmax

end Heads

end HammerheadTwo

end LeanDag
