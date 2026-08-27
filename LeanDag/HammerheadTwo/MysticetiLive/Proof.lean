import LeanDag.HammerheadTwo.MysticetiLive.Statement
import LeanDag.HammerheadTwo.Helpers.MysticetiLive
import LeanDag.HammerheadTwo.Helpers.Heads

/-!
# Mysticeti liveness — proof

Generated proof layer; not part of the audit surface. The descent laws
are `mysticetiLive_descent`; round-robin liveness is HH9e at slack `f`
and wave length `3`, with `3f + 1 ≤ n` from `Faults.card_validators`.
-/

namespace LeanDag

namespace HammerheadTwo

namespace MysticetiLive

theorem holds : Statement := by
  refine ⟨?_, ?_⟩
  · intro Validator BlockId Payload _ _ F _
    exact mysticetiLive_descent
  · intro n hn F BlockId Payload _ w hk m hm hmax
    have hbound : (mysticetiLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload)).waveLength * F.f + 1 ≤ n := by
      have := F.card_validators
      rw [Fintype.card_fin] at this
      change 3 * F.f + 1 ≤ n
      omega
    exact liveOn_roundRobin hn _ mysticetiLive_descent (Nat.succ_pos 2) hbound hk m hm hmax

end MysticetiLive

end HammerheadTwo

end LeanDag
