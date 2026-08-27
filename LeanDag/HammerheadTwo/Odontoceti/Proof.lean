import LeanDag.HammerheadTwo.Odontoceti.Statement
import LeanDag.HammerheadTwo.Helpers.Odontoceti

/-!
# Hammerhead 2.0 over Odontoceti — proof

Generated proof layer; not part of the audit surface. The laws and
descent laws are the helpers; round-robin liveness is HH9e at slack
`f` and wave length `2`, with `2f + 1 ≤ n` from the committee bound.
-/

namespace LeanDag

namespace HammerheadTwo

namespace Odontoceti

theorem holds : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Validator BlockId Payload _ _ _ _
    exact odontoceti_laws
  · intro Validator BlockId Payload _ _ F _
    exact odontocetiLive_descent
  · intro n hn F BlockId Payload _ w hk m hm hmax
    have hbound : (odontocetiLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload)).waveLength * F.f + 1 ≤ n := by
      have := F.card_validators
      rw [Fintype.card_fin] at this
      change 2 * F.f + 1 ≤ n
      omega
    exact liveOn_roundRobin hn _ odontocetiLive_descent (Nat.succ_pos 1) hbound hk m hm hmax

end Odontoceti

end HammerheadTwo

end LeanDag
