import LeanDag.Barnacle.Nemo.Statement
import LeanDag.Barnacle.Helpers.NemoLive

/-!
# Barnacle over Nemo-Nemo — proof

Generated proof layer; not part of the audit surface. The laws and
descent laws are the helpers; round-robin liveness is BN9e at the
majority slack and wave length `2`, whose bound holds at every `n`.
-/

namespace LeanDag

namespace Barnacle

namespace Nemo

theorem holds : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Validator BlockId Payload _ _ _
    exact nemo_laws
  · intro Validator BlockId Payload _ _ _ _
    exact nemoLive_descent
  · intro n hn C BlockId Payload _ w hk m hm hmax
    have hbound : (nemoLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload)).waveLength * (Fintype.card (Fin n) - LeanDag.Nemo.majority (Fin n))
          + 1 ≤ n := by
      change 2 * (Fintype.card (Fin n) - LeanDag.Nemo.majority (Fin n)) + 1 ≤ n
      rw [Fintype.card_fin]
      exact majority_bound n hn
    exact liveOn_roundRobin hn _ nemoLive_descent (Nat.succ_pos 1) hbound hk m hm hmax

end Nemo

end Barnacle

end LeanDag
