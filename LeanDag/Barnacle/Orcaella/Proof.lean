import LeanDag.Barnacle.Orcaella.Statement
import LeanDag.Barnacle.Helpers.Orcaella

/-!
# Barnacle over Orcaella — proof

Generated proof layer; not part of the audit surface. The laws and
descent laws are the helpers; round-robin liveness is BN9e at slack
`fb + fc` and wave length `2`, with `2·(fb + fc) + 1 ≤ n` from the
committee bound, itself read off the admissible threshold.
-/

namespace LeanDag

namespace Barnacle

namespace Orcaella

theorem holds : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro Validator BlockId Payload _ _ _ _ k hk
    exact orcaella_laws hk
  · intro Validator BlockId Payload _ _ H _ k _
    exact orcaellaLive_descent
  · intro n hn H BlockId Payload _ k hadm w hkey m hm hmax
    have hbound : (orcaellaLive (Validator := Fin n) (BlockId := BlockId)
        (Payload := Payload) k).waveLength * (H.fb + H.fc) + 1 ≤ n := by
      have hcommittee := Hybrid.committee_bound_of_admissible hadm
      rw [Fintype.card_fin] at hcommittee
      change 2 * (H.fb + H.fc) + 1 ≤ n
      omega
    exact liveOn_roundRobin hn _ orcaellaLive_descent (Nat.succ_pos 1) hbound hkey m hm hmax

end Orcaella

end Barnacle

end LeanDag
