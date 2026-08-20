import LeanDag.MahiMahi.Liveness.Statement
import LeanDag.MahiMahi.Helpers.Liveness

/-!
# Liveness under the clause — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Liveness.lean`.
-/

namespace LeanDag

namespace MahiMahi

namespace Liveness

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U w
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k h
    exact decided_of_mem_good h
  · intro c N hclause k hk
    obtain ⟨k', hk1, hk2, hgood⟩ := hclause k hk
    exact ⟨k', hk1, hk2, decided_of_mem_good hgood⟩
  · intro c d N hw hspan hrun k hk
    exact allDecidedBelow hw hspan hrun k hk
  · intro T N pc hcard k L hL hN hcert
    exact localCommit pc hcard hL hN hcert
  · intro U₁ U₂ w r hw h
    exact h.goodAt_eq (by omega) (le_refl _)

end Liveness

end MahiMahi

end LeanDag
