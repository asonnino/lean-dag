import LeanDag.Barnacle.Progress.Statement
import LeanDag.Barnacle.Helpers.Progress

/-!
# BN8 — proof

Generated proof layer; not part of the audit surface. BN8a is
`progress_exists` with the bound forgotten; BN8b is `everyHeight_bound`,
the induction on the height that carries `start K ≤ K · (interval + 1 + c)`.
-/

namespace LeanDag

namespace Barnacle

namespace Progress

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R hR P getLeader hk upd hupd c
  refine ⟨?_, ?_⟩
  · intro U V Rnd N K hcov Rn hlive hgood hRnd hN
    exact progress hR hupd hcov Rn hlive hgood hRnd hN
  · intro hlive U V Rnd N hgood hcov hRnd K hK
    exact everyHeight hR hupd hlive hcov hgood hRnd K hK

end Progress

end Barnacle

end LeanDag
