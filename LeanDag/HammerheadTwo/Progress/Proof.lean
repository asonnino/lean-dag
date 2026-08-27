import LeanDag.HammerheadTwo.Progress.Statement
import LeanDag.HammerheadTwo.Helpers.Progress

/-!
# HH8 — proof

Generated proof layer; not part of the audit surface. HH8a is
`progress_exists` with the bound forgotten; HH8b is `everyHeight_bound`,
the induction on the height that carries `start K ≤ K · (interval + 1 + c)`.
-/

namespace LeanDag

namespace HammerheadTwo

namespace Progress

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R hR P getLeader hk upd hupd c
  refine ⟨?_, ?_⟩
  · intro U Rnd N K Rn hlive hgood hRnd hN
    exact progress hR hupd Rn hlive hgood hRnd hN
  · intro hlive U Rnd N hgood hRnd K hK
    exact everyHeight hR hupd hlive hgood hRnd K hK

end Progress

end HammerheadTwo

end LeanDag
