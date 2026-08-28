import LeanDag.Barnacle.Live.Statement
import LeanDag.Barnacle.Progress.Proof
import LeanDag.Barnacle.Mysticeti.Proof
import LeanDag.Barnacle.MysticetiLive.Proof
import LeanDag.Barnacle.Odontoceti.Proof
import LeanDag.Barnacle.Nemo.Proof

/-!
# BN11 — proof

Generated proof layer; not part of the audit surface. Each conjunct is
BN8b applied to BN10's liveness clause for the same rule, with the laws
from BN10's first conjunct.
-/

namespace LeanDag

namespace Barnacle

namespace Live

theorem holds : Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn F BlockId Payload _ P hk upd hbnd
    exact (Progress.holds (Fin n) BlockId Payload mysticetiLive
      (Mysticeti.holds (Fin n) BlockId Payload) P (roundRobin n hn) hk upd hbnd (n + 2)).2
      (fun m hm hmax => MysticetiLive.holds.2 n hn BlockId Payload _ hk m hm hmax)
  · intro n hn F BlockId Payload _ P hk upd hbnd
    exact (Progress.holds (Fin n) BlockId Payload odontocetiLive
      (Odontoceti.holds.1 (Fin n) BlockId Payload) P (roundRobin n hn) hk upd hbnd (n + 1)).2
      (fun m hm hmax => Odontoceti.holds.2.2 n hn BlockId Payload _ hk m hm hmax)
  · intro n hn F BlockId Payload _ P hk upd hbnd
    exact (Progress.holds (Fin n) BlockId Payload nemoLive
      (Nemo.holds.1 (Fin n) BlockId Payload) P (roundRobin n hn) hk upd hbnd (n + 1)).2
      (fun m hm hmax => Nemo.holds.2.2 n hn BlockId Payload _ hk m hm hmax)

end Live

end Barnacle

end LeanDag
