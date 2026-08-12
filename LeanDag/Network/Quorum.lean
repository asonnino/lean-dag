import LeanDag.GC.Window
import LeanDag.DoS.Novelty

/-!
# The DoS capstones, bundling growth with the storage bound

The composed statements — DoS resistance in one theorem — with production
as the hypothesis every liveness result takes: `PopulatedOn`, discharged
by the `ViewPace` route (`ViewPace.populatedOn`, report §6.9) as
everywhere else in the development.

This file once carried the quorum route to production — N1
(`DeliversQuorum`) with the build rule (`Live`), yielding `Populated`
through L1 (`no_stall`). That route is deleted: production is derived
from genesis, view convergence and the pacemaker's progress rule, and no
result names a `Live` or a `DeliversQuorum` any more. What survives of
the file is the pairing the route was bundled with.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {D : Delivery U} {G N : ℕ}

/-- **The composed statement — DoS resistance in one theorem.** One set of
hypotheses — production, post-`R` delivery, the *enforceable* budget, and
the reference discipline — supports liveness and linear storage
**simultaneously**: no correct validator ever stalls, and no correct
validator's retained view grows faster than
`|Correct|·(f·κ+1) + f·κ` per round. The two conclusions do not compete:
liveness never needs a Byzantine block (D15b, and post-`R` the quorum is
derivable from the correct set alone,
`card_creators_accepted_of_eventuallyDelivers`), and by C3″ enforcing the
budget never defers a correct one. -/
theorem populated_and_card_viewUpto_le' {κ R N : ℕ}
    (hpop : ∀ r ≤ N, Populated U r)
    (hED : EventuallyDelivers D R)
    (hbyz : ByzBudget D κ) (hra : RefsAccepted D) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n, R + 1 ≤ n →
        (viewUpto D v n).card ≤ (viewUpto D v (R + 1)).card +
          (n - (R + 1)) *
            ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ) :=
  ⟨hpop, fun _v hv _n hn => card_viewUpto_le' hbyz hED hra hv hn⟩

/-- **The capstone, unconditional.** `EventuallyDelivers` is gone:
production plus the enforceable budget plus the reference discipline give
liveness and linear storage from round 0 — DoS resistance under full
asynchrony, in one theorem. -/
theorem populated_and_card_viewUpto_le {κ N : ℕ}
    (hpop : ∀ r ≤ N, Populated U r)
    (hbyz : ByzBudget D κ) (hra : RefsAccepted D) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto D v n).card ≤
          (Correct : Finset Validator).card * (n + 1) +
            ((Correct : Finset Validator).card * F.f +
              n * ((Correct : Finset Validator).card * (F.f * κ))) :=
  ⟨hpop, fun _v hv n => card_viewUpto_le hbyz hra hv n⟩

end LeanDag
