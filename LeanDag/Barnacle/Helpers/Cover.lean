import LeanDag.Barnacle.Model.Rule

/-!
# Barnacle helpers — the full view is caught up

Not part of the audit surface. `CoversUpto U V N` asks that `V` hold
every block of `U` at a round up to `N`; the full view holds every block
of `U`, so it satisfies it at every `N`, which is what recovers the
whole-universe reading of every liveness result stated over a view.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : BaseRule Validator BlockId Payload}

/-- **The full view is caught up to every horizon.** -/
theorem coversUpto_full (hR : R.Laws) (U : R.Universe) (N : ℕ) :
    R.CoversUpto U (R.full U) N := by
  intro b hb _
  rw [hR.full_ids]
  exact hb

end Barnacle

end LeanDag
