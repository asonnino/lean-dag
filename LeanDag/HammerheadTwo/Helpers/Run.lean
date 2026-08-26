import LeanDag.HammerheadTwo.Model.Run

/-!
# Run helpers

Lemma and conversion infrastructure for `Model/Run.lean`; not part of
the audit surface.
-/

namespace LeanDag

namespace HammerheadTwo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
variable {R : BaseRule Validator BlockId Payload} {P : Params}
variable {getLeader : ℕ → Validator} {hk : Keyed getLeader P.maxLeaders}
variable {upd : UpdateRule R} {U : R.Universe} {V : R.View U}

/-- A total run is partial at every height: through the anchor is within
through the anchor's round, since the anchor's round is `start (k + 1)`. -/
def ConfigRun.toPartial (Rn : ConfigRun R P getLeader hk upd U V) (K : ℕ) :
    PartialRun R P getLeader hk upd U V K where
  start := Rn.start
  count := Rn.count
  backoff := Rn.backoff
  anchor := Rn.anchor
  vdct := Rn.vdct
  init := Rn.init
  count_pos := Rn.count_pos
  count_le := Rn.count_le
  closed := fun k _ κ h₁ h₂ =>
    Rn.closed k κ h₁ (by rw [Rn.start_succ k]; exact Nat.div_le_div_right h₂)
  anchor_commits := fun k _ => Rn.anchor_commits k
  anchor_least := fun k _ => Rn.anchor_least k
  start_succ := fun k _ => Rn.start_succ k
  update := fun k _ => Rn.update k

end HammerheadTwo

end LeanDag
