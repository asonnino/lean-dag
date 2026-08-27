import LeanDag.FinWhale.Model.Rule
import Mathlib.Data.ZMod.Basic

/-!
# FinWhale — the schedule, and the block structure it works against

Two structural conditions, neither of which is a commit rule, and which
Theorem 26 consumes together.

`SelfParented` is the self-parent clause: every non-genesis block
references a block by its own author. The paper's block structure has it
and `ValidHere` omits it, so it is carried as a separate condition — one
a DoS-valid universe satisfies outright (`DoSBridge.lean`). It is what
makes a correct validator's blocks a chain.

`RoundRobin` is the leader schedule: the leader of round `r` is the
`r`-th validator of a fixed cyclic order, so the schedule is
`n`-periodic and each cycle names every validator once. It is what makes
a correct validator a leader, and what Lemma 22 counts over.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- **The self-parent clause**, which the paper's block structure has and
`ValidHere` omits. -/
def SelfParented (D : Dag Validator BlockId Payload) : Prop :=
  ∀ b ∈ D.ids, 0 < (D.block b).round →
    ∃ q ∈ (D.block b).refs, (D.block q).creator = (D.block b).creator

/-- **Round robin.** The leader of round `r` is the `r`-th validator of a
fixed cyclic order, so the schedule is `n`-periodic and each cycle names
every validator once. -/
def RoundRobin (leader : ℕ → Validator) : Prop :=
  ∃ e : ZMod (Fintype.card Validator) ≃ Validator,
    ∀ r : ℕ, leader r = e (r : ZMod (Fintype.card Validator))

end FinWhale

end LeanDag
