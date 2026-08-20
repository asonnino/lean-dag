import LeanDag.MahiMahi.Model.Decision

/-!
# Mahi-Mahi — the committed candidates of a wave

`goodAt U w r` is the set of validators whose round-`r` block the DAG
directly commits at wave `w`; `good U w k` is the same at a slot's round.
A property of the DAG alone — no schedule, no network, no time — and the
object the liveness clause of `mahi-mahi.md` §5 is stated against: the
late-revealed leader is the one the adversary cannot aim at, and what
"cannot aim" amounts to on a DAG is that the leader keeps landing in
this set. The counting results of `mahi-mahi.md` §4 bound its size from
below with no network hypothesis.

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- The validators whose round-`r` block is directly committed at wave
`w`. Round-indexed and slot-free, so that the counting theorems mention
no schedule; decidable on a concrete universe, as a bounded search over
`U.ids` of decidable conjuncts. -/
def goodAt (U : BlockUniverse Validator BlockId Payload) (w r : ℕ) : Finset Validator :=
  Finset.univ.filter (fun v => ∃ L ∈ U.ids,
    (U.block L).round = r ∧ (U.block L).creator = v ∧ DirectCommit U w L r)

/-- The slot-`k` candidates the DAG directly commits: `goodAt` at the
slot's round. The schedule enters only through `slotRound`. -/
def good (U : BlockUniverse Validator BlockId Payload) [S : Slots Validator]
    (w k : ℕ) : Finset Validator :=
  goodAt U w (S.slotRound k)

end MahiMahi

end LeanDag
