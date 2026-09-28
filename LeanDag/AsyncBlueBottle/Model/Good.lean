import LeanDag.AsyncBlueBottle.Model.Decision
/-!
# Async BlueBottle — the committed candidates of a wave

`goodAt U r` is the set of validators whose round-`r` block the DAG
directly commits; `good U k` is the same at a slot's round. A property
of the DAG alone — no schedule, no network, no time — and the object the
liveness clause of `async-bluebottle.md` §5 is stated against, as in the
Mahi-Mahi arc: the coin-revealed leader is the one the adversary cannot
aim at, and what "cannot aim" amounts to on a DAG is that the leader
keeps landing in this set. The counting results of
`async-bluebottle.md` §5 bound its size from below with no network
hypothesis.

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace AsyncBlueBottle

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- The validators whose round-`r` block is directly committed.
Round-indexed and slot-free, so that the counting theorems mention no
schedule; decidable on a concrete universe, as a bounded search over
`U.ids` of decidable conjuncts. -/
def goodAt (U : BlockUniverse Validator BlockId Payload) (r : ℕ) : Finset Validator :=
  Finset.univ.filter (fun v => ∃ L ∈ U.ids,
    (U.block L).round = r ∧ (U.block L).creator = v ∧ DirectCommit U L r)

/-- The slot-`k` candidates the DAG directly commits: `goodAt` at the
slot's round. The schedule enters only through `slotRound`. -/
def good (U : BlockUniverse Validator BlockId Payload) [S : Slots Validator] (k : ℕ) :
    Finset Validator :=
  goodAt U (S.slotRound k)

end AsyncBlueBottle

end LeanDag
