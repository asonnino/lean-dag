import LeanDag.Nemo.Basic
import LeanDag.Causality

/-!
# Nemo-Nemo: causal history

Reachability over the crash `Universe`. There is nothing crash-specific in
it: the walk needs only that references stay inside the population and that
a reference sits one round below, which is exactly `CausalStructure`, so
this file supplies that structure and names the walk at the crash universe's
data. The Byzantine `BlockUniverse` does the same; neither arc restates it.

Only what the arc consumes is restated here. Everything else `Causality.lean`
proves is reached through `U.causal` — `U.causal.round_le_of_reaches`,
`U.causal.mem_ids_of_reaches`, and the rest — without a wrapper standing
between the two.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : Universe Validator BlockId Payload}

/-- **The crash universe is a causal structure.** Completeness is a field;
the round condition is the predecessor clause of crash validity. This is the
arc's one bridge to the shared layer. -/
theorem Universe.causal (U : Universe Validator BlockId Payload) :
    CausalStructure U.block U.ids :=
  ⟨U.complete, fun _ hi _ hj => (U.valid _ hi).predecessor _ hj⟩

/-- `Reaches U c b` — `b` lies in the causal history of `c`. -/
def Reaches (U : Universe Validator BlockId Payload) : BlockId → BlockId → Prop :=
  ReachesFrom U.block

namespace Reaches

/-- A direct reference is one step of causal history. -/
theorem single {i j : BlockId} (h : j ∈ (U.block i).refs) : Reaches U i j :=
  ReachesFrom.single h

/-- Prepend a direct reference. -/
theorem of_mem_refs {i j b : BlockId} (hij : j ∈ (U.block i).refs) (hjb : Reaches U j b) :
    Reaches U i b :=
  ReachesFrom.of_mem_refs hij hjb

end Reaches

end Nemo

end LeanDag
