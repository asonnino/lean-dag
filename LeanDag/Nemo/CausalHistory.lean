import LeanDag.Nemo.Basic
import LeanDag.Causality

/-!
# Nemo-Nemo: causal history

Reachability over the crash `Universe`. There is nothing crash-specific in
it: the walk needs only that references stay inside the population and that
a reference sits one round below, which is exactly `CausalStructure`, so
this file supplies that structure and reads `Causality.lean` at the crash
universe's data.

The Byzantine `BlockUniverse` does the same. Neither arc restates the walk.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : Universe Validator BlockId Payload}

/-- **The crash universe is a causal structure.** Completeness is a field;
the round condition is the predecessor clause of crash validity. -/
theorem Universe.causal (U : Universe Validator BlockId Payload) :
    CausalStructure U.block U.ids :=
  ⟨U.complete, fun _ hi _ hj => (U.valid _ hi).predecessor _ hj⟩

/-- `Reaches U c b` — `b` lies in the causal history of `c`. -/
def Reaches (U : Universe Validator BlockId Payload) : BlockId → BlockId → Prop :=
  ReachesFrom U.block

namespace Reaches

@[refl]
theorem refl {c : BlockId} : Reaches U c c := ReachesFrom.refl

theorem single {i j : BlockId} (h : j ∈ (U.block i).refs) : Reaches U i j :=
  ReachesFrom.single h

theorem trans {a b c : BlockId} (h₁ : Reaches U a b) (h₂ : Reaches U b c) : Reaches U a c :=
  ReachesFrom.trans h₁ h₂

theorem of_mem_refs {i j b : BlockId} (hij : j ∈ (U.block i).refs) (hjb : Reaches U j b) :
    Reaches U i b :=
  ReachesFrom.of_mem_refs hij hjb

end Reaches

/-- Causal history stays inside the universe. -/
theorem mem_ids_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) : b ∈ U.ids :=
  U.causal.mem_ids_of_reaches hc h

/-- Causal history runs downward in rounds. -/
theorem round_le_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    (U.block b).round ≤ (U.block c).round :=
  U.causal.round_le_of_reaches hc h

/-- A block cannot reach anything strictly above it. -/
theorem not_reaches_of_round_lt {c b : BlockId} (hc : c ∈ U.ids)
    (h : (U.block c).round < (U.block b).round) : ¬ Reaches U c b :=
  U.causal.not_reaches_of_round_lt hc h

/-- Causal history never escapes a view — the same closure argument, at a
view's holdings rather than the universe's population. -/
theorem View.mem_of_reaches {V : View Validator BlockId Payload U} {c b : BlockId}
    (hc : c ∈ V.ids) (h : Reaches U c b) : b ∈ V.ids :=
  mem_of_reaches_of_closed V.complete hc h

end Nemo

end LeanDag
