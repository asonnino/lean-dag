import LeanDag.Nemo.Basic
import Mathlib.Logic.Relation

/-!
# Nemo-Nemo: causal history

A verbatim port of `LeanDag/CausalHistory.lean` to the crash `Universe`. Nothing
here touches the quorum — `Reaches` needs only `block`/`complete`/the predecessor
condition — so the port is mechanical.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : Universe Validator BlockId Payload}

/-- One step of causal history: `j` is directly referenced by `i`. -/
def RefStep (U : Universe Validator BlockId Payload) (i j : BlockId) : Prop :=
  j ∈ (U.block i).refs

/-- `Reaches U c b` — `b` lies in the causal history of `c`. -/
def Reaches (U : Universe Validator BlockId Payload) : BlockId → BlockId → Prop :=
  Relation.ReflTransGen (RefStep U)

namespace Reaches

@[refl]
theorem refl {c : BlockId} : Reaches U c c := Relation.ReflTransGen.refl

theorem single {i j : BlockId} (h : j ∈ (U.block i).refs) : Reaches U i j :=
  Relation.ReflTransGen.single h

theorem trans {a b c : BlockId} (h₁ : Reaches U a b) (h₂ : Reaches U b c) : Reaches U a c :=
  Relation.ReflTransGen.trans h₁ h₂

theorem of_mem_refs {i j b : BlockId} (hij : j ∈ (U.block i).refs) (hjb : Reaches U j b) :
    Reaches U i b :=
  trans (single hij) hjb

end Reaches

/-- Causal history stays inside the universe. -/
theorem mem_ids_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) : b ∈ U.ids := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih => exact U.complete _ ih _ hstep

/-- Causal history runs downward in rounds. -/
theorem round_le_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    (U.block b).round ≤ (U.block c).round := by
  induction h with
  | refl => exact le_refl _
  | tail hab hstep ih =>
      have hmid := mem_ids_of_reaches hc hab
      have := U.round_of_mem_refs hmid hstep
      omega

/-- A block cannot reach anything strictly above it. -/
theorem not_reaches_of_round_lt {c b : BlockId} (hc : c ∈ U.ids)
    (h : (U.block c).round < (U.block b).round) : ¬ Reaches U c b := by
  intro hreach
  have := round_le_of_reaches hc hreach
  omega

/-- Causal history never escapes a view. -/
theorem View.mem_of_reaches {V : View Validator BlockId Payload U} {c b : BlockId}
    (hc : c ∈ V.ids) (h : Reaches U c b) : b ∈ V.ids := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih => exact V.complete _ ih _ hstep

end Nemo

end LeanDag
