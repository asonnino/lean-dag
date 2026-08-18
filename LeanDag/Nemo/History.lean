import LeanDag.Nemo.CausalHistory

/-!
# Nemo-Nemo: causal history as a finite set

`Reaches` is a `Prop` and nothing can be counted in a `Prop`, so the history
is realised as a `Finset` via a round-indexed fuel. As with reachability,
none of this is crash-specific: the fuelled walk and its lemmas are proved
once in `Causality.lean` over the raw block data, and this file names the
result at the crash universe.

The three lemmas below are the ones the arc consumes. The rest of the layer
— the fuel lemmas, the one-step unfolding, the round bounds, the leaf cases
— is reached through `U.causal` when needed, rather than restated here.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : Universe Validator BlockId Payload}

/-- The causal history of `b`, as a `Finset`. -/
def history (U : Universe Validator BlockId Payload) (b : BlockId) : Finset BlockId :=
  historyFrom U.block b

/-- **The representation is faithful.** For a block of the universe,
membership of `history` and reachability are the same thing. -/
theorem mem_history_iff {b i : BlockId} (hb : b ∈ U.ids) :
    i ∈ history U b ↔ Reaches U b i :=
  U.causal.mem_history_iff hb

/-- Histories nest along reachability. -/
theorem history_subset_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    history U b ⊆ history U c :=
  U.causal.history_subset_of_reaches hc h

/-- A block's references lie in its history, one step down. -/
theorem mem_history_of_mem_refs {b j : BlockId} (hb : b ∈ U.ids) (hj : j ∈ (U.block b).refs) :
    j ∈ history U b :=
  U.causal.mem_history_of_mem_refs hb hj

end Nemo

end LeanDag
