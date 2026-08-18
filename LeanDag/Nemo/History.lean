import LeanDag.Nemo.CausalHistory

/-!
# Nemo-Nemo: causal history as a finite set

`Reaches` is a `Prop` and nothing can be counted in a `Prop`, so the history
is realised as a `Finset` via a round-indexed fuel. As with reachability,
none of this is crash-specific: the fuelled walk and its lemmas live in
`Causality.lean` over the raw block data, and this file reads them at the
crash universe, keeping the names the arc uses.

The two leaf lemmas the port used to reprove — a block with no references
reaches only itself, and a round-`0` block has no references — are now the
structural layer's, the second *derived* there from the predecessor
condition rather than assumed.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : Universe Validator BlockId Payload}

omit [DecidableEq BlockId] in
/-- A block with no references reaches only itself. -/
theorem eq_of_reaches_of_refs_empty {c b : BlockId} (hc : (U.block c).refs = ∅)
    (h : Reaches U c b) : b = c :=
  _root_.LeanDag.eq_of_reaches_of_refs_empty hc h

omit [DecidableEq BlockId] in
/-- Genesis blocks have no references: at round `0` the predecessor equation
`round + 1 = 0` is unsatisfiable. -/
theorem refs_empty_of_round_zero {b : BlockId} (hb : b ∈ U.ids)
    (h0 : (U.block b).round = 0) : (U.block b).refs = ∅ :=
  U.causal.refs_empty_of_round_zero hb h0

/-- Everything reachable from `b` in at most `n` reference steps. -/
def historyUpto (U : Universe Validator BlockId Payload) :
    ℕ → BlockId → Finset BlockId :=
  historyUptoFrom U.block

@[simp]
theorem historyUpto_zero (b : BlockId) : historyUpto U 0 b = {b} := rfl

theorem historyUpto_succ (n : ℕ) (b : BlockId) :
    historyUpto U (n + 1) b = insert b ((U.block b).refs.biUnion (historyUpto U n)) := rfl

theorem mem_historyUpto_succ {n : ℕ} {b i : BlockId} :
    i ∈ historyUpto U (n + 1) b ↔
      i = b ∨ ∃ j ∈ (U.block b).refs, i ∈ historyUpto U n j :=
  mem_historyUptoFrom_succ

theorem mem_historyUpto_self {n : ℕ} {b : BlockId} : b ∈ historyUpto U n b :=
  mem_historyUptoFrom_self

/-- More fuel never loses anything. -/
theorem historyUpto_mono {m n : ℕ} (h : m ≤ n) (b : BlockId) :
    historyUpto U m b ⊆ historyUpto U n b :=
  historyUptoFrom_mono h b

/-- **Soundness.** Anything the fuelled search finds really is reachable. -/
theorem reaches_of_mem_historyUpto {n : ℕ} {b i : BlockId}
    (h : i ∈ historyUpto U n b) : Reaches U b i :=
  reaches_of_mem_historyUptoFrom h

/-- **Completeness**, with the fuel accounted for. -/
theorem mem_historyUpto_of_reaches {n : ℕ} {b i : BlockId} (hb : b ∈ U.ids)
    (hn : (U.block b).round ≤ n) (h : Reaches U b i) : i ∈ historyUpto U n b :=
  U.causal.mem_historyUpto_of_reaches hb hn h

/-- The causal history of `b`, as a `Finset`. -/
def history (U : Universe Validator BlockId Payload) (b : BlockId) : Finset BlockId :=
  historyFrom U.block b

/-- **The representation is faithful.** For a block of the universe,
membership of `history` and reachability are the same thing. -/
theorem mem_history_iff {b i : BlockId} (hb : b ∈ U.ids) :
    i ∈ history U b ↔ Reaches U b i :=
  U.causal.mem_history_iff hb

/-- A block lies in its own causal history. -/
@[simp]
theorem mem_history_self {b : BlockId} : b ∈ history U b := mem_historyFrom_self

/-- Histories stay inside the universe. -/
theorem history_subset_ids {b : BlockId} (hb : b ∈ U.ids) : history U b ⊆ U.ids :=
  U.causal.history_subset_ids hb

/-- Histories nest along reachability. -/
theorem history_subset_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    history U b ⊆ history U c :=
  U.causal.history_subset_of_reaches hc h

/-- The one-step unfolding: a history is its block, plus the histories of its
references. -/
theorem mem_history_succ_iff {b : BlockId} (hb : b ∈ U.ids) {i : BlockId} :
    i ∈ history U b ↔ i = b ∨ ∃ j ∈ (U.block b).refs, i ∈ history U j :=
  U.causal.mem_history_succ_iff hb

/-- Causal history runs downward, in the `Finset` form. -/
theorem round_le_of_mem_history {b i : BlockId} (hb : b ∈ U.ids) (hi : i ∈ history U b) :
    (U.block i).round ≤ (U.block b).round :=
  U.causal.round_le_of_mem_history hb hi

/-- Nothing in a block's history sits at the block's own round except the
block itself. -/
theorem eq_of_mem_history_of_round_eq {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round = (U.block b).round) : i = b :=
  U.causal.eq_of_mem_history_of_round_eq hb hi hround

/-- **The layer one below is exactly the reference set.** -/
theorem mem_refs_of_mem_history_of_round_succ {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round + 1 = (U.block b).round) :
    i ∈ (U.block b).refs :=
  U.causal.mem_refs_of_mem_history_of_round_succ hb hi hround

/-- A block's references lie in its history, one step down. -/
theorem mem_history_of_mem_refs {b j : BlockId} (hb : b ∈ U.ids) (hj : j ∈ (U.block b).refs) :
    j ∈ history U b :=
  U.causal.mem_history_of_mem_refs hb hj

end Nemo

end LeanDag
