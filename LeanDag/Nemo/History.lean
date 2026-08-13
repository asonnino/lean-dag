import LeanDag.Nemo.CausalHistory
import Mathlib.Data.Finset.Union

/-!
# Nemo-Nemo: causal history as a finite set

A port of `LeanDag/History.lean` to the crash `Universe`. `Reaches` is a `Prop`
and nothing can be counted in a `Prop`, so the history is realised as a `Finset`
via a round-indexed fuel, exactly as in the core. Nothing here touches the
quorum, so the port is mechanical — the only additions are the two leaf lemmas
the core inherits from its `CausalHistory`/`Block` files
(`eq_of_reaches_of_refs_empty` and `refs = ∅` at round `0`), reproved locally
against the crash `Universe`.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : Universe Validator BlockId Payload}

omit [DecidableEq BlockId] in
/-- A block with no references reaches only itself — the crash port of the
core's `eq_of_reaches_of_refs_empty`. -/
theorem eq_of_reaches_of_refs_empty {c b : BlockId} (hc : (U.block c).refs = ∅)
    (h : Reaches U c b) : b = c := by
  rcases h.cases_head with heq | ⟨_, hstep, _⟩
  · exact heq.symm
  · simp [RefStep, hc] at hstep

omit [DecidableEq BlockId] in
/-- Genesis blocks have no references: at round `0` the predecessor equation
`round + 1 = 0` is unsatisfiable. -/
theorem refs_empty_of_round_zero {b : BlockId} (hb : b ∈ U.ids)
    (h0 : (U.block b).round = 0) : (U.block b).refs = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro i hi
  have := (U.valid b hb).predecessor i hi
  omega

/-- Everything reachable from `b` in at most `n` reference steps.

Structural in the fuel `n`, so it is computable and needs no decidability
hypothesis. Outside `U.ids` it still evaluates — to junk, like `U.block`
itself — and every statement below quantifies over ids of the universe. -/
def historyUpto (U : Universe Validator BlockId Payload) :
    ℕ → BlockId → Finset BlockId
  | 0, b => {b}
  | n + 1, b => insert b ((U.block b).refs.biUnion (historyUpto U n))

@[simp]
theorem historyUpto_zero (b : BlockId) : historyUpto U 0 b = {b} := rfl

theorem historyUpto_succ (n : ℕ) (b : BlockId) :
    historyUpto U (n + 1) b = insert b ((U.block b).refs.biUnion (historyUpto U n)) := rfl

theorem mem_historyUpto_succ {n : ℕ} {b i : BlockId} :
    i ∈ historyUpto U (n + 1) b ↔
      i = b ∨ ∃ j ∈ (U.block b).refs, i ∈ historyUpto U n j := by
  rw [historyUpto_succ, Finset.mem_insert, Finset.mem_biUnion]

theorem mem_historyUpto_self {n : ℕ} {b : BlockId} : b ∈ historyUpto U n b := by
  cases n with
  | zero => simp
  | succ n => exact mem_historyUpto_succ.mpr (Or.inl rfl)

/-- More fuel never loses anything. Needed because `mem_history_iff` fixes the
fuel at `round + 1` while the recursion hands out whatever is left. -/
theorem historyUpto_mono {m n : ℕ} (h : m ≤ n) (b : BlockId) :
    historyUpto U m b ⊆ historyUpto U n b := by
  induction n generalizing m b with
  | zero =>
      obtain rfl : m = 0 := Nat.le_zero.mp h
      exact Finset.Subset.refl _
  | succ n ih =>
      intro i hi
      rcases Nat.eq_zero_or_pos m with rfl | hm
      · rw [historyUpto_zero, Finset.mem_singleton] at hi
        exact hi ▸ mem_historyUpto_self
      · obtain ⟨m, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
        rcases mem_historyUpto_succ.mp hi with rfl | ⟨j, hj, hij⟩
        · exact mem_historyUpto_self
        · exact mem_historyUpto_succ.mpr (Or.inr ⟨j, hj, ih (by omega) j hij⟩)

/-- **Soundness.** Anything the fuelled search finds really is reachable. No
hypothesis on `b`: even off the universe, `historyUpto` only ever walks
references. -/
theorem reaches_of_mem_historyUpto {n : ℕ} {b i : BlockId}
    (h : i ∈ historyUpto U n b) : Reaches U b i := by
  induction n generalizing b with
  | zero =>
      rw [historyUpto_zero, Finset.mem_singleton] at h
      exact h ▸ Reaches.refl
  | succ n ih =>
      rcases mem_historyUpto_succ.mp h with rfl | ⟨j, hj, hij⟩
      · exact Reaches.refl
      · exact Reaches.of_mem_refs hj (ih hij)

/-- **Completeness**, with the fuel accounted for. A path from `b` drops the
round by one per step (T2), so `round b` steps exhaust it — and one more is
harmless by `historyUpto_mono`.

The base case is where the round bound does its work: at round `0` validity
forces `refs = ∅` (`refs_empty_of_round_zero`), so `b` reaches only itself. -/
theorem mem_historyUpto_of_reaches {n : ℕ} {b i : BlockId} (hb : b ∈ U.ids)
    (hn : (U.block b).round ≤ n) (h : Reaches U b i) : i ∈ historyUpto U n b := by
  induction n generalizing b with
  | zero =>
      have hrefs : (U.block b).refs = ∅ := refs_empty_of_round_zero hb (by omega)
      rw [eq_of_reaches_of_refs_empty hrefs h]
      simp
  | succ n ih =>
      rcases h.cases_head with rfl | ⟨j, hstep, hji⟩
      · exact mem_historyUpto_self
      · have hj_ids : j ∈ U.ids := U.complete b hb j hstep
        have hj_round := U.round_of_mem_refs hb hstep
        exact mem_historyUpto_succ.mpr (Or.inr ⟨j, hstep, ih hj_ids (by omega) hji⟩)

/-- The causal history of `b`, as a `Finset`. -/
def history (U : Universe Validator BlockId Payload) (b : BlockId) : Finset BlockId :=
  historyUpto U ((U.block b).round + 1) b

/-- **The representation is faithful.** For a block of the universe, membership
of `history` and reachability are the same thing. -/
theorem mem_history_iff {b i : BlockId} (hb : b ∈ U.ids) :
    i ∈ history U b ↔ Reaches U b i :=
  ⟨reaches_of_mem_historyUpto, mem_historyUpto_of_reaches hb (by omega)⟩

/-- A block lies in its own causal history. -/
@[simp]
theorem mem_history_self {b : BlockId} : b ∈ history U b := mem_historyUpto_self

/-- Histories stay inside the universe. -/
theorem history_subset_ids {b : BlockId} (hb : b ∈ U.ids) : history U b ⊆ U.ids :=
  fun _ hi => mem_ids_of_reaches hb ((mem_history_iff hb).mp hi)

/-- Histories nest along reachability — the `Finset` form of transitivity. -/
theorem history_subset_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    history U b ⊆ history U c := by
  have hb : b ∈ U.ids := mem_ids_of_reaches hc h
  intro i hi
  exact (mem_history_iff hc).mpr (h.trans ((mem_history_iff hb).mp hi))

/-- The one-step unfolding: a history is its block, plus the histories of its
references. -/
theorem mem_history_succ_iff {b : BlockId} (hb : b ∈ U.ids) {i : BlockId} :
    i ∈ history U b ↔ i = b ∨ ∃ j ∈ (U.block b).refs, i ∈ history U j := by
  rw [history, mem_historyUpto_succ]
  constructor
  · rintro (rfl | ⟨j, hj, hij⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨j, hj, ?_⟩
      rw [history, U.round_of_mem_refs hb hj]
      exact hij
  · rintro (rfl | ⟨j, hj, hij⟩)
    · exact Or.inl rfl
    · refine Or.inr ⟨j, hj, ?_⟩
      rw [history, U.round_of_mem_refs hb hj] at hij
      exact hij

/-- Causal history runs downward (T2), in the `Finset` form. -/
theorem round_le_of_mem_history {b i : BlockId} (hb : b ∈ U.ids) (hi : i ∈ history U b) :
    (U.block i).round ≤ (U.block b).round :=
  round_le_of_reaches hb ((mem_history_iff hb).mp hi)

/-- Nothing in a block's history sits at the block's own round except the block
itself: a reference step drops the round strictly. -/
theorem eq_of_mem_history_of_round_eq {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round = (U.block b).round) : i = b := by
  rcases (mem_history_succ_iff hb).mp hi with rfl | ⟨j, hj, hij⟩
  · rfl
  · exfalso
    have hj_ids : j ∈ U.ids := U.complete b hb j hj
    have h1 := U.round_of_mem_refs hb hj
    have h2 := round_le_of_reaches hj_ids ((mem_history_iff hj_ids).mp hij)
    omega

/-- **The layer one below is exactly the reference set.** Anything in `b`'s
history at round `round b - 1` is a direct reference of `b`. -/
theorem mem_refs_of_mem_history_of_round_succ {b i : BlockId} (hb : b ∈ U.ids)
    (hi : i ∈ history U b) (hround : (U.block i).round + 1 = (U.block b).round) :
    i ∈ (U.block b).refs := by
  rcases (mem_history_succ_iff hb).mp hi with rfl | ⟨j, hj, hij⟩
  · omega
  · have hj_ids : j ∈ U.ids := U.complete b hb j hj
    have h1 := U.round_of_mem_refs hb hj
    have h2 := round_le_of_reaches hj_ids ((mem_history_iff hj_ids).mp hij)
    have : i = j := eq_of_mem_history_of_round_eq hj_ids hij (by omega)
    exact this ▸ hj

/-- A block's references lie in its history, one step down. -/
theorem mem_history_of_mem_refs {b j : BlockId} (hb : b ∈ U.ids) (hj : j ∈ (U.block b).refs) :
    j ∈ history U b :=
  (mem_history_iff hb).mpr (Reaches.single hj)

end Nemo

end LeanDag
