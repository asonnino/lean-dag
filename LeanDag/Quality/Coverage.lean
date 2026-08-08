import LeanDag.DoS.Density
import LeanDag.Mysticeti

/-!
# Chain quality: asynchronous coverage

`chain-quality.md` §3, CQP1 — **CQ1**, **CQ2**, **CQ3**. Every commit
flushes the entire causal cone of the committed leader, and the quorum
structure forces every layer of every valid cone to carry blocks from
all but at most `f` of the correct validators. So each commit carries,
at every round below it, blocks from **at least half of the correct
validators** — with no synchrony assumption, no delivery model, and no
populated rounds anywhere in the hypotheses. The engine is density
(D25, `card_missingAt_le`); everything here is packaging.

The metric is **per-round author coverage**, not a block-count
fraction: an equivocator can inflate a cone with any number of blocks
per round, so the raw fraction is adversary-deflatable, while the
author count is what density bounds (`chain-quality.md` §2, a recorded
decision).
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {b L : BlockId} {δ : ℕ}

/-- The correct validators whose round-`δ` block a cone carries — the
complement, within `Correct`, of `missingAt`. -/
def coveredAt (U : BlockUniverse Validator BlockId Payload)
    (b : BlockId) (δ : ℕ) : Finset Validator :=
  (Correct : Finset Validator).filter fun v =>
    ∃ i ∈ history U b, (U.block i).creator = v ∧ (U.block i).round = δ

theorem mem_coveredAt {v : Validator} :
    v ∈ coveredAt U b δ ↔
      v ∈ (Correct : Finset Validator) ∧
        ∃ i ∈ history U b, (U.block i).creator = v ∧ (U.block i).round = δ :=
  Finset.mem_filter

theorem coveredAt_subset_correct :
    coveredAt U b δ ⊆ (Correct : Finset Validator) :=
  Finset.filter_subset _ _

/-- Covered and missing partition the correct validators. -/
theorem coveredAt_eq_sdiff :
    coveredAt U b δ = (Correct : Finset Validator) \ missingAt U b δ := by
  ext v
  rw [mem_coveredAt, Finset.mem_sdiff, mem_missingAt]
  constructor
  · rintro ⟨hv, i, hi, hic, hir⟩
    exact ⟨hv, fun ⟨_, hall⟩ => hall i hi ⟨hic, hir⟩⟩
  · rintro ⟨hv, hmiss⟩
    refine ⟨hv, ?_⟩
    by_contra hnone
    push_neg at hnone
    exact hmiss ⟨hv, fun i hi ⟨hic, hir⟩ => hnone i hi hic hir⟩

/-- **CQ1, the count.** A valid block's cone covers all but at most `f`
of the correct validators, at every round below it. Purely structural:
density (D25) plus the partition. -/
theorem card_coveredAt_ge (hb : b ∈ U.ids) (hδ : δ < (U.block b).round) :
    (Correct : Finset Validator).card - F.f ≤ (coveredAt U b δ).card := by
  have hsub : missingAt U b δ ⊆ (Correct : Finset Validator) :=
    Finset.filter_subset _ _
  have hcard := Finset.card_sdiff_of_subset hsub
  have hmiss := card_missingAt_le hb hδ
  rw [coveredAt_eq_sdiff, hcard]
  omega

section Decided

variable [S : Slots Validator]

/-- **CQ1.** A committed leader's flush covers all but at most `f` of
the correct validators at every round below it — any route, any view,
no synchrony. -/
theorem card_coveredAt_ge_of_decided {V : View Validator BlockId Payload U}
    {k : ℕ} (h : Decided U V k (some L)) (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card - F.f ≤ (coveredAt U L δ).card :=
  card_coveredAt_ge (isLeaderBlock_of_decided h).1 hδ

/-- **CQ2 (the half, exactly).** Every commit carries, at every round
below it, blocks from at least half of the correct validators:
`|Correct| ≤ 2·|covered|`, since `|Correct| ≥ 2f + 1`. -/
theorem card_correct_le_two_mul_coveredAt_of_decided
    {V : View Validator BlockId Payload U} {k : ℕ}
    (h : Decided U V k (some L)) (hδ : δ < (U.block L).round) :
    (Correct : Finset Validator).card ≤ 2 * (coveredAt U L δ).card := by
  have h1 := card_coveredAt_ge_of_decided h hδ
  have h2 := two_f_add_one_le_card_correct (Validator := Validator)
  omega

/-- A cone block of a committed slot is in the ledger — the one
unfolding both CQ3 and CQ6 rest on. -/
theorem mem_ledgerSet_of_mem_history {g : ℕ → Option BlockId} {n k : ℕ}
    (hg : g k = some L) (hk : k < n) (hL : L ∈ U.ids)
    (hb : b ∈ history U L) : b ∈ ledgerSet U g n :=
  ⟨k, hk, L, hg, (mem_history_iff hL).mp hb⟩

/-- **CQ3 (ledger coverage, cumulative).** For a verdict assignment `g`
of a view with a committed slot `k < n` whose leader sits at round `r`:
for every `δ < r`, at least `|Correct| − f` correct validators each
have a round-`δ` block in the ledger `ledgerSet U g n`. The set is
exhibited (`coveredAt`), so no choice and no decidability of the
ledger is needed; view-independence is `ledgerSet_agree`. -/
theorem ledger_coverage {V : View Validator BlockId Payload U}
    {g : ℕ → Option BlockId} {n k : ℕ}
    (hdec : Decided U V k (some L)) (hg : g k = some L) (hk : k < n)
    (hδ : δ < (U.block L).round) :
    ∃ S : Finset Validator, S ⊆ (Correct : Finset Validator) ∧
      (Correct : Finset Validator).card - F.f ≤ S.card ∧
      ∀ v ∈ S, ∃ i ∈ ledgerSet U g n,
        (U.block i).creator = v ∧ (U.block i).round = δ := by
  refine ⟨coveredAt U L δ, coveredAt_subset_correct,
    card_coveredAt_ge_of_decided hdec hδ, ?_⟩
  intro v hv
  obtain ⟨-, i, hi, hic, hir⟩ := mem_coveredAt.mp hv
  exact ⟨i, mem_ledgerSet_of_mem_history hg hk
    (isLeaderBlock_of_decided hdec).1 hi, hic, hir⟩

end Decided

end LeanDag
