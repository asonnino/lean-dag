import LeanDag.RedSnapper.Uncontested.Statement
import LeanDag.RedSnapper.Helpers.Liveness

/-!
# Uncontested liveness — proof

Generated proof layer; not part of the audit surface. Synchrony carries
the transaction from the carrier into every correct block of the next
two rounds; with no rival anywhere, `fast_vote_of_sole` makes each of
them a fast vote; every correct `r₀ + 2` block then references a
correct quorum of fast votes and keeps its own ACK — a certificate —
and the correct pool is itself the quorum of certificate authors.
-/

namespace LeanDag

namespace RedSnapper

namespace Uncontested

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj}

omit [DecidableEq BlockId] in
theorem fastLiveness : FastLiveness U := by
  intro hdisc hrule tx r₀ R b₀ hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1 hpop2
  apply atLeast_of_correct_blocks quorum_le_card_correct
  intro v hv
  obtain ⟨b₂, hb₂, hab₂, hrb₂⟩ := hpop2 v hv
  have hvc₂ : (U.block b₂).author ∈ (Correct : Finset Validator) := hab₂.symm ▸ hv
  refine ⟨b₂, Finset.mem_filter.mpr ⟨hb₂, hrb₂⟩, hab₂, ?_⟩
  -- b₂ includes tx through its author's own r₀+1 block and the carrier
  obtain ⟨b₁ᵥ, hb₁ᵥ, hab₁ᵥ, hrb₁ᵥ⟩ := hpop1 v hv
  have hvc₁ᵥ : (U.block b₁ᵥ).author ∈ (Correct : Finset Validator) := hab₁ᵥ.symm ▸ hv
  have hpar₀ : b₀ ∈ (U.block b₁ᵥ).parents :=
    hsync b₁ᵥ hb₁ᵥ hvc₁ᵥ (by omega) b₀ hb₀ hc₀ (by omega)
  have hpar₁ : b₁ᵥ ∈ (U.block b₂).parents :=
    hsync b₂ hb₂ hvc₂ (by omega) b₁ᵥ hb₁ᵥ hvc₁ᵥ (by omega)
  have hinc₂ : Includes U b₂ tx :=
    includes_mono (Reaches.of_mem_parents hpar₁ (Reaches.single hpar₀)) hinc₀
  refine ⟨fast_vote_of_sole hrule hval hsole hb₂ hvc₂ hinc₂, ?_⟩
  -- every correct validator's r₀+1 block is a fast-vote parent of b₂
  apply atLeast_of_correct_blocks quorum_le_card_correct
  intro w hw
  obtain ⟨b₁, hb₁, hab₁, hrb₁⟩ := hpop1 w hw
  have hwc₁ : (U.block b₁).author ∈ (Correct : Finset Validator) := hab₁.symm ▸ hw
  have hpar₀' : b₀ ∈ (U.block b₁).parents :=
    hsync b₁ hb₁ hwc₁ (by omega) b₀ hb₀ hc₀ (by omega)
  have hinc₁ : Includes U b₁ tx := includes_mono (Reaches.single hpar₀') hinc₀
  exact ⟨b₁, hsync b₂ hb₂ hvc₂ (by omega) b₁ hb₁ hwc₁ (by omega), hab₁,
    fast_vote_of_sole hrule hval hsole hb₁ hwc₁ hinc₁⟩

theorem fastVerdict : FastVerdict U := by
  intro hdisc hrule tx r₀ R b₀ hown hval hsole hb₀ hc₀ hr₀ hinc₀ hRr hsync hpop1 hpop2
    A V hVfull
  have hq := fastLiveness hdisc hrule tx r₀ R b₀ hval hsole hb₀ hc₀ hr₀ hinc₀ hRr
    hsync hpop1 hpop2
  refine TxVerdict.fastFinal (r := r₀ + 2) hown ?_
  unfold FastQuorumAtInView
  have heq : blocksAt U (r₀ + 2) ∩ V.ids = blocksAt U (r₀ + 2) :=
    Finset.inter_eq_left.mpr fun b hb => hVfull (mem_ids_of_mem_blocksAt hb)
  rw [heq]
  exact hq

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U
  exact ⟨fastLiveness, fastVerdict⟩

end Uncontested

end RedSnapper

end LeanDag
