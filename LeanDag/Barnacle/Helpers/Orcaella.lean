import LeanDag.Barnacle.Orcaella.Statement
import LeanDag.Barnacle.Helpers.Heads

/-!
# Orcaella instance helpers

Not part of the audit surface. The laws are the hybrid agreement
theorem — consuming the bundled `HonestNoEquiv` and the admissibility
of the threshold — with the direct constructor and
`isLeaderBlock_of_decided`; the descent laws are H7a
(`directCommit_of_leader_mem`, at the fully-correct quorum) and the two
indirect constructors, the commit one at the least candidate with a
`k`-thick link. Descent consumes no admissibility: the constructors are
unconditional, and the reliable set alone carries the direct commit.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- The laws, for Orcaella at an admissible threshold. -/
theorem orcaella_laws [HybridFaults Validator] {k : ℕ} (hk : Hybrid.Admissible Validator k) :
    BaseRule.Laws
      (orcaella (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k) where
  view_subset := fun V => V.subset_ids
  view_complete := fun V => V.complete
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := fun S {U} _ _ _ _ _ h₁ h₂ => letI := S; Hybrid.decided_agree U.property hk h₁ h₂
  decided_of_directCommitIn := fun S {_} _ _ _ hL hdc =>
    letI := S; Hybrid.Decided.directCommit hL hdc
  candidates := fun S {_} _ _ _ h => letI := S; Hybrid.isLeaderBlock_of_decided h

/-- The descent laws, for Orcaella at slack `fb + fc`. -/
theorem orcaellaLive_descent [H : HybridFaults Validator] {k : ℕ} :
    (orcaellaLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload) k).Descent
      (H.fb + H.fc) where
  goodLeaders := by
    intro U Rnd N hgood
    obtain ⟨T, -, hcard, hsync, hpop⟩ := hgood
    have hcard' : Fintype.card Validator - (H.fb + H.fc) ≤ T.card := hcard
    refine ⟨T, by omega, ?_⟩
    intro S V κ hcov hRnd hN hlead
    letI := S
    change S.slotRound κ + 2 ≤ N at hN
    obtain ⟨L, hLb, hdc⟩ := Hybrid.directCommit_of_leader_mem hcard hsync hRnd
      (hpop _ hRnd (by omega)) (hpop _ (by omega) (by omega)) hlead
    refine ⟨L, Hybrid.Decided.directCommit hLb ?_⟩
    -- the supporters sit one round up, which the view covers
    have hsub : (blocksAt U.val (S.slotRound κ + 1)).filter
        (fun q => L ∈ (U.val.block q).refs) ⊆ V.ids := by
      intro q hq
      rw [Finset.mem_filter, mem_blocksAt] at hq
      obtain ⟨⟨hqids, hqr⟩, -⟩ := hq
      exact hcov q hqids (by change (U.val.block q).round ≤ N; omega)
    change Hybrid.q Validator ≤ (Hybrid.supportersIn U.val V L (S.slotRound κ)).card
    rw [Hybrid.supportersIn, Finset.inter_eq_left.2 hsub]
    exact hdc
  indirect := by
    intro S U V i j A hij hj hmid
    letI := S
    change S.slotRound i + 2 ≤ S.slotRound j at hij
    have helig : Hybrid.Eligible Validator i j := Hybrid.eligible_iff.mpr hij
    have hmid' : ∀ i', i < i' → i' < j → Hybrid.Eligible Validator i i' →
        Hybrid.Decided k U.val V i' none :=
      fun i' h1 h2 h3 => hmid i' h1 h2 (Hybrid.eligible_iff.mp h3)
    classical
    -- The candidates of `i` with a `k`-thick link to the anchor.
    by_cases hne : (U.val.ids.filter
        (fun L => IsLeaderBlock U.val i L ∧
          Hybrid.ThickLink k U.val A L (S.slotRound i))).Nonempty
    · obtain ⟨_, hL, ht⟩ := Finset.mem_filter.mp (Finset.min'_mem _ hne)
      refine ⟨some _, Hybrid.Decided.indirectCommit
        (Hybrid.lt_of_eligible helig) helig hj hmid' hL ht ?_⟩
      intro L' hL' ht' hlt
      have hL's : L' ∈ U.val.ids.filter
          (fun L => IsLeaderBlock U.val i L ∧
            Hybrid.ThickLink k U.val A L (S.slotRound i)) :=
        Finset.mem_filter.mpr ⟨hL'.1, hL', ht'⟩
      exact absurd hlt (not_lt.mpr (Finset.min'_le _ L' hL's))
    · refine ⟨none, Hybrid.Decided.indirectSkip
        (Hybrid.lt_of_eligible helig) helig hj hmid' ?_⟩
      intro L hL ht
      exact hne ⟨L, Finset.mem_filter.mpr ⟨hL.1, hL, ht⟩⟩

end Barnacle

end LeanDag
