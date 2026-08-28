import LeanDag.Barnacle.Nemo.Statement
import LeanDag.Barnacle.Helpers.Heads

/-!
# Nemo instance helpers — the laws

Not part of the audit surface. The laws are `Nemo.decided_agree`, the
direct constructor and `isLeaderBlock_of_decided`; the descent laws are
`Nemo.decided_of_leader_mem` and the two indirect constructors, at the
slack a majority may miss.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- The laws, for Nemo-Nemo. -/
theorem nemo_laws :
    BaseRule.Laws (nemo (Validator := Validator) (BlockId := BlockId) (Payload := Payload)) where
  view_subset := fun V => V.subset_ids
  view_complete := fun V => V.complete
  full_ids := fun _ => rfl
  historyView_ids := fun _ _ _ => rfl
  agree := fun _ {_} _ _ _ _ _ h₁ h₂ => Nemo.decided_agree h₁ h₂
  decided_of_directCommitIn := fun _ {_} _ _ _ hL hdc => Nemo.Decided.directCommit hL hdc
  candidates := fun _ {_} _ _ _ h => Nemo.isLeaderBlock_of_decided h

/-- The descent laws, for Nemo-Nemo, at the slack a majority may miss:
`n − majority`. -/
theorem nemoLive_descent [Nemo.CrashFaults Validator] :
    (nemoLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      (Fintype.card Validator - Nemo.majority Validator) where
  goodLeaders := by
    intro U Rnd N hgood
    obtain ⟨T, -, hcard, hsync, hpop⟩ := hgood
    refine ⟨T, ?_, ?_⟩
    · have := Nat.sub_le (Fintype.card Validator) (Nemo.majority Validator)
      omega
    intro S V κ hcov hRnd hN hlead
    letI := S
    change S.slotRound κ + 2 ≤ N at hN
    obtain ⟨L, hLb, hdc⟩ := Nemo.directCommit_of_leader_mem hcard hsync hRnd
      (hpop _ hRnd (by omega)) (hpop _ (by omega) (by omega)) hlead
    refine ⟨L, Nemo.Decided.directCommit hLb ?_⟩
    -- the supporters sit one round up, which the view covers
    have hsub : (Nemo.blocksAt U (S.slotRound κ + 1)).filter
        (fun p => L ∈ (U.block p).refs) ⊆ V.ids := by
      intro q hq
      rw [Finset.mem_filter, Nemo.mem_blocksAt] at hq
      obtain ⟨⟨hqids, hqr⟩, -⟩ := hq
      exact hcov q hqids (by show (U.block q).round ≤ N; omega)
    show Nemo.majority Validator ≤ (Nemo.supportersIn U V L (S.slotRound κ)).card
    rw [Nemo.supportersIn, Finset.inter_eq_left.2 hsub]
    exact hdc
  indirect := by
    intro S U V i j A hij hj hmid
    letI := S
    change S.slotRound i + 2 ≤ S.slotRound j at hij
    have helig : Nemo.Eligible Validator i j := Nemo.eligible_iff.mpr hij
    have hmid' : ∀ i', i < i' → i' < j → Nemo.Eligible Validator i i' →
        Nemo.Decided U V i' none :=
      fun i' h1 h2 h3 => hmid i' h1 h2 (Nemo.eligible_iff.mp h3)
    by_cases hc : ∃ L, Nemo.IsLeaderBlock U i L ∧ Nemo.CertifiedIn U A L (S.slotRound i)
    · obtain ⟨L, hL, hcert⟩ := hc
      exact ⟨some L, Nemo.Decided.indirectCommit (Nemo.lt_of_eligible helig) helig hj hmid'
        hL hcert⟩
    · push Not at hc
      exact ⟨none, Nemo.Decided.indirectSkip (Nemo.lt_of_eligible helig) helig hj hmid' hc⟩

/-- The pigeonhole's committee bound holds for the majority slack at
every `n`: `2 · (n − majority) + 1 ≤ n`. -/
theorem majority_bound (n : ℕ) (hn : 0 < n) :
    2 * (n - Nemo.majority (Fin n)) + 1 ≤ n := by
  unfold Nemo.majority
  rw [Fintype.card_fin]
  omega

end Barnacle

end LeanDag
