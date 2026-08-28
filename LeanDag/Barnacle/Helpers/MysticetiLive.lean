import LeanDag.Barnacle.MysticetiLive.Statement

/-!
# Mysticeti liveness helpers

Not part of the audit surface. The descent laws for Mysticeti:
`goodLeaders` is L4 (`decided_of_leader_mem`), `indirect` the two
indirect constructors of `Decided` by cases on a certified candidate.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

theorem mysticetiLive_descent [F : Faults Validator] :
    (mysticetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent
      F.f where
  goodLeaders := by
    intro U Rnd N hgood
    obtain ⟨T, -, hcard, hsync, hpop⟩ := hgood
    refine ⟨T, by omega, ?_⟩
    intro S V κ hcov hRnd hN hlead
    letI := S
    change S.slotRound κ + 3 ≤ N at hN
    obtain ⟨L, hLb, hdc⟩ := directCommit_of_leader_mem hcard hsync hRnd
      (hpop _ hRnd (by omega)) (hpop _ (by omega) (by omega)) (hpop _ (by omega) (by omega)) hlead
    refine ⟨L, Decided.directCommit hLb ?_⟩
    -- the certificates sit at `slotRound κ + 2`, a round the view covers
    have hsub : certificates U L (S.slotRound κ) ⊆ V.ids := by
      intro c hc
      rw [certificates, Finset.mem_filter, mem_blocksAt] at hc
      obtain ⟨⟨hcids, hcr⟩, -⟩ := hc
      exact hcov c hcids (by show (U.block c).round ≤ N; omega)
    show quorumCard Validator ≤ (creatorsOf U.block (certificatesIn U V L (S.slotRound κ))).card
    rwa [certificatesIn, Finset.inter_eq_left.2 hsub]
  indirect := by
    intro S U V i j A hij hj hmid
    letI := S
    change S.slotRound i + 3 ≤ S.slotRound j at hij
    have helig : Eligible Validator i j := eligible_iff.mpr hij
    have hmid' : ∀ i', i < i' → i' < j → Eligible Validator i i' → Decided U V i' none :=
      fun i' h1 h2 h3 => hmid i' h1 h2 (eligible_iff.mp h3)
    by_cases hc : ∃ L, IsLeaderBlock U i L ∧ CertifiedIn U A L (S.slotRound i)
    · obtain ⟨L, hL, hcert⟩ := hc
      exact ⟨some L, Decided.indirectCommit (lt_of_eligible helig) helig hj hmid' hL hcert⟩
    · push Not at hc
      exact ⟨none, Decided.indirectSkip (lt_of_eligible helig) helig hj hmid' hc⟩

#print axioms mysticetiLive_descent

end Barnacle

end LeanDag
