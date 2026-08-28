import LeanDag.Barnacle.Healthy.Statement

/-!
# BN12 — proof

Generated proof layer; not part of the audit surface. The scoring slots
of the window are the product `Icc waveLength interval ×ˢ range m`, of
cardinality `expected`; each lies in the filtered product `observed`
counts, so the count dominates it. The rule's threshold test then passes
by monotonicity.
-/

namespace LeanDag

namespace Barnacle

namespace Healthy

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R P getLeader hk
  have hcount : Counted R P getLeader hk := by
    intro U A hA m hm hmax hwi hint hH
    -- the scoring slots, as a product of intervals
    set W : Finset (ℕ × ℕ) := (Finset.Icc R.waveLength P.interval) ×ˢ Finset.range m with hW
    have hcard : W.card = expected R P m := by
      rw [hW, Finset.card_product, Nat.card_Icc, Finset.card_range, expected]
      congr 1
      omega
    have hsub : W ⊆ (Finset.range (P.interval + 1) ×ˢ Finset.range m).filter
        (fun dl : ℕ × ℕ => dl.1 ≤ (R.block U A).round ∧
          R.SlotDirect (Sched getLeader hk m hm hmax) U (R.historyView U A hA)
            (m * ((R.block U A).round - dl.1) + dl.2)) := by
      intro dl hdl
      rw [hW, Finset.mem_product, Finset.mem_Icc, Finset.mem_range] at hdl
      obtain ⟨⟨hlo, hhi⟩, hl⟩ := hdl
      rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨by omega, hl⟩, by omega, hH dl.1 hlo hhi dl.2 hl⟩
    have : W.card ≤ (observed R P getLeader hk U A m hm hmax) := by
      rw [observed, dif_pos hA]
      exact Finset.card_le_card hsub
    omega
  refine ⟨hcount, ?_⟩
  intro U A hA m hm hmax backoff hnd hwi hint hH
  have hge : expected R P m ≤ observed R P getLeader hk U A m hm hmax :=
    hcount U A hA m hm hmax hwi hint hH
  have htest : P.num * expected R P m ≤ P.den * observed R P getLeader hk U A m hm hmax :=
    le_trans (Nat.mul_le_mul_right _ hnd) (Nat.mul_le_mul_left _ hge)
  rw [Aimd.rule, dif_pos ⟨hm, hmax⟩, decide_eq_true htest, Aimd.update, if_pos rfl]

end Healthy

end Barnacle

end LeanDag
