import LeanDag.BlackMarlin.Order.Statement
import LeanDag.BlackMarlin.Helpers.Order
import LeanDag.BlackMarlin.Helpers.Descent
import LeanDag.BlackMarlin.Helpers.Liveness

/-!
# Black Marlin — the delivered sequence, proved

Generated proof layer; not part of the audit surface. BMO1 to BMO7 are
one helper of `Helpers/Order.lean` each; BMO8 composes `flushRecord_agree`
with `deliverSeq_agree`, and BMO9 composes `mem_history_of_mem` with
`mem_ledgerSeq_of_mem_history` and `deliverSeq_of_correct`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Order

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f τ ρ L b hL hb
    exact idxOf_le_idxOf_anchor hL hb
  · intro f₁ f₂ τ n h
    exact deliverSeq_agree h
  · intro f τ n m h
    exact deliverSeq_prefix h
  · intro f τ n
    exact ⟨deliverSeq_pairwise, fun b hb => deliverSeq_mem_ids hb⟩
  · intro f τ n b hb
    exact deliverSeq_key_mem hb
  · intro f τ n b hb hc
    exact deliverSeq_of_correct hb hc
  · intro f₁ f₂ τ n a b h hlt
    rw [deliverSeq_agree h] at hlt
    omega
  · intro f₁ f₂ τ B₁ B₂ M σ n h₁ h₂ he₁ he₂ hm₁ hm₂ hn
    refine deliverSeq_agree (fun ρ hρ => ?_)
    rw [he₁, he₂]
    exact flushRecord_agree h₁ h₂ hm₁ hm₂ (by omega)
  · intro f τ T R ρ n b L hT hcard hs hR hpop hb hbr hbc hL hn
    refine deliverSeq_of_correct ?_ (hT hbc)
    refine mem_ledgerSeq_of_mem_history (ρ + 2) L b hL ?_ hn
    exact mem_history_of_mem hcard hs hR hpop hb hbr hbc (f.isAnchor _ L hL).1
      (by rw [(f.isAnchor _ L hL).2.1])

end Order

end BlackMarlin

end LeanDag
