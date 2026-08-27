import LeanDag.HammerheadTwo.Window.Statement

/-!
# HH2 — proof

Generated proof layer; not part of the audit surface. Membership in a
history is reachability (`reaches_of_mem_historyUptoFrom`), and a view
closed under references contains everything reachable from a block it
holds (`mem_of_reaches_of_closed`, with A2 as the closure).
-/

namespace LeanDag

namespace HammerheadTwo

namespace Window

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R hR
  have hin : HistoryInView R := by
    intro U V A hA i hi
    exact mem_of_reaches_of_closed (hR.view_complete V) hA
      (reaches_of_mem_historyUptoFrom hi)
  refine ⟨hin, ?_⟩
  intro U V₁ V₂ A h₁ h₂
  rw [Finset.inter_eq_left.mpr (hin U V₁ A h₁), Finset.inter_eq_left.mpr (hin U V₂ A h₂)]

end Window

end HammerheadTwo

end LeanDag
