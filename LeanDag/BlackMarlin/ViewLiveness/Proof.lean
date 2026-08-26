import LeanDag.BlackMarlin.ViewLiveness.Statement
import LeanDag.BlackMarlin.Agreement.Proof
import LeanDag.BlackMarlin.Helpers.Liveness

/-!
# Black Marlin — liveness at a validator's view, proved

`ViewLiveness/Statement.lean` states it. Two of the three claims are
compositions: BMA2 and BMA3 already conclude at the view, and what they
ask of the round — that the rotation names reliable validators at two
consecutive rounds — is what BMA4 supplies. BMV3 is BMP13 read at an
anchor, where `IsAnchor` supplies the reliable author the helper wants.

No claim of this file is new work at the level of the DAG. That is the
point of stating it: the arc's liveness results were already available
at a view, and were being read at the universe.
-/

namespace LeanDag

namespace BlackMarlin

namespace ViewLiveness

open Liveness

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ Rot
  refine ⟨?_, ?_, ?_⟩
  · -- BMV1
    intro T R r hcard hfair
    obtain ⟨r', hr', hall⟩ := hfair (max r R)
    have ha0 : Rot.anchor r' ∈ T := by simpa using hall 0 (by omega)
    have ha1 : Rot.anchor (r' + 1) ∈ T := hall 1 (by omega)
    refine ⟨r', le_trans (le_max_left _ _) hr', le_trans (le_max_right _ _) hr', ?_⟩
    intro U N pc hT hc hgst htimeout hN
    exact ((Agreement.holds Validator BlockId Payload U).2.2 T N pc).1
      R r' hT hc hgst htimeout (le_trans (le_max_right _ _) hr') hN ha0 ha1
  · -- BMV2
    intro T R ρ hcard hfair
    obtain ⟨r, hr, hall⟩ := hfair (max ρ R)
    have ha0 : Rot.anchor r ∈ T := by simpa using hall 0 (by omega)
    have ha1 : Rot.anchor (r + 1) ∈ T := hall 1 (by omega)
    refine ⟨r, le_trans (le_max_left _ _) hr, le_trans (le_max_right _ _) hr, ?_⟩
    intro U N pc V A B hT hc hgst htimeout hN hA hB
    exact ((Agreement.holds Validator BlockId Payload U).2.2 T N pc).2
      R r ρ V A B hT hc hgst htimeout (le_trans (le_max_right _ _) hr) hN
      (le_trans (le_max_left _ _) hr) ha0 ha1 hA hB
  · -- BMV3
    intro U T R ρ V L hcard hs hR hpop hanchor hL hheld
    obtain ⟨hmem, hround, hcreator⟩ := hL
    have hc : (U.block L).creator ∈ T := by rw [hcreator]; exact hanchor
    exact supportedIn_of_synchronised hcard hs hR hpop hmem hround hc hheld

end ViewLiveness

end BlackMarlin

end LeanDag
