import LeanDag.Steelhead.Liveness.Statement
import LeanDag.Steelhead.Helpers.Liveness
/-!
# Liveness at any lawful rule — proof

Generated proof layer; not part of the audit surface. Each conjunct is
the helper of the same name in `Helpers/Liveness.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Liveness

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ S U R p good ws wa k
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro rules h
    exact commitsUnderSync_compose h
  · intro T c hleast hcu hT hcard hspan fair R₀ k
    exact allDecidedBelowOfSynchrony hleast hcu hT hcard hspan fair R₀ k
  · intro rules h
    exact skipsSilent_compose h
  · intro T V R₀ N k a hleast hcu hid hT hcard hs hpop hR hka hlead hdec hN hV
    exact decidedOfReliableAboveFloor hleast hcu hid hT hcard hs hpop hR hka hlead hdec hN hV
  · intro T V R₀ N h x hleast hcu hid hT hcard hs hpop hR hhop hlead hN hV
    exact floorChainDecides hleast hcu hid hT hcard hs hpop hV h x hR hhop hlead hN
  · intro n hn T
    exact ⟨fun _ hlt => roundRobin_fairRun hn hlt, fun hT r => roundRobin_near hn hT r⟩
  · intro T V R₀ N ws n hn lead x hl hcu hwr hid hT hcard hs hpop hV hbij hsched hlt hR hhop hN
    exact floorChainReachesReliable hn hl hcu hwr hid hT hcard hs hpop hV hbij hsched hlt hR hhop
      hN
  · intro T V R₀ N ws n hn lead x hl hcu hsk hwr hid hT hcard hs hpop hV hcrash hbij hsched hlt
      hR hstart hhop hN
    exact floorChainReachesReliableWithinByzantine hn hl hcu hsk hwr hid hT hcard hs hpop hV hcrash
      hbij hsched hlt hR hstart hhop hN
  · intro T V R₀ N ws n hn lead k hl hleast hcu hsk hwr hid hT hcard hs hpop hV hcrash hbij hsched
      hlt hR hstart hN
    exact floorChainDecidesWithinRounds hn hl hleast hcu hsk hwr hid hT hcard hs hpop hV hcrash
      hbij hsched hlt hR hstart hN
  · intro T V N k vp hcu hT hcard hrate N' hR hpop hN hV hlead
    exact commitsOfViewPace hcu vp hT hcard hrate hR hpop hN hV hlead
  · intro V h x hleast hid hhop hcom
    exact floorChainDecidesFromCommit hleast hid h x hhop hcom
  · intro n p hn T hp hlt r
    exact periodicRoundRobinReliableSync hn hp hlt r
  · intro T V R₀ N ws p n hn lead x hl hcu hw0 hp hid hkind hsched hT hcard hs hpop hV hbij hlt
      hasync hR hstart hhop hN
    exact floorChainReachesAtPeriod hn hp hl hcu hw0 hid hkind hsched hT hcard hs hpop hV hbij hlt
      hasync hR hstart hhop hN
  · intro T V R₀ N ws wa p n W hn lead k hl hleast hcu hsk hw0 hw1 hp hid hkind hsched hT hcard hs
      hpop hV hcrash hbij hlt hwait hasync hR hstart hN
    exact floorChainDecidesWithinRoundsAtPeriod hn hp hl hleast hcu hsk hw0 hw1 hid hkind hsched hT
      hcard hs hpop hV hcrash hbij hlt hwait hasync hR hstart hN
  · intro S' V c N wa hleast hgc hw hmono hrun hV k hk
    exact chainAllDecidedBelow hleast hgc (fun _ => hw _) hmono hrun hV k hk
  · intro S' T wa hleast hcu hw hT hcard hmono fair R₀ k
    exact chainAllDecidedBelowOfSynchrony hleast hcu (fun _ => hw _) hT hcard hmono fair R₀ k
  · intro coin V b wa hleast hgc hw hgood hV
    exact chainAllDecidedBelowOfRun hleast hgc hw hgood hV
  · intro V ws k hw0 hws hk hid hkind hcl hskip i hi v h
    exact stall hw0 hws hk hid hkind hcl hskip hi h
  · intro V b hleast hw hid hrun
    exact allDecidedBelowOfRun hleast hw hid hrun
  · intro V c N wa hleast hgc hwa hid hone hrun hV r hr
    exact allDecidedBelowAtPeriodOne hleast hgc hwa hid hone hrun hV r hr
  · intro hid hkind hw0 hw1 hwa r hr
    exact asyncSlotCost hid hkind hw0 hw1 hwa hr

end Liveness

end Steelhead

end LeanDag
