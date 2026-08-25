import LeanDag.BlackMarlin.Reactive.Statement
import LeanDag.BlackMarlin.Helpers.Reactive

/-!
# Black Marlin — the reactive schedule, proved

Generated proof layer; not part of the audit surface. Each conjunct is
one helper of `Helpers/Reactive.lean`: `Pace.votes` for BMR1,
`Pace.reactive_committed` for BMR2, `Pace.concludesAt_of_holds` for BMR3,
`Pace.concludesAt_of_sustained` for BMR4, the two `built_succ_le_of_fast`
forms for BMR5 and `Pace.no_timeout_of_fast_gst` for BMR6.
-/

namespace LeanDag

namespace BlackMarlin

namespace Reactive

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ _ _ U T N pc
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro R r A hT hcard hgst hto hR hN hlead hA
    exact pc.votes hT hcard hgst hto hR hN hlead hA
  · intro R r hT hcard hgst hto hR hN hlead hlead1
    exact pc.reactive_committed hT hcard hgst hto hR hN hlead hlead1
  · intro r v t hcard hv hN hheld ha0 ha1 ha2 hvotes
    exact pc.concludesAt_of_holds hcard hv hN hheld ha0 ha1 ha2 hvotes
  · intro r v t₀ t hcard hv hN hheld hprev ht ha1 ha2 hvotes
    exact pc.concludesAt_of_sustained hcard hv hN hheld hprev ht ha1 ha2 hvotes
  · intro r v δ D R hcard hv hN hδ ha0 ha1 ha2 hvotes
    refine ⟨fun hD => pc.built_succ_le_of_fast hcard hv hN hδ hD ha0 ha1 ha2 hvotes,
      fun hgst hR => pc.built_succ_le_of_fast_gst hcard hv hN hgst hR hδ ha0 ha1 ha2 hvotes⟩
  · intro r v δ R hcard hv hN hgst hR hδ ha0 ha1 ha2 hvotes hfast
    exact pc.no_timeout_of_fast_gst hcard hv hN hgst hR hδ ha0 ha1 ha2 hvotes hfast

end Reactive

end BlackMarlin

end LeanDag
