import LeanDag.Steelhead.Model.Compose
import LeanDag.Steelhead.Model.Decision
import LeanDag.Odontoceti.Decision
import LeanDag.AsyncBlueBottle.Model.Decision
/-!
# Steelhead — the two pairs the interface is instantiated at

The paper instantiates the interface at two pairs of rules, and both are
a family of the shape `compose` takes, one rule per kind
(`docs/kinds.md`). This file names the two families; the claims about
each live in the sibling directories `MahiMahiPair/` and
`BlueBottlePair/`, and what holds of any family at all lives in
`Interface/`.

* **The `3f + 1` pair**, Mysticeti at `ws` and Mahi-Mahi at `wa`, is
  `mahiMahiPair w`: Mahi-Mahi's rule read at the wave of the kind. It is
  one predicate family read at two numbers, since at wave three
  Mahi-Mahi's relation is the core's slot for slot (SH4), and
  `steelheadAnchored w` is its composite by definition (SH16c).
* **The `5f + 1` pair**, BlueBottle's two variants, is `blueBottlePair`:
  Odontoceti, the partially synchronous variant at wave two, at the
  synchronous kind, and Async BlueBottle at wave three elsewhere. Here
  the two rules are genuinely two predicate families, with different
  direct rules and a different indirect test, which is what the composite
  has to carry.

Both are consumed read-only: no file of Odontoceti's or Async
BlueBottle's arc is touched, and neither rule is restated here.

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace Steelhead

/-- **The `3f + 1` pair as a family**: Mahi-Mahi's rule at the wave the wavelength function `w`
gives each kind. `steelheadAnchored w` is its composite (SH16c). -/
def mahiMahiPair (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] (w : ℕ → ℕ) :
    ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct :=
  fun κ => MahiMahi.mahiMahiAnchored Validator BlockId Payload (w κ)

/-- **The `5f + 1` pair as a family**: Odontoceti at the synchronous kind, wave two, and Async
BlueBottle at every other kind, wave three. Unlike `mahiMahiPair` the two members are different
rules, agreeing only on the rung count and the tie-break, which is what the interface asks of a
family and all it asks. -/
def blueBottlePair (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] :
    ℕ → AnchoredRule Validator BlockId Payload ValidWrt Correct :=
  fun κ => if κ = 0 then Odontoceti.odontocetiAnchored Validator BlockId Payload
    else AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload

/-- **The `5f + 1` pair's rule**: the composite of `blueBottlePair`, which is what a validator
running BlueBottle's two variants on one DAG decides by. -/
def blueBottlePairAnchored (Validator BlockId Payload : Type) [Fintype Validator]
    [DecidableEq Validator] [Faults5 Validator] [LinearOrder BlockId] :
    AnchoredRule Validator BlockId Payload ValidWrt Correct :=
  compose (blueBottlePair Validator BlockId Payload)

end Steelhead

end LeanDag
