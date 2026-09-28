import LeanDag.Properties.Record
import LeanDag.AsyncBlueBottle.Properties
/-!
# Async BlueBottle on the record

The witness that Async BlueBottle runs on the core's universes, from
which the cut, the copy fill and re-genesis are the record's own and
every verdict cell is `Properties/Arcs/Record.lean` at this instance.
-/

namespace LeanDag

namespace AsyncBlueBottleProperties

open LeanDag.Properties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

section AsyncBlueBottleRecord

variable [Faults5 Validator] {B : Type} [LinearOrder B]

/-- **Async BlueBottle's carrier, read as block records.** -/
def onRecord :
    (AsyncBlueBottleProperties.asyncBlueBottleRule (Validator := Validator) (BlockId := B)
      (Payload := Payload)).OnRecord ValidWrt (Correct : Finset Validator) BlockRecord.Any where
  toRec := fun U => U
  inv := fun _ => True.intro
  ofRec := fun W _ => W
  ids_to := fun _ => rfl
  block_to := fun _ => rfl
  ids_of := fun _ _ => rfl
  block_of := fun _ _ => rfl
  toRec_ofRec := fun _ _ => rfl
  toView := fun V => V
  ofView := fun V => V
  viewIds_to := fun _ => rfl
  viewIds_of := fun _ => rfl

end AsyncBlueBottleRecord

end AsyncBlueBottleProperties

end LeanDag
