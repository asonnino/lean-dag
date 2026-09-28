import LeanDag.AsyncBlueBottle.Safety.Proof
import LeanDag.AsyncBlueBottle.Counting.Proof
import LeanDag.AsyncBlueBottle.Liveness.Proof
import LeanDag.AsyncBlueBottle.Synchrony.Proof
/-!
# Async BlueBottle — axiom audit

Every principal result of the arc, checked to depend on the three
standard axioms and nothing else. Drift detection: a `sorryAx` or a
bespoke axiom would show here before anywhere else.
-/

#print axioms LeanDag.AsyncBlueBottle.Safety.holds
#print axioms LeanDag.AsyncBlueBottle.Counting.holds
#print axioms LeanDag.AsyncBlueBottle.Liveness.holds
#print axioms LeanDag.AsyncBlueBottle.Synchrony.holds
