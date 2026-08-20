import LeanDag.MahiMahi.Safety.Proof
import LeanDag.MahiMahi.Counting.Proof
import LeanDag.MahiMahi.Liveness.Proof
import LeanDag.MahiMahi.Synchrony.Proof

/-!
# Mahi-Mahi — axiom audit

Every principal result of the arc, checked to depend on the three
standard axioms and nothing else. Drift detection: a `sorryAx` or a
bespoke axiom would show here before anywhere else.
-/

#print axioms LeanDag.MahiMahi.Safety.holds

#print axioms LeanDag.MahiMahi.Counting.holds
#print axioms LeanDag.MahiMahi.Liveness.holds
#print axioms LeanDag.MahiMahi.Synchrony.holds
