import LeanDag.Nemo.Liveness

/-!
# Nemo-Nemo: axiom hygiene

All four checks print the repo's baseline axiom set (`propext`,
`Classical.choice`, `Quot.sound`) — Mathlib's `Finset` machinery carries
choice transitively into everything, exactly as in the other arcs. The
point of the checks is drift detection: nothing here should ever acquire
an axiom beyond that baseline (`sorryAx` in particular).
-/

namespace LeanDagTest

#print axioms LeanDag.Nemo.decided_unique
#print axioms LeanDag.Nemo.outputAt_agree
#print axioms LeanDag.Nemo.all_decided_below_of_fairRun
#print axioms LeanDag.Nemo.majority_le_card_live

end LeanDagTest
