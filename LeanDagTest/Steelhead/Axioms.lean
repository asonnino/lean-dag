import LeanDag.Steelhead.Properties
import LeanDag.Steelhead.Safety.Proof
import LeanDag.Steelhead.Liveness.Proof
import LeanDag.Steelhead.MahiMahiPair.Liveness.Proof
import LeanDag.Steelhead.Period.Proof
import LeanDag.Steelhead.MahiMahiPair.Period.Proof
import LeanDag.Steelhead.BlueBottlePair.Period.Proof
import LeanDag.Steelhead.Coin.Proof
import LeanDag.Steelhead.Ledger.Proof
import LeanDag.Steelhead.Interface.Proof
import LeanDag.Steelhead.MahiMahiPair.Proof
import LeanDag.Steelhead.BlueBottlePair.Proof
import LeanDag.Steelhead.BlueBottlePair.Liveness.Proof
import LeanDag.Steelhead.Broadcast.Proof
import LeanDag.Steelhead.Replay.Proof
import LeanDag.Steelhead.Timeout.Proof
import LeanDag.Steelhead.MahiMahiPair.Safety.Proof
import LeanDag.Steelhead.MahiMahiPair.Ledger.Proof
import LeanDag.Steelhead.MahiMahiPair.Broadcast.Proof
import LeanDag.Steelhead.BlueBottlePair.Safety.Proof
import LeanDag.Steelhead.BlueBottlePair.Ledger.Proof
import LeanDag.Steelhead.BlueBottlePair.Broadcast.Proof
/-!
# Steelhead — axiom audit

Every principal result of the arc, checked to depend on the three
standard axioms and nothing else. Drift detection: a `sorryAx` or a
bespoke axiom would show here before anywhere else.
-/

#print axioms LeanDag.Steelhead.Safety.holds
#print axioms LeanDag.Steelhead.MahiMahiPair.Safety.holds
#print axioms LeanDag.Steelhead.BlueBottlePair.Safety.holds
#print axioms LeanDag.Steelhead.Liveness.holds
#print axioms LeanDag.Steelhead.MahiMahiPair.Liveness.holds
#print axioms LeanDag.Steelhead.Period.holds
#print axioms LeanDag.Steelhead.MahiMahiPair.Period.holds
#print axioms LeanDag.Steelhead.BlueBottlePair.Period.holds
#print axioms LeanDag.Steelhead.Coin.holds
#print axioms LeanDag.Steelhead.Ledger.holds
#print axioms LeanDag.Steelhead.MahiMahiPair.Ledger.holds
#print axioms LeanDag.Steelhead.BlueBottlePair.Ledger.holds
#print axioms LeanDag.Steelhead.Interface.holds
#print axioms LeanDag.Steelhead.MahiMahiPair.holds
#print axioms LeanDag.Steelhead.BlueBottlePair.holds
#print axioms LeanDag.Steelhead.BlueBottlePair.Liveness.holds
#print axioms LeanDag.Steelhead.Broadcast.holds
#print axioms LeanDag.Steelhead.MahiMahiPair.Broadcast.holds
#print axioms LeanDag.Steelhead.BlueBottlePair.Broadcast.holds
#print axioms LeanDag.Steelhead.Replay.holds
#print axioms LeanDag.Steelhead.Timeout.holds
#print axioms LeanDag.SteelheadProperties.banded
#print axioms LeanDag.SteelheadProperties.safety
#print axioms LeanDag.SteelheadProperties.persist
#print axioms LeanDag.SteelheadProperties.liveness
