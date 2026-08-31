import LeanDag.RedSnapper.Revocation.Proof
import LeanDag.RedSnapper.CertificateExclusion.Proof
import LeanDag.RedSnapper.TxAgreement.Proof
import LeanDag.RedSnapper.Uncontested.Proof
import LeanDag.RedSnapper.ConflictResolution.Proof
import LeanDag.RedSnapper.Five.FullCertSafety.Proof

/-!
# The axioms tripwire

Build-failing enforcement of the acceptance criterion: every headline
theorem depends on exactly the standard triple `propext`,
`Classical.choice`, `Quot.sound`. `#guard_msgs` fails elaboration — hence
`lake build`, hence CI — on any deviation: a smuggled axiom, a `sorry`
anywhere in the dependency tree, or a dropped axiom, which is as loud.
-/

/--
info: 'LeanDag.RedSnapper.Revocation.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.RedSnapper.Revocation.holds

/--
info: 'LeanDag.RedSnapper.CertificateExclusion.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.RedSnapper.CertificateExclusion.holds

/--
info: 'LeanDag.RedSnapper.TxAgreement.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.RedSnapper.TxAgreement.holds

/--
info: 'LeanDag.RedSnapper.Uncontested.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.RedSnapper.Uncontested.holds

/--
info: 'LeanDag.RedSnapper.ConflictResolution.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.RedSnapper.ConflictResolution.holds

/--
info: 'LeanDag.RedSnapper.FullCertSafety.holds' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms LeanDag.RedSnapper.FullCertSafety.holds
