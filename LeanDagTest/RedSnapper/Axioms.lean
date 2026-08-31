import LeanDag.RedSnapper.Revocation.Proof
import LeanDag.RedSnapper.CertificateExclusion.Proof

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
