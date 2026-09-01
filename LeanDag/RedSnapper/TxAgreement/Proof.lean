import LeanDag.RedSnapper.TxAgreement.Statement
import LeanDag.RedSnapper.Helpers.Verdict

/-!
# Transaction agreement — proof

Generated proof layer; not part of the audit surface. The core is
`no_both`: a finalization and a drop for one transaction cannot both be
derivable. The finalization is turned into a certificate
(`cert_of_finalized`); a skip-quorum drop then contradicts ack/skip
exclusivity, a rival drop contradicts certificate uniqueness, and a
release drop is impossible because no anchor is ever release-ready — by
`no_ready_of_fastQuorum` when the finalization was consensusless, and by
`no_ready_of_anchor_cert` when it was at an anchor, the readiness floor
coming from conflict monotonicity (`finalizeOnCommit`) or from the
liveness clause `¬ DeadAt` (`resolveCommit`). Agreement is `no_both`
over the fates; no conflicting finalizations is certificate uniqueness;
the mixed corollary reads the anchor off the derivation, the `Owned`
gate barring the consensusless route.
-/

namespace LeanDag

namespace RedSnapper

namespace TxAgreement

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]
  {U : Universe Validator BlockId Tx Obj}

open CertificateExclusion

/-- One transaction is never both finalized and dropped. -/
theorem no_both (hdisc : StanceDiscipline U) {A : Anchors U} {V₁ V₂ : View U} {tx : Tx}
    (h1 : TxVerdict U A V₁ tx Fate.finalized)
    (h2 : TxVerdict U A V₂ tx Fate.dropped) : False := by
  obtain ⟨C, hCid, hCert⟩ := cert_of_finalized h1
  cases h2 with
  | skipDecide hb hcand hq =>
      obtain ⟨Cs, hCsmem, hCs⟩ := exists_of_atLeast quorum_pos hq
      exact ackSkipExclusion hdisc C hCid Cs
        (mem_ids_of_mem_blocksAt (Finset.mem_inter.mp hCsmem).1) tx hCert hCs
  | resolveDropRival hia hcand hriv =>
      obtain ⟨tx0, hconf0, hcand0, hcert0, hlive0⟩ := hriv
      obtain ⟨C₁, hC₁, hc₁, -⟩ := hcert0
      exact certUniqueness hdisc C hCid C₁ hC₁ tx tx0 hconf0 hCert hc₁
  | @resolveDrop i a hia hres hcand =>
      cases h1 with
      | fastFinal ho hq =>
          exact no_ready_of_fastQuorum hdisc
            (atLeast_mono Finset.inter_subset_left hq) i hres.1
      | @finalizeOnCommit j aj hj hcandj hncj hcertj =>
          refine no_ready_of_anchor_cert hdisc hj hcertj (fun k hk hready => ?_) i hres.1
          obtain ⟨ak, hka, hconfk, -, -⟩ := hready
          exact hncj (conflicted_mono (anchor_reaches (le_of_lt hk) hka hj) hconfk)
      | @resolveCommit j aj hj hconfj hcandj hcertj hlivej =>
          refine no_ready_of_anchor_cert hdisc hj hcertj (fun k hk hready => ?_) i hres.1
          exact hlivej ⟨aj, hj,
            Or.inr (Or.inr (releasedBelow_iff_exists.mpr ⟨k, hk, hready⟩))⟩

theorem verdictAgreement (hdisc : StanceDiscipline U) {A : Anchors U} :
    VerdictAgreement U A := by
  intro V₁ V₂ tx f₁ f₂ h1 h2
  cases f₁ <;> cases f₂
  · rfl
  · exact (no_both hdisc h1 h2).elim
  · exact (no_both hdisc h2 h1).elim
  · rfl

theorem noConflictingFinal (hdisc : StanceDiscipline U) {A : Anchors U} :
    NoConflictingFinal U A := by
  intro V₁ V₂ tx tx' h1 h2 hconf
  obtain ⟨C, hC, hc⟩ := cert_of_finalized h1
  obtain ⟨C', hC', hc'⟩ := cert_of_finalized h2
  exact certUniqueness hdisc C hC C' hC' tx tx' hconf hc hc'

theorem mixedViaAnchor {A : Anchors U} : MixedViaAnchor U A := by
  intro V tx hmix h
  cases h with
  | fastFinal ho hq => exact absurd hmix ho
  | @finalizeOnCommit i a hi hcand hnc hcert => exact ⟨i, a, hi, hcert⟩
  | @resolveCommit i a hi hconf hcand hcert hlive => exact ⟨i, a, hi, hcert⟩

theorem holds : Statement := by
  intro Validator BlockId Tx Obj _ _ _ _ _ U A
  exact ⟨fun hdisc => ⟨verdictAgreement hdisc, noConflictingFinal hdisc⟩, mixedViaAnchor⟩

end TxAgreement

end RedSnapper

end LeanDag
