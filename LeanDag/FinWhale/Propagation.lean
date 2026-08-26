import LeanDag.FinWhale.Skip

/-!
# FinWhale — Lemmas 3 and 5, the evidence reaching upward

Once a leader block is committed, the evidence has to survive into every
later block's history, or a later anchor could skip past it. That is
Lemma 3 for the slow path and Lemma 5 for the fast one.

**Lemma 3.** A quorum of `2f + p` SP-certificates at round `r + 2` is
reached by every block above round `r + 2`. One round up it is quorum
intersection: a round-`(r+3)` block references `n − f` validators, the
certificates come from `2f + p`, and at this committee those meet in
`f + p` — of which `p ≥ 1` are correct. A correct validator's
round-`(r+2)` block is one block, so the one referenced *is* the
certificate. Above that it is induction: a block references at least one
parent, and the parent already reaches a certificate.

**Lemma 5.** Under a fast commit no intersection is needed. Lemma 4 makes
*every* round-`(r+2)` block FP-evidence, so a round-`(r+3)` block's whole
parent set is FP-evidence, and it has `n − f` of them by validity alone.

The two are not the same argument, and the difference is the point of the
fast path: the slow path must *find* its evidence among a quorum, the
fast path cannot avoid it.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- A block above genesis has a parent: validity gives it `n − f`, and
`n − f` is positive. -/
theorem exists_parent {c : BlockId} (hc : c ∈ D.ids) (hround : 0 < (D.block c).round) :
    ∃ q, q ∈ (D.block c).refs := by
  have hq := (D.valid c hc).quorum hround
  have := params_arith (Validator := Validator)
  have hpos : 0 < (creators D.block (D.block c)).card := by
    have hp : P.p ≤ Fintype.card Validator := by
      have := Finset.card_le_univ (F.byzantine); omega
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
  simp only [creators, mem_creatorsOf] at hv
  obtain ⟨q, hq', -⟩ := hv
  exact ⟨q, hq'⟩

/-- **Lemma 3, one round up.** A round-`(r+3)` block references one of the
`2f + p` SP-certificates for `l`. -/
theorem references_spCertificate {c l : BlockId}
    (hc : c ∈ D.ids) (hround : (D.block c).round = (D.block l).round + 3)
    {certs : Finset Validator} (hcert : spQuorum Validator ≤ certs.card)
    (hcertb : ∀ v ∈ certs, ∃ b ∈ blocksAt D ((D.block l).round + 2),
      (D.block b).creator = v ∧ SPCertificate D b l) :
    ∃ b ∈ (D.block c).refs, SPCertificate D b l := by
  have hpar : quorumCard Validator ≤ (parentSet D c).card :=
    (D.valid c hc).quorum (by omega)
  have hmeet := card_add_card_le_card_inter_add_card (parentSet D c) certs
  have := params_arith (Validator := Validator)
  have hcard : F.f + 1 ≤ (parentSet D c ∩ certs).card := by
    simp only [spQuorum] at hcert; omega
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hcard
  rw [Finset.mem_inter] at hv
  obtain ⟨q, hq, hqv⟩ := mem_creatorsOf.1 hv.1
  obtain ⟨b, hb, hbv, hbcert⟩ := hcertb v hv.2
  simp only [blocksAt, Finset.mem_filter] at hb
  -- the parent and the certificate are one block, by `correct_single`
  have hqids : q ∈ D.ids := D.complete c hc q hq
  have hqround : (D.block q).round = (D.block l).round + 2 := by
    have := parent_round hc hq; omega
  have heq : q = b :=
    D.correct_single q hqids b hb.1 (by rw [hqv]; exact hvc) (by rw [hqv, hbv])
      (by rw [hqround, hb.2])
  exact ⟨q, hq, heq ▸ hbcert⟩

/-- **Lemma 3.** Every block above round `r + 2` reaches an SP-certificate
for `l` from round `r + 2`. -/
theorem reaches_spCertificate {l : BlockId} {certs : Finset Validator}
    (hcert : spQuorum Validator ≤ certs.card)
    (hcertb : ∀ v ∈ certs, ∃ b ∈ blocksAt D ((D.block l).round + 2),
      (D.block b).creator = v ∧ SPCertificate D b l) :
    ∀ k : ℕ, ∀ c ∈ D.ids, (D.block c).round = (D.block l).round + 3 + k →
      ∃ b, ReachesFrom D.block c b ∧ SPCertificate D b l := by
  intro k
  induction k with
  | zero =>
    intro c hc hround
    obtain ⟨b, hb, hbcert⟩ := references_spCertificate hc (by omega) hcert hcertb
    exact ⟨b, ReachesFrom.single hb, hbcert⟩
  | succ k ih =>
    intro c hc hround
    obtain ⟨q, hq⟩ := exists_parent hc (by omega)
    have hqids : q ∈ D.ids := D.complete c hc q hq
    have hqround : (D.block q).round = (D.block l).round + 3 + k := by
      have := parent_round hc hq; omega
    obtain ⟨b, hreach, hbcert⟩ := ih q hqids hqround
    exact ⟨b, ReachesFrom.of_mem_refs hq hreach, hbcert⟩

/-- **Lemma 5.** Under a fast commit for `l`, a round-`(r+3)` block's
parents are all FP-evidence for `l`, and validity gives it `n − f` of
them. No intersection argument is needed: Lemma 4 leaves no round-`(r+2)`
block that is not evidence. -/
theorem parents_all_fpEvidence {c l : BlockId}
    (hc : c ∈ D.ids) (hl : l ∈ D.ids)
    (hround : (D.block c).round = (D.block l).round + 3)
    (hfast : FastCommit D l) :
    quorumCard Validator ≤ (parentSet D c).card ∧
      ∀ q ∈ (D.block c).refs, FPEvidence D q l := by
  refine ⟨(D.valid c hc).quorum (by omega), fun q hq => ?_⟩
  have hqids : q ∈ D.ids := D.complete c hc q hq
  have hqround : (D.block q).round = (D.block l).round + 2 := by
    have := parent_round hc hq; omega
  exact lemma4 hqids hl hqround hfast

end FinWhale

end LeanDag
