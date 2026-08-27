import LeanDag.FinWhale.Evidence

/-!
# FinWhale — what follows from Lemma 4

The paper's Lemmas 2, 5, 8, and the direct-commit halves of 9 and 10.

**Voters for conflicting blocks are disjoint** (`parentsVoting_disjoint`),
because validity gives a block one edge per validator and two blocks of a
slot share an author. That single fact carries Lemma 2 and Lemma 8, and
it is also what Lemma 9's third case actually needs.

**Lemma 9's third case is right for a reason the paper does not give.**
The paper argues that under a fast commit for `b`, "any honest validator
can produce FP-evidence blocks only for `b`, and not for the conflicting
block `b′`, by Lemma 4". Lemma 4 says every round-`(r+2)` block *is*
FP-evidence for `b`; it does not say none is *also* FP-evidence for `b′`,
and the paper elsewhere notes that a DAG may carry FP-evidence for
conflicting blocks at once. The conclusion holds, and
`not_fpEvidence_conflicting` proves it, but from the definition's own two
branches rather than from Lemma 4: a block that has seen the equivocation
carries fewer than `f + p` parents voting for `b′`, which is what its
branch forbids, and one that has not is leader-consistent, so its parents
vote for at most one of the pair.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- **A validator's parent votes once.** A block carries one edge per
validator, and two blocks of a slot share an author, so no parent votes
for both and the two voter sets are disjoint. -/
theorem parentsVoting_disjoint {b l l' : BlockId} (hb : b ∈ D.ids)
    (hconf : Conflicting D l l') :
    Disjoint (parentsVoting D b l) (parentsVoting D b l') := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  simp only [parentsVoting, mem_creatorsOf, Finset.mem_filter] at hv hv'
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  obtain ⟨q', ⟨hq', hq'ref⟩, hq'v⟩ := hv'
  -- one edge per validator makes the two parents the same block
  have heq : q = q' :=
    (D.valid b hb).distinct_creators q hq q' hq' (by rw [hqv, hq'v])
  subst heq
  -- which then references both `l` and `l'`, sharing an author
  have hqids : q ∈ D.ids := D.complete b hb q hq
  exact hconf.1 ((D.valid q hqids).distinct_creators l hqref l' hq'ref hconf.2.2)

/-- **A quorum for one block bounds the parents voting for the other.**
The two voter sets are disjoint inside a parent set of at most `n`, so
`2f + p` for one leaves at most `f + p − 1` for the other. -/
theorem conflicting_le_of_spQuorum {b l l' : BlockId} (hb : b ∈ D.ids)
    (hconf : Conflicting D l l') (hcert : SPCertificate D b l) :
    (parentsVoting D b l').card + 1 ≤ F.f + P.p := by
  have hdisj := parentsVoting_disjoint hb hconf
  have hunion : (parentsVoting D b l ∪ parentsVoting D b l').card
      ≤ Fintype.card Validator := by
    rw [← Finset.card_univ]; exact Finset.card_le_univ _
  have hcard := Finset.card_union_of_disjoint hdisj
  have := params_arith (Validator := Validator)
  simp only [SPCertificate, spQuorum] at hcert
  omega

/-- **Lemma 2.** Any SP-certificate for `l` is also FP-evidence for `l`.
Its `2f + p` parents voting for `l` clear both branches, and on the
equivocating branch they leave at most `f + p − 1` for anything
conflicting. -/
theorem lemma2 {b l : BlockId} (hb : b ∈ D.ids) (hcert : SPCertificate D b l) :
    FPEvidence D b l := by
  have hq : spQuorum Validator ≤ (parentsVoting D b l).card := hcert
  have := params_arith (Validator := Validator)
  simp only [FPEvidence]
  by_cases hexp : ExposesEquivocation D b
  · rw [if_pos hexp]
    refine ⟨by simp only [spQuorum] at hq; omega, fun l' _ hconf => ?_⟩
    exact conflicting_le_of_spQuorum hb hconf hcert
  · rw [if_neg hexp]
    simp only [spQuorum] at hq; omega

/-- **Lemma 8.** At most one block of a slot gathers a quorum of votes.
Two quorums of `2f + p` among `n = 3f + 2p − 1` share `f + 1` validators,
one of them correct, and a correct validator votes once. -/
theorem lemma8 {l l' : BlockId} (hconf : Conflicting D l l')
    (h : spQuorum Validator ≤ (voters D l).card)
    (h' : spQuorum Validator ≤ (voters D l').card) : False := by
  -- the two voter sets meet in more than `f` validators
  have hmeet := card_add_card_le_card_inter_add_card (voters D l) (voters D l')
  have := params_arith (Validator := Validator)
  have hcard : F.f + 1 ≤ (voters D l ∩ voters D l').card := by
    simp only [spQuorum] at h h'; omega
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hcard
  rw [Finset.mem_inter] at hv
  exact not_voter_of_conflicting hconf v hv.2 hvc hv.1

/-- A fast commit carries a quorum of votes, so it feeds the above. -/
theorem spQuorum_le_of_fastCommit {l : BlockId} (hfast : FastCommit D l) :
    spQuorum Validator ≤ (voters D l).card :=
  le_trans spQuorum_le_fastCard hfast

/-- **Lemma 9's third case, proved from the definition rather than from
Lemma 4.** Under a fast commit for `l`, no round-`(r+2)` block is
FP-evidence for a conflicting `l'`.

A block that has seen the equivocation is FP-evidence for `l` by Lemma 4,
and that branch bounds its parents voting for `l'` below `f + p` — which
is exactly what FP-evidence for `l'` would need. A block that has not
seen it is FP-evidence for `l` with `f + p − 1` parents voting for `l`,
and those parents are disjoint from the ones voting for `l'`; the same
branch would need `f + p − 1` for `l'`, and the parent set is too small
to hold both. -/
theorem not_fpEvidence_conflicting {b l l' : BlockId}
    (hb : b ∈ D.ids) (hl : l ∈ D.ids) (hl' : l' ∈ D.ids)
    (hround : (D.block b).round = (D.block l).round + 2)
    (hlead : (D.block l).creator = D.leader ((D.block b).round - 2))
    (hconf : Conflicting D l l') (hfast : FastCommit D l) :
    ¬ FPEvidence D b l' := by
  intro hev'
  have hev : FPEvidence D b l := lemma4 hb hl hround hfast
  have := params_arith (Validator := Validator)
  simp only [FPEvidence] at hev hev'
  by_cases hexp : ExposesEquivocation D b
  · -- it has seen the equivocation, so its own branch caps the parents
    -- voting for `l'` below what FP-evidence for `l'` would need
    rw [if_pos hexp] at hev hev'
    have hbound := hev.2 l' hl' hconf
    have hneed := hev'.1
    omega
  · -- it has not, so its parents are leader-consistent and cannot vote for
    -- both; both counts are positive, which is the equivocation it would
    -- have to have seen
    rw [if_neg hexp] at hev hev'
    refine hexp ⟨l, hl, l', hl', hconf, hlead, ?_, ?_⟩
    · rw [← Finset.card_pos]; omega
    · rw [← Finset.card_pos]; omega

/-- **The same exclusion, under a slow-path commit.** A block carrying an
SP-certificate for `l` is not FP-evidence for a conflicting `l'`.

If it has seen the equivocation, the FP-evidence branch caps its parents
voting for `l` below `f + p`, and the certificate already has `2f + p` of
them. If it has not, both counts are positive — `f + p − 1` for `l'` and
`2f + p` for `l` — which is the equivocation it would have to have seen. -/
theorem not_fpEvidence_of_spCertificate {c l l' : BlockId}
    (hl : l ∈ D.ids) (hl' : l' ∈ D.ids)
    (hlead : (D.block l).creator = D.leader ((D.block c).round - 2))
    (hconf : Conflicting D l l') (hcert : SPCertificate D c l) :
    ¬ FPEvidence D c l' := by
  intro hev'
  have := params_arith (Validator := Validator)
  have hcard : spQuorum Validator ≤ (parentsVoting D c l).card := hcert
  simp only [spQuorum] at hcard
  simp only [FPEvidence] at hev'
  by_cases hexp : ExposesEquivocation D c
  · rw [if_pos hexp] at hev'
    have := hev'.2 l hl ⟨Ne.symm hconf.1, hconf.2.1.symm, hconf.2.2.symm⟩
    omega
  · rw [if_neg hexp] at hev'
    refine hexp ⟨l, hl, l', hl', hconf, hlead, ?_, ?_⟩
    · rw [← Finset.card_pos]; omega
    · rw [← Finset.card_pos]; omega

end FinWhale

end LeanDag
