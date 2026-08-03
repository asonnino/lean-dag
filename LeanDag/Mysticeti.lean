import LeanDag.Support

/-!
# Uncertified DAGs: the Mysticeti commit rules

`spec.md` §4, Phase 2 — Stage A.

A certified DAG (DAG-Rider, Bullshark, Narwhal) admits a block only once
2f+1 validators have signed it, so the block *is* a certificate and
"referenced by 2f+1 validators next round" is the whole commit rule.
Mysticeti drops that round for latency, so blocks carry no authority of
their own and it has to be rebuilt inside the DAG, one round further on:

* a round-`(r+1)` block **votes** for a round-`r` block `L` when `L ∈ refs`,
  and **blames** otherwise;
* a round-`(r+2)` block **certifies** `L` when its own references include
  votes for `L` from 2f+1 *distinct* validators;
* `L` is **directly committed** when certificates for it come from 2f+1
  distinct validators, and **directly skipped** when blames do.

This file is Stage A: everything here is universe-level, so it needs neither
views nor a leader schedule. `L` is an arbitrary block — nothing in M1–M3
cares that it is a leader — and M5 is stated as *same round, same creator*
rather than *same slot*, which is what "same slot" means operationally.
Views, the slot schedule, and the indirect rule arrive in Stages B and C.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The validators whose round-`n` block declines to reference `L`.

The complement of `supporters U L n` *within the round-`n` author pool* —
but only for correct validators. A Byzantine author can appear in both, by
publishing one round-`n` block that votes and another that does not; ruling
that out for correct validators is exactly what `blames_inter_supporters`
does, and is the whole content of M3. -/
def blames (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((blocksAt U n).filter (fun q => L ∉ (U.block q).refs))

theorem mem_blames {L : BlockId} {n : ℕ} {v : Validator} :
    v ∈ blames U L n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ L ∉ (U.block q).refs ∧ (U.block q).creator = v := by
  simp [blames, mem_creatorsOf]
  tauto

/-- A round-`(r+2)` block certifies `L` when the votes for `L` among its own
references come from a quorum of distinct validators. -/
def Certifies (U : BlockUniverse Validator BlockId Payload) (C L : BlockId) : Prop :=
  2 * F.f + 1 ≤
    (creatorsOf U.block ((U.block C).refs.filter (fun q => L ∈ (U.block q).refs))).card

/-- All three rule predicates are cardinality comparisons and so decidable,
but as `Prop`-valued `def`s Lean will not see that unaided. `certificates`
needs this to filter on `Certifies`, and concrete models need it to settle
the rules by `decide`. -/
instance decidableCertifies (C L : BlockId) : Decidable (Certifies U C L) :=
  inferInstanceAs (Decidable (2 * F.f + 1 ≤
    (creatorsOf U.block ((U.block C).refs.filter (fun q => L ∈ (U.block q).refs))).card))

/-- The certificates for a round-`r` block `L`: the round-`(r+2)` blocks that
certify it. -/
def certificates (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) :
    Finset BlockId :=
  (blocksAt U (r + 2)).filter (fun C => Certifies U C L)

/-- `L` is directly committed when its certificates come from a quorum of
distinct validators. -/
def DirectCommit (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  2 * F.f + 1 ≤ (creatorsOf U.block (certificates U L r)).card

/-- `L` is directly skipped when a quorum of distinct validators declined to
vote for it. -/
def DirectSkip (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (r : ℕ) : Prop :=
  2 * F.f + 1 ≤ (blames U L (r + 1)).card

instance decidableDirectCommit (L : BlockId) (r : ℕ) : Decidable (DirectCommit U L r) :=
  inferInstanceAs (Decidable (2 * F.f + 1 ≤ (creatorsOf U.block (certificates U L r)).card))

instance decidableDirectSkip (L : BlockId) (r : ℕ) : Decidable (DirectSkip U L r) :=
  inferInstanceAs (Decidable (2 * F.f + 1 ≤ (blames U L (r + 1)).card))

/-- A correct validator cannot both vote for `L` and blame it: that would be
two distinct round-`n` blocks by one correct author. So the overlap between
blamers and supporters is confined to the Byzantine set.

This is the only place non-equivocation enters M3, and it is what stops a
Byzantine author from being counted on both sides of the ledger. -/
theorem blames_inter_supporters_subset_byzantine {L : BlockId} {n : ℕ} :
    blames U L n ∩ supporters U L n ⊆ F.byzantine := by
  intro v hv
  rw [Finset.mem_inter] at hv
  obtain ⟨hb, hs⟩ := hv
  obtain ⟨q, hq_ids, hq_round, hq_noref, hq_creator⟩ := mem_blames.mp hb
  obtain ⟨q', hq'_ids, hq'_round, hq'_ref, hq'_creator⟩ := mem_supporters.mp hs
  by_contra hcorrect
  -- If `v` were correct, `q` and `q'` would be the same block — but one
  -- references `L` and the other does not.
  have hv_correct : v ∈ (Correct : Finset Validator) := by simpa using hcorrect
  have : q = q' :=
    U.eq_of_creator_eq hq_ids hq'_ids hv_correct hq_creator hq'_creator
      (by rw [hq_round, hq'_round])
  exact hq_noref (this ▸ hq'_ref)

/-- **M3.** A directly skipped block has **no certificate anywhere** in the
universe — not merely none in some view.

With `2f+1` blamers, and correct validators unable to sit on both sides, the
supporters number at most `(3f+1) - (2f+1) + f = 2f`. A certificate needs
`2f+1` distinct vote-creators, and every voter among a round-`(r+2)` block's
references is a genuine supporter, so no such block can exist.

Universe-wide is the right strength: it is why a skip needs no anchor to
justify it, and it is what makes the indirect rule agree with the direct one
(M4). -/
theorem certificates_eq_empty_of_directSkip {L : BlockId} {r : ℕ}
    (h : DirectSkip U L r) : certificates U L r = ∅ := by
  -- Supporters are squeezed by the blamers.
  have hcap : (supporters U L (r + 1)).card ≤ 2 * F.f := by
    have hunion : (blames U L (r + 1) ∪ supporters U L (r + 1)).card ≤ 3 * F.f + 1 := by
      have := Finset.card_le_univ (blames U L (r + 1) ∪ supporters U L (r + 1))
      have := F.card_validators
      omega
    have hinter : (blames U L (r + 1) ∩ supporters U L (r + 1)).card ≤ F.f := by
      refine le_trans (Finset.card_le_card blames_inter_supporters_subset_byzantine) ?_
      exact F.card_byzantine
    have hadd := Finset.card_union_add_card_inter (blames U L (r + 1)) (supporters U L (r + 1))
    rw [DirectSkip] at h
    omega
  -- So no round-(r+2) block can gather a quorum of votes.
  rw [Finset.eq_empty_iff_forall_notMem]
  intro C hC
  rw [certificates, Finset.mem_filter, mem_blocksAt] at hC
  obtain ⟨⟨hC_ids, hC_round⟩, hCert⟩ := hC
  rw [Certifies] at hCert
  -- Every voting reference of `C` is a round-(r+1) supporter of `L`.
  have hsub :
      creatorsOf U.block ((U.block C).refs.filter (fun q => L ∈ (U.block q).refs))
        ⊆ supporters U L (r + 1) := by
    intro v hv
    rw [mem_creatorsOf] at hv
    obtain ⟨q, hq, hq_creator⟩ := hv
    rw [Finset.mem_filter] at hq
    obtain ⟨hq_mem, hq_ref⟩ := hq
    rw [mem_supporters]
    refine ⟨q, U.complete C hC_ids q hq_mem, ?_, hq_ref, hq_creator⟩
    have := U.round_of_mem_refs hC_ids hq_mem
    omega
  have := Finset.card_le_card hsub
  omega

/-- **M1.** No block is both directly committed and directly skipped.

Immediate from M3: a skip leaves no certificates at all, and a commit needs
`2f+1` distinct certificate authors. -/
theorem not_directCommit_of_directSkip {L : BlockId} {r : ℕ}
    (h : DirectSkip U L r) : ¬ DirectCommit U L r := by
  rw [DirectCommit, certificates_eq_empty_of_directSkip h]
  simp [creatorsOf]

/-- **M2.** Once a block is directly committed, its certificate becomes
unavoidable: every block from round `r+3` on has one in its causal history.

The bound is `r+3` and it is **tight**. Certificates sit at round `r+2`, and
a round-`(r+2)` block's own references sit at `r+1`, so a round-`(r+2)` block
that is not itself a certificate reaches none. One round above the
certificates is needed before the intersection argument bites — the same
phenomenon as T3's `r+2`.

This is what makes the indirect rule agree with the direct one, and it is
why the slot schedule must space leaders at least 3 rounds apart: that is
exactly what puts every anchor at round `≥ r+3`. -/
theorem exists_certificate_reaches_of_directCommit {L : BlockId} {r : ℕ}
    (h : DirectCommit U L r)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 3 ≤ (U.block c).round) :
    ∃ C ∈ certificates U L r, Reaches U c C := by
  -- Base case at `r+3`: the certificates' correct authors cannot be dodged.
  have hbase : ∀ c' ∈ U.ids, (U.block c').round = r + 3 →
      ∃ C, C ∈ certificates U L r ∧ Reaches U c' C := by
    intro c' hc' hc'r
    set T := creatorsOf U.block (certificates U L r) ∩ (Correct : Finset Validator) with hT_def
    have hT : ∀ v ∈ T, ∃ q ∈ U.ids,
        (U.block q).round = r + 2 ∧ q ∈ certificates U L r ∧ (U.block q).creator = v := by
      intro v hv
      rw [hT_def, Finset.mem_inter, mem_creatorsOf] at hv
      obtain ⟨⟨q, hq_cert, hq_creator⟩, _⟩ := hv
      have hq := hq_cert
      rw [certificates, Finset.mem_filter, mem_blocksAt] at hq
      exact ⟨q, hq.1.1, hq.1.2, hq_cert, hq_creator⟩
    have hTc : ∀ v ∈ T, v ∈ (Correct : Finset Validator) :=
      fun _ hv => Finset.mem_of_mem_inter_right hv
    have hcard : F.f + 1 ≤ T.card := card_inter_correct_of_quorum h
    obtain ⟨C, hC_mem, hC_cert⟩ :=
      exists_mem_refs_of_correct_support_of_card
        (P := fun q => q ∈ certificates U L r) hT hTc hcard hc' (by omega)
    exact ⟨C, hC_cert, Reaches.single hC_mem⟩
  exact reaches_pred_of_round_le hbase hc hcr

/-- **M5.** At most one block per slot is directly committed: two directly
committed blocks with the same author are the same block.

Stated as *same round, same creator* rather than *same slot*, which is what
"same slot" means operationally and avoids needing a leader schedule at all.
(The round is not a hypothesis — it follows, since both are referenced by
round-`(r+1)` voters.)

This is T5's argument run once per certification layer. Two quorum
intersections and two appeals to non-equivocation peel the layers off, and
then **distinctness** closes it: one correct validator's single round-`(r+1)`
block would otherwise reference two different round-`r` blocks by the same
author. That is the one place in the whole development where distinctness is
load-bearing. -/
theorem eq_of_directCommit_of_creator_eq {L₁ L₂ : BlockId} {r : ℕ}
    (h₁ : DirectCommit U L₁ r) (h₂ : DirectCommit U L₂ r)
    (hcreator : (U.block L₁).creator = (U.block L₂).creator) :
    L₁ = L₂ := by
  -- Layer 1: the two certificate quorums share a correct author, whose
  -- single round-`(r+2)` block therefore certifies both candidates.
  obtain ⟨v, hv_inter, hv_correct⟩ := exists_correct_mem_creators_inter h₁ h₂
  rw [Finset.mem_inter] at hv_inter
  obtain ⟨hv₁, hv₂⟩ := hv_inter
  rw [mem_creatorsOf] at hv₁ hv₂
  obtain ⟨C₁, hC₁, hC₁_creator⟩ := hv₁
  obtain ⟨C₂, hC₂, hC₂_creator⟩ := hv₂
  rw [certificates, Finset.mem_filter, mem_blocksAt] at hC₁ hC₂
  obtain ⟨⟨hC₁_ids, hC₁_round⟩, hC₁_cert⟩ := hC₁
  obtain ⟨⟨hC₂_ids, hC₂_round⟩, hC₂_cert⟩ := hC₂
  have hCC : C₁ = C₂ :=
    U.eq_of_creator_eq hC₁_ids hC₂_ids hv_correct hC₁_creator hC₂_creator
      (by rw [hC₁_round, hC₂_round])
  subst hCC
  -- Layer 2: that block's two vote quorums share a correct author, whose
  -- single round-`(r+1)` block therefore votes for both candidates.
  rw [Certifies] at hC₁_cert hC₂_cert
  obtain ⟨w, hw_inter, hw_correct⟩ := exists_correct_mem_creators_inter hC₁_cert hC₂_cert
  rw [Finset.mem_inter] at hw_inter
  obtain ⟨hw₁, hw₂⟩ := hw_inter
  rw [mem_creatorsOf] at hw₁ hw₂
  obtain ⟨q₁, hq₁, hq₁_creator⟩ := hw₁
  obtain ⟨q₂, hq₂, hq₂_creator⟩ := hw₂
  rw [Finset.mem_filter] at hq₁ hq₂
  obtain ⟨hq₁_mem, hq₁_ref⟩ := hq₁
  obtain ⟨hq₂_mem, hq₂_ref⟩ := hq₂
  have hq₁_ids : q₁ ∈ U.ids := U.complete _ hC₁_ids _ hq₁_mem
  have hq₂_ids : q₂ ∈ U.ids := U.complete _ hC₁_ids _ hq₂_mem
  have hq₁_round := U.round_of_mem_refs hC₁_ids hq₁_mem
  have hq₂_round := U.round_of_mem_refs hC₁_ids hq₂_mem
  have hqq : q₁ = q₂ :=
    U.eq_of_creator_eq hq₁_ids hq₂_ids hw_correct hq₁_creator hq₂_creator (by omega)
  subst hqq
  -- Both candidates are references of one block, by one author: distinctness.
  exact (U.valid q₁ hq₁_ids).distinct_creators L₁ hq₁_ref L₂ hq₂_ref hcreator

end LeanDag
