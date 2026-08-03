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

end LeanDag
