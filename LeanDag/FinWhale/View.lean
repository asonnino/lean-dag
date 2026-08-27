import LeanDag.FinWhale.Decided

/-!
# FinWhale — views, and the direct rules relative to one

The safety arc took each validator's direct rules as abstract predicates,
with two conditions relating them to the universe: that a view's direct
verdict is one of the universe (`exclusions_of_dag`), and, for liveness,
that the universe's direct commit is one of the view (`hsees`). This file
replaces the abstract predicates with the rules evaluated on the
validator's own sub-DAG, and proves both conditions instead of assuming
them.

A **view** is a reference-closed subset of the universe's blocks, and it
is a `Dag` in its own right: validity and non-equivocation are inherited,
and closure is its completeness. `restrict` builds it.

Three facts make the transfer work.

**Most of the vocabulary does not read the population at all.**
`parentsVoting`, `parentSet` and `SPCertificate` are computed from a
block's references, so they are the same in a view as in the universe.

**Closure carries a block into the view whenever anything in the view
votes for it.** `mem_view_of_parentsVoting` is the immediate form, and
`mem_view_of_voters` is the counting form: a view holding a single
round-`(r+2)` block holds every block a quorum of round-`(r+1)`
validators votes for, because that block's `n − f` parents meet the
quorum in a correct author.

**And so FP-evidence is view-independent.** Its equivocation test
quantifies over the population, but the blocks it can find are voted for
by the block's own parents, hence in any view holding the block.

The skip rule is where the two directions part. Its first condition
quantifies over the slot's blocks *as the view sees them*, so a view's
skip is not a skip of the universe, and the exclusions it takes part in
have to be proved directly — `no_directSkip_of_commit_view` and
`no_indirectCommit_of_directSkip_view` below. Both run through the second
condition, the quorum of Non-FP-evidence blocks, which is what makes the
missing block visible.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload} {V : Finset BlockId}

/-- **A view**: part of the universe, closed under references. -/
structure IsView (D : Dag Validator BlockId Payload) (V : Finset BlockId) : Prop where
  /-- Only blocks that exist. -/
  subset : V ⊆ D.ids
  /-- And everything they reference. -/
  closed : ∀ i ∈ V, ∀ j ∈ (D.block i).refs, j ∈ V

/-- **A view is a DAG.** Validity and non-equivocation are inherited; the
view's completeness is its closure. -/
def restrict (D : Dag Validator BlockId Payload) (V : Finset BlockId) (hV : IsView D V) :
    Dag Validator BlockId Payload where
  ids := V
  block := D.block
  leader := D.leader
  complete := hV.closed
  valid := fun i hi => D.valid i (hV.subset hi)
  correct_single := fun i hi j hj => D.correct_single i (hV.subset hi) j (hV.subset hj)

variable {hV : IsView D V}

@[simp] theorem restrict_ids : (restrict D V hV).ids = V := rfl

@[simp] theorem restrict_block : (restrict D V hV).block = D.block := rfl

@[simp] theorem restrict_leader : (restrict D V hV).leader = D.leader := rfl

/-- The population shrinks, so a round's blocks do. -/
theorem blocksAt_restrict {r : ℕ} : blocksAt (restrict D V hV) r ⊆ blocksAt D r := by
  intro b hb
  simp only [blocksAt, restrict_ids, restrict_block, Finset.mem_filter] at hb ⊢
  exact ⟨hV.subset hb.1, hb.2⟩

/-- And so does a slot's. -/
theorem slotBlocks_restrict {r : ℕ} : slotBlocks (restrict D V hV) r ⊆ slotBlocks D r := by
  intro b hb
  simp only [slotBlocks, Finset.mem_filter] at hb ⊢
  exact ⟨blocksAt_restrict hb.1, hb.2⟩

/-- Fewer blocks, fewer voters. -/
theorem voters_restrict {l : BlockId} : voters (restrict D V hV) l ⊆ voters D l := by
  intro v hv
  simp only [voters, mem_creatorsOf, Finset.mem_filter] at hv ⊢
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  exact ⟨q, ⟨blocksAt_restrict hq, hqref⟩, hqv⟩

/-- And fewer validators declining to vote. -/
theorem nonVoters_restrict {l : BlockId} : nonVoters (restrict D V hV) l ⊆ nonVoters D l := by
  intro v hv
  simp only [nonVoters, mem_creatorsOf, Finset.mem_filter] at hv ⊢
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  exact ⟨q, ⟨blocksAt_restrict hq, hqref⟩, hqv⟩

/-- **What a block's parents say is view-independent.** -/
@[simp] theorem parentsVoting_restrict {b l : BlockId} :
    parentsVoting (restrict D V hV) b l = parentsVoting D b l := rfl

/-- So an SP-certificate is a certificate in either reading. -/
@[simp] theorem spCertificate_restrict {b l : BlockId} :
    SPCertificate (restrict D V hV) b l ↔ SPCertificate D b l := Iff.rfl

/-- **Closure, in its immediate form.** A view holding a block holds
everything the block's parents vote for. -/
theorem mem_view_of_parentsVoting (hV : IsView D V) {b l : BlockId} (hb : b ∈ V)
    (h : (parentsVoting D b l).Nonempty) : l ∈ V := by
  obtain ⟨v, hv⟩ := h
  simp only [parentsVoting, mem_creatorsOf, Finset.mem_filter] at hv
  obtain ⟨q, ⟨hq, hql⟩, -⟩ := hv
  exact hV.closed q (hV.closed b hb q hq) l hql

/-- **Closure, in its counting form.** A view holding one round-`(r+2)`
block holds every block a quorum of round-`(r+1)` validators votes for:
that block carries `n − f` parents, which meet the quorum in `f + p`
authors, one of them correct — and a correct author's round-`(r+1)` block
is one block, so the parent and the vote are the same block. -/
theorem mem_view_of_voters (hV : IsView D V) {c l : BlockId} (hc : c ∈ V)
    (hcround : (D.block c).round = (D.block l).round + 2)
    (hvote : spQuorum Validator ≤ (voters D l).card) : l ∈ V := by
  have hcids : c ∈ D.ids := hV.subset hc
  have hpar : quorumCard Validator ≤ (parentSet D c).card :=
    (D.valid c hcids).quorum (by omega)
  have hmeet := card_add_card_le_card_inter_add_card (parentSet D c) (voters D l)
  have := params_arith (Validator := Validator)
  have hcard : F.f + 1 ≤ ((parentSet D c) ∩ (voters D l)).card := by
    simp only [spQuorum] at hvote
    omega
  obtain ⟨w, hw, hwc⟩ := exists_correct_of_card hcard
  rw [Finset.mem_inter] at hw
  obtain ⟨q, hq, hqw⟩ := mem_creatorsOf.1 hw.1
  obtain ⟨q', hq', hq'w⟩ := mem_creatorsOf.1 hw.2
  rw [Finset.mem_filter] at hq'
  simp only [blocksAt, Finset.mem_filter] at hq'
  have hqids : q ∈ D.ids := D.complete c hcids q hq
  have hqround : (D.block q).round = (D.block l).round + 1 := by
    have := parent_round hcids hq; omega
  have heq : q = q' :=
    D.correct_single q hqids q' hq'.1.1 (by rw [hqw]; exact hwc) (by rw [hqw, hq'w])
      (by rw [hqround, hq'.1.2])
  exact hV.closed q (hV.closed c hc q hq) l (heq ▸ hq'.2)

/-- **Exposing an equivocation is view-independent**, for a block the view
holds: the conflicting versions it finds are voted for by the block's own
parents, so closure puts them in the view. -/
theorem exposes_restrict {b : BlockId} (hb : b ∈ V) :
    ExposesEquivocation (restrict D V hV) b ↔ ExposesEquivocation D b := by
  constructor
  · rintro ⟨l, hl, l', hl', hconf, hlead, h1, h2⟩
    exact ⟨l, hV.subset hl, l', hV.subset hl', hconf, hlead, h1, h2⟩
  · rintro ⟨l, -, l', -, hconf, hlead, h1, h2⟩
    exact ⟨l, mem_view_of_parentsVoting hV hb h1, l',
      mem_view_of_parentsVoting hV hb h2, hconf, hlead, h1, h2⟩

/-- **FP-evidence is view-independent** for a block the view holds. The
equivocating branch bounds the parents voting for anything conflicting;
a conflicting block outside the view has no such parents, and the bound
holds of it for nothing. -/
theorem fpEvidence_restrict {b l : BlockId} (hb : b ∈ V) :
    FPEvidence (restrict D V hV) b l ↔ FPEvidence D b l := by
  have := params_arith (Validator := Validator)
  simp only [FPEvidence, parentsVoting_restrict]
  by_cases hexp : ExposesEquivocation D b
  · rw [if_pos ((exposes_restrict hb).2 hexp), if_pos hexp]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun l' _ hconf => ?_⟩
      rcases Finset.eq_empty_or_nonempty (parentsVoting D b l') with he | hne
      · rw [he]; simp; omega
      · exact h2 l' (mem_view_of_parentsVoting hV hb hne) hconf
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun l' hl' hconf => h2 l' (hV.subset hl') hconf⟩
  · rw [if_neg fun h => hexp ((exposes_restrict hb).1 h), if_neg hexp]

/-- Every FP-evidence block has a parent voting for what it is evidence
for: both branches ask for at least `f + p − 1 ≥ 1`. -/
theorem parentsVoting_nonempty_of_fpEvidence {b l : BlockId} (h : FPEvidence D b l) :
    (parentsVoting D b l).Nonempty := by
  have := params_arith (Validator := Validator)
  rw [← Finset.card_pos]
  simp only [FPEvidence] at h
  by_cases hexp : ExposesEquivocation D b
  · rw [if_pos hexp] at h; omega
  · rw [if_neg hexp] at h; omega

/-! ## The direct rules, in both directions -/

/-- A view's fast commit is one of the universe. -/
theorem fastCommit_restrict {l : BlockId} (h : FastCommit (restrict D V hV) l) :
    FastCommit D l :=
  le_trans h (Finset.card_le_card voters_restrict)

/-- And its slow commit. -/
theorem spCommit_restrict {l : BlockId} (h : SPCommit (restrict D V hV) l) : SPCommit D l := by
  obtain ⟨certs, hcard, hcerts⟩ := h
  refine ⟨certs, hcard, fun v hv => ?_⟩
  obtain ⟨b, hb, hbv, hbcert⟩ := hcerts v hv
  exact ⟨b, blocksAt_restrict hb, hbv, hbcert⟩

/-- So its direct commit is one of the universe: the condition safety
took as a hypothesis. -/
theorem directCommit_restrict {l : BlockId} (h : DirectCommit (restrict D V hV) l) :
    DirectCommit D l :=
  h.imp fastCommit_restrict spCommit_restrict

/-- A view's SP-skip is one of the universe: it counts validators
declining to vote, and the view has fewer of them. -/
theorem spSkip_restrict {l : BlockId} (h : SPSkip (restrict D V hV) l) : SPSkip D l :=
  le_trans h (Finset.card_le_card nonVoters_restrict)

/-- Where the view holds a whole round, it counts the same voters. -/
theorem voters_restrict_eq {l : BlockId}
    (hV1 : blocksAt D ((D.block l).round + 1) ⊆ V) :
    voters (restrict D V hV) l = voters D l := by
  refine Finset.Subset.antisymm voters_restrict fun v hv => ?_
  simp only [voters, mem_creatorsOf, Finset.mem_filter] at hv ⊢
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  refine ⟨q, ⟨?_, hqref⟩, hqv⟩
  simp only [blocksAt, restrict_ids, restrict_block, Finset.mem_filter]
  simp only [blocksAt, Finset.mem_filter] at hq
  exact ⟨hV1 (by simp only [blocksAt, Finset.mem_filter]; exact hq), hq.2⟩

/-- **The liveness direction, fast path.** A view holding round `r + 1`
sees the fast commit the universe sees. -/
theorem fastCommit_of_holds {l : BlockId}
    (hV1 : blocksAt D ((D.block l).round + 1) ⊆ V) (h : FastCommit D l) :
    FastCommit (restrict D V hV) l := by
  change fastCard Validator ≤ (voters (restrict D V hV) l).card
  rw [voters_restrict_eq hV1]
  exact h

/-- **And the slow path**, for a view holding round `r + 2`. -/
theorem spCommit_of_holds {l : BlockId}
    (hV2 : blocksAt D ((D.block l).round + 2) ⊆ V) (h : SPCommit D l) :
    SPCommit (restrict D V hV) l := by
  obtain ⟨certs, hcard, hcerts⟩ := h
  refine ⟨certs, hcard, fun v hv => ?_⟩
  obtain ⟨b, hb, hbv, hbcert⟩ := hcerts v hv
  refine ⟨b, ?_, hbv, hbcert⟩
  simp only [blocksAt, restrict_ids, restrict_block, Finset.mem_filter]
  simp only [blocksAt, Finset.mem_filter] at hb
  exact ⟨hV2 (by simp only [blocksAt, Finset.mem_filter]; exact hb), hb.2⟩

/-- **`hsees`, discharged.** A view holding the two rounds above a slot
sees whatever direct commit the universe has there. -/
theorem directCommit_of_holds {l : BlockId}
    (hV1 : blocksAt D ((D.block l).round + 1) ⊆ V)
    (hV2 : blocksAt D ((D.block l).round + 2) ⊆ V) (h : DirectCommit D l) :
    DirectCommit (restrict D V hV) l :=
  h.imp (fastCommit_of_holds hV1) (spCommit_of_holds hV2)

/-! ## The two exclusions the skip rule needs

A view's direct skip is *not* a direct skip of the universe: its first
condition quantifies over the slot blocks the view holds, and a view
holding none of them satisfies it for nothing. Both exclusions therefore
run through the second condition, the quorum of Non-FP-evidence blocks —
which is also what forces the committed block into the view. -/

/-- **A view's direct skip is incompatible with a direct commit.** The
skip carries a quorum of round-`(r+2)` blocks, and a single one of them
already puts the committed block in the view; then either Lemma 4 or
Lemma 2 makes one of those blocks FP-evidence for it, which is what
Non-FP-evidence denies. -/
theorem no_directSkip_of_commit_view {r : ℕ} {l : BlockId}
    (hl : l ∈ slotBlocks D r) (hcom : DirectCommit D l) :
    ¬ DirectSkip (restrict D V hV) r := by
  rintro ⟨-, nonev, hnon, hnonb⟩
  have hlu : l ∈ D.ids ∧ (D.block l).round = r ∧ (D.block l).creator = D.leader r := by
    simp only [slotBlocks, blocksAt, Finset.mem_filter] at hl
    exact ⟨hl.1.1, hl.1.2, hl.2⟩
  have hvote := voters_of_directCommit hcom
  have harith := params_arith (Validator := Validator)
  have hpos : 0 < nonev.card := by simp only [spQuorum] at hnon; omega
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.1 hpos
  obtain ⟨b₀, hb₀, -, hnonfp₀⟩ := hnonb v₀ hv₀
  have hb₀V : b₀ ∈ V := by
    simp only [blocksAt, restrict_ids, Finset.mem_filter] at hb₀; exact hb₀.1
  have hb₀round : (D.block b₀).round = r + 2 := by
    simp only [blocksAt, restrict_block, Finset.mem_filter] at hb₀; exact hb₀.2
  -- the committed block is in the view, whatever the view had seen of the slot
  have hlV : l ∈ V := mem_view_of_voters hV hb₀V (by rw [hb₀round, hlu.2.1]) hvote
  have hlslot : l ∈ slotBlocks (restrict D V hV) r := by
    simp only [slotBlocks, blocksAt, restrict_ids, restrict_block, restrict_leader,
      Finset.mem_filter]
    exact ⟨⟨hlV, hlu.2.1⟩, hlu.2.2⟩
  rcases hcom with hfast | ⟨certs, hcerts, hcertb⟩
  · -- under a fast commit every round-`(r+2)` block is evidence (Lemma 4)
    have hfp : FPEvidence D b₀ l :=
      lemma4 (hV.subset hb₀V) hlu.1 (by rw [hb₀round, hlu.2.1]) hfast
    exact hnonfp₀ l hlslot ((fpEvidence_restrict hb₀V).2 hfp)
  · -- under a slow commit the two quorums meet in a correct author
    have hmeet := card_add_card_le_card_inter_add_card certs nonev
    have hcard : F.f + 1 ≤ (certs ∩ nonev).card := by
      simp only [spQuorum] at hcerts hnon; omega
    obtain ⟨w, hw, hwc⟩ := exists_correct_of_card hcard
    rw [Finset.mem_inter] at hw
    obtain ⟨c₁, hc₁, hc₁w, hc₁cert⟩ := hcertb w hw.1
    obtain ⟨c₂, hc₂, hc₂w, hnonfp⟩ := hnonb w hw.2
    replace hc₂w : (D.block c₂).creator = w := hc₂w
    simp only [blocksAt, Finset.mem_filter] at hc₁
    have hc₂V : c₂ ∈ V := by
      simp only [blocksAt, restrict_ids, Finset.mem_filter] at hc₂; exact hc₂.1
    have hc₂round : (D.block c₂).round = r + 2 := by
      simp only [blocksAt, restrict_block, Finset.mem_filter] at hc₂; exact hc₂.2
    have heq : c₁ = c₂ :=
      D.correct_single c₁ hc₁.1 c₂ (hV.subset hc₂V) (by rw [hc₁w]; exact hwc)
        (by rw [hc₁w, hc₂w]) (by rw [hc₁.2, hc₂round, hlu.2.1])
    exact hnonfp l hlslot ((fpEvidence_restrict hc₂V).2 (heq ▸ lemma2 hc₁.1 hc₁cert))

/-- **A view's direct skip is incompatible with an indirect commit.**
Either route puts the candidate in the view — an SP-certificate through
the voter count, a quorum of evidence through the author the two quorums
share — and then the skip's own conditions deny it. -/
theorem no_indirectCommit_of_directSkip_view {A : BlockId} {r : ℕ} {b : BlockId}
    (hskip : DirectSkip (restrict D V hV) r) : ¬ IndirectCommit D A r b := by
  obtain ⟨hsp, nonev, hnon, hnonb⟩ := hskip
  rintro ⟨hbslot, hroute⟩
  have harith := params_arith (Validator := Validator)
  have hbu : b ∈ D.ids ∧ (D.block b).round = r ∧ (D.block b).creator = D.leader r := by
    simp only [slotBlocks, blocksAt, Finset.mem_filter] at hbslot
    exact ⟨hbslot.1.1, hbslot.1.2, hbslot.2⟩
  have hpos : 0 < nonev.card := by simp only [spQuorum] at hnon; omega
  obtain ⟨v₀, hv₀⟩ := Finset.card_pos.1 hpos
  obtain ⟨b₀, hb₀, -, -⟩ := hnonb v₀ hv₀
  have hb₀V : b₀ ∈ V := by
    simp only [blocksAt, restrict_ids, Finset.mem_filter] at hb₀; exact hb₀.1
  have hb₀round : (D.block b₀).round = r + 2 := by
    simp only [blocksAt, restrict_block, Finset.mem_filter] at hb₀; exact hb₀.2
  -- the candidate is in the view, and so the slot's blocks include it
  have hin : b ∈ V → False := by
    intro hbV
    have hbslotV : b ∈ slotBlocks (restrict D V hV) r := by
      simp only [slotBlocks, blocksAt, restrict_ids, restrict_block, restrict_leader,
        Finset.mem_filter]
      exact ⟨⟨hbV, hbu.2.1⟩, hbu.2.2⟩
    rcases hroute with ⟨c, hc, -, hcert⟩ | ⟨ev, hev, hevb⟩
    · simp only [blocksAt, Finset.mem_filter] at hc
      exact no_skip_of_quorum
        (voters_of_spCertificate hc.1 (by rw [hc.2, hbu.2.1]) hcert)
        (spSkip_restrict (hsp b hbslotV))
    · have hmeet := card_add_card_le_card_inter_add_card ev nonev
      have hcard : F.f + 1 ≤ (ev ∩ nonev).card := by
        simp only [spQuorum] at hev hnon; omega
      obtain ⟨w, hw, hwc⟩ := exists_correct_of_card hcard
      rw [Finset.mem_inter] at hw
      obtain ⟨c₁, hc₁, -, hc₁w, hc₁fp⟩ := hevb w hw.1
      obtain ⟨c₂, hc₂, hc₂w, hnonfp⟩ := hnonb w hw.2
      replace hc₂w : (D.block c₂).creator = w := hc₂w
      simp only [blocksAt, Finset.mem_filter] at hc₁
      have hc₂V : c₂ ∈ V := by
        simp only [blocksAt, restrict_ids, Finset.mem_filter] at hc₂; exact hc₂.1
      have hc₂round : (D.block c₂).round = r + 2 := by
        simp only [blocksAt, restrict_block, Finset.mem_filter] at hc₂; exact hc₂.2
      have heq : c₁ = c₂ :=
        D.correct_single c₁ hc₁.1 c₂ (hV.subset hc₂V) (by rw [hc₁w]; exact hwc)
          (by rw [hc₁w, hc₂w]) (by rw [hc₁.2, hc₂round])
      exact hnonfp b hbslotV ((fpEvidence_restrict hc₂V).2 (heq ▸ hc₁fp))
  -- and it is: either route exhibits a quorum behind `b`
  refine hin ?_
  rcases hroute with ⟨c, hc, -, hcert⟩ | ⟨ev, hev, hevb⟩
  · simp only [blocksAt, Finset.mem_filter] at hc
    exact mem_view_of_voters hV hb₀V (by rw [hb₀round, hbu.2.1])
      (voters_of_spCertificate hc.1 (by rw [hc.2, hbu.2.1]) hcert)
  · have hevpos : 0 < ev.card := by simp only [spQuorum] at hev; omega
    obtain ⟨w, hw⟩ := Finset.card_pos.1 hevpos
    obtain ⟨c, hc, -, -, hcfp⟩ := hevb w hw
    have hmeet := card_add_card_le_card_inter_add_card ev nonev
    have hcard : F.f + 1 ≤ (ev ∩ nonev).card := by
      simp only [spQuorum] at hev hnon; omega
    obtain ⟨w', hw', hw'c⟩ := exists_correct_of_card hcard
    rw [Finset.mem_inter] at hw'
    obtain ⟨c₁, hc₁, -, hc₁w, hc₁fp⟩ := hevb w' hw'.1
    obtain ⟨c₂, hc₂, hc₂w, -⟩ := hnonb w' hw'.2
    replace hc₂w : (D.block c₂).creator = w' := hc₂w
    simp only [blocksAt, Finset.mem_filter] at hc₁
    have hc₂V : c₂ ∈ V := by
      simp only [blocksAt, restrict_ids, Finset.mem_filter] at hc₂; exact hc₂.1
    have hc₂round : (D.block c₂).round = r + 2 := by
      simp only [blocksAt, restrict_block, Finset.mem_filter] at hc₂; exact hc₂.2
    have heq : c₁ = c₂ :=
      D.correct_single c₁ hc₁.1 c₂ (hV.subset hc₂V) (by rw [hc₁w]; exact hw'c)
        (by rw [hc₁w, hc₂w]) (by rw [hc₁.2, hc₂round])
    exact mem_view_of_parentsVoting hV (heq ▸ hc₂V)
      (parentsVoting_nonempty_of_fpEvidence hc₁fp)

/-! ## The exclusions, on two views -/

/-- The direct commit rule as a validator with view `V` evaluates it. -/
def viewCommit (D : Dag Validator BlockId Payload) (V : Finset BlockId) (hV : IsView D V)
    (r : ℕ) (l : BlockId) : Prop :=
  l ∈ slotBlocks (restrict D V hV) r ∧ DirectCommit (restrict D V hV) l

/-- And the direct skip rule. -/
def viewSkip (D : Dag Validator BlockId Payload) (V : Finset BlockId) (hV : IsView D V)
    (r : ℕ) : Prop :=
  DirectSkip (restrict D V hV) r

/-- **Lemma 12's side conditions, on two views of one DAG.** Nothing is
assumed about how the views relate to the universe beyond their being
views: the direct rules are evaluated on them, and every field is a
theorem about that. -/
theorem exclusions_of_views {V V' : Finset BlockId} (hV : IsView D V) (hV' : IsView D V')
    {choose : BlockId → ℕ → Option BlockId} (hch : ChooseSound D choose) :
    Exclusions (viewCommit D V hV) (viewCommit D V' hV') (viewSkip D V hV) (viewSkip D V' hV')
      choose (fun r A => A ∈ D.ids ∧ r + 3 ≤ (D.block A).round) := by
  have hconf : ∀ (r : ℕ) (l b : BlockId), l ∈ slotBlocks D r → b ∈ slotBlocks D r → l ≠ b →
      Conflicting D l b ∧ l ∈ D.ids ∧ b ∈ D.ids ∧ (D.block l).creator = D.leader r := by
    intro r l b hl hb hne
    simp only [slotBlocks, blocksAt, Finset.mem_filter] at hl hb
    exact ⟨⟨hne, by rw [hl.1.2, hb.1.2], by rw [hl.2, hb.2]⟩, hl.1.1, hb.1.1, hl.2⟩
  refine
    { commit_unique := fun r l l' ⟨hs, hc⟩ ⟨hs', hc'⟩ =>
        direct_commit_unique (slotBlocks_restrict hs) (slotBlocks_restrict hs')
          (directCommit_restrict hc) (directCommit_restrict hc')
      commit_bars_skip := fun r l ⟨hs, hc⟩ =>
        no_directSkip_of_commit_view (slotBlocks_restrict hs) (directCommit_restrict hc)
      commit_bars_skip' := fun r l ⟨hs, hc⟩ =>
        no_directSkip_of_commit_view (slotBlocks_restrict hs) (directCommit_restrict hc)
      commit_forces_choose := fun r l A hA ⟨hs, hc⟩ =>
        hch.total A r ⟨l, indirectCommit_of_directCommit hA.1 hA.2 (slotBlocks_restrict hs)
          (directCommit_restrict hc)⟩
      commit_forces_choose' := fun r l A hA ⟨hs, hc⟩ =>
        hch.total A r ⟨l, indirectCommit_of_directCommit hA.1 hA.2 (slotBlocks_restrict hs)
          (directCommit_restrict hc)⟩
      skip_bars_choose := fun r A b hs hchb =>
        no_indirectCommit_of_directSkip_view hs (hch.sound A r b hchb)
      skip_bars_choose' := fun r A b hs hchb =>
        no_indirectCommit_of_directSkip_view hs (hch.sound A r b hchb)
      commit_pins_choose := ?_
      commit_pins_choose' := ?_ } <;>
  · intro r l A b h hchb
    by_contra hne
    obtain ⟨hs, hc⟩ := h
    have hlslot := slotBlocks_restrict hs
    have hcom := directCommit_restrict hc
    have hind := hch.sound A r b hchb
    obtain ⟨hcf, hlids, hbids, hlead⟩ := hconf r l b hlslot hind.1 (Ne.symm hne)
    exact no_indirectCommit_of_directCommit hlids hbids hlslot hlead hcf hcom hind

/-! ## The capstones, with the views supplied

`safety` and the liveness results were stated with the view conditions as
hypotheses. Here they are again with views in place of them: what is
assumed is that each validator follows the reverse pass on its own view,
and — for liveness — that its view holds the blocks up to the horizon,
which is what catching up means. -/

/-- **Safety, on two views.** Two validators running the reverse pass on
their own views of one DAG deliver prefix-comparable sequences. -/
theorem safety_of_views {V V' : Finset BlockId} (hV : IsView D V) (hV' : IsView D V')
    {choose : BlockId → ℕ → Option BlockId} {dec dec' : ℕ → Verdict BlockId}
    (hwf : WellFormed (viewCommit D V hV) (viewSkip D V hV) choose dec)
    (hwf' : WellFormed (viewCommit D V' hV') (viewSkip D V' hV') choose dec')
    (hch : ChooseSound D choose)
    (hslot : ∀ r A, dec r = Verdict.commit A → A ∈ slotBlocks D r)
    (hslot' : ∀ r A, dec' r = Verdict.commit A → A ∈ slotBlocks D r)
    {N : ℕ} (hbound : ∀ s, N ≤ s → dec s = Verdict.undecided ∧ dec' s = Verdict.undecided)
    {k k' : ℕ} (hk : ∀ s, s < k → dec s ≠ Verdict.undecided)
    (hk' : ∀ s, s < k' → dec' s ≠ Verdict.undecided)
    (hist : BlockId → List BlockId) :
    linearise hist (commitSeq dec k) <+: linearise hist (commitSeq dec' k') ∨
      linearise hist (commitSeq dec' k') <+: linearise hist (commitSeq dec k) := by
  have habove : ∀ (dq : ℕ → Verdict BlockId),
      (∀ r A, dq r = Verdict.commit A → A ∈ slotBlocks D r) →
      ∀ r a A, r + 2 < a → dq a = Verdict.commit A → A ∈ D.ids ∧ r + 3 ≤ (D.block A).round := by
    intro dq hq r a A hra hcom
    have hA := hq a A hcom
    simp only [slotBlocks, blocksAt, Finset.mem_filter] at hA
    exact ⟨hA.1.1, by omega⟩
  rcases lemma13 (lemma12 hwf hwf' (exclusions_of_views hV hV' hch)
      (habove dec hslot) (habove dec' hslot') hbound) hk hk' with h | h
  · exact Or.inl (theorem14 hist h)
  · exact Or.inr (theorem14 hist h)

/-- **A view holding the reliable blocks sees the commits.** The liveness
interface names its certificates as reliable validators' blocks, and a
view holds those; the leader's own block is reliable too, the slot being
correct-led. Nothing is asked of the view about Byzantine authors, which
is as much as a schedule can give. -/
theorem sees_of_commits_of_held {V : Finset BlockId} (hV : IsView D V) {R N : ℕ}
    (hcommits : CommitsCorrectLeaders D R N)
    (hheld : ∀ n, R ≤ n → n ≤ N → ∀ b ∈ blocksAt D n,
      (D.block b).creator ∈ (Correct : Finset Validator) → b ∈ V) :
    SeesCommits D (viewCommit D V hV) R N := by
  intro s hR hN hlead
  obtain ⟨l, hslot, certs, hsub, hcard, hcertb⟩ := hcommits s hR hN hlead
  have hlu : l ∈ blocksAt D s ∧ (D.block l).creator = D.leader s := by
    simp only [slotBlocks, Finset.mem_filter] at hslot
    exact hslot
  have hlround : (D.block l).round = s := by
    simp only [blocksAt, Finset.mem_filter] at hlu
    exact hlu.1.2
  have hlV : l ∈ V := hheld s hR (by omega) l hlu.1 (by rw [hlu.2]; exact hlead)
  refine ⟨l, hslot, ?_, Or.inr ⟨certs, hcard, fun v hv => ?_⟩⟩
  · simp only [slotBlocks, blocksAt, restrict_ids, restrict_block, restrict_leader,
      Finset.mem_filter]
    exact ⟨⟨hlV, hlround⟩, hlu.2⟩
  · obtain ⟨b, hb, hbc, hcert⟩ := hcertb v hv
    have hbV : b ∈ V :=
      hheld ((D.block l).round + 2) (by omega) (by omega) b hb (by rw [hbc]; exact hsub hv)
    refine ⟨b, ?_, hbc, hcert⟩
    simp only [blocksAt, restrict_ids, restrict_block, Finset.mem_filter]
    simp only [blocksAt, Finset.mem_filter] at hb
    exact ⟨hbV, hb.2⟩

/-- **Lemma 23, on a view.** A validator whose view holds the blocks up
to the horizon decides every slot below it. `hsees` is discharged by
`directCommit_of_holds`: holding the two rounds above a slot is seeing
whatever direct commit is there. -/
theorem all_decided_of_view {V : Finset BlockId} (hV : IsView D V)
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed (viewCommit D V hV) (viewSkip D V hV) choose dec) {R N r : ℕ}
    (hheld : ∀ n, R ≤ n → n ≤ N → ∀ b ∈ blocksAt D n,
      (D.block b).creator ∈ (Correct : Finset Validator) → b ∈ V)
    (hcommits : CommitsCorrectLeaders D R N)
    (hrr : RoundRobin D.leader) (hN : max r R + (3 * F.f + 5) ≤ N) :
    dec r ≠ Verdict.undecided :=
  all_decided hwf (sees_of_commits_of_held hV hcommits hheld) hrr hN

/-- **Theorem 24, on two views.** Two validators that have caught up to
the horizon deliver the same sequence. -/
theorem agreement_of_views {V V' : Finset BlockId} (hV : IsView D V) (hV' : IsView D V')
    {choose : BlockId → ℕ → Option BlockId} {dec dec' : ℕ → Verdict BlockId}
    (hwf : WellFormed (viewCommit D V hV) (viewSkip D V hV) choose dec)
    (hwf' : WellFormed (viewCommit D V' hV') (viewSkip D V' hV') choose dec')
    (hch : ChooseSound D choose)
    (hslot : ∀ r A, dec r = Verdict.commit A → A ∈ slotBlocks D r)
    (hslot' : ∀ r A, dec' r = Verdict.commit A → A ∈ slotBlocks D r)
    {M : ℕ} (hbound : ∀ s, M ≤ s → dec s = Verdict.undecided ∧ dec' s = Verdict.undecided)
    {R N k : ℕ}
    (hheld : ∀ n, R ≤ n → n ≤ N → ∀ b ∈ blocksAt D n,
      (D.block b).creator ∈ (Correct : Finset Validator) → b ∈ V)
    (hheld' : ∀ n, R ≤ n → n ≤ N → ∀ b ∈ blocksAt D n,
      (D.block b).creator ∈ (Correct : Finset Validator) → b ∈ V')
    (hcommits : CommitsCorrectLeaders D R N)
    (hrr : RoundRobin D.leader) (hkN : max k R + (3 * F.f + 5) ≤ N)
    (hist : BlockId → List BlockId) :
    linearise hist (commitSeq dec k) = linearise hist (commitSeq dec' k) := by
  have habove : ∀ (dq : ℕ → Verdict BlockId),
      (∀ r A, dq r = Verdict.commit A → A ∈ slotBlocks D r) →
      ∀ r a A, r + 2 < a → dq a = Verdict.commit A → A ∈ D.ids ∧ r + 3 ≤ (D.block A).round := by
    intro dq hq r a A hra hcom
    have hA := hq a A hcom
    simp only [slotBlocks, blocksAt, Finset.mem_filter] at hA
    exact ⟨hA.1.1, by omega⟩
  refine theorem24
    (lemma12 hwf hwf' (exclusions_of_views hV hV' hch)
      (habove dec hslot) (habove dec' hslot') hbound)
    (fun s hs => all_decided_of_view hV hwf hheld hcommits hrr (by
      have : max s R ≤ max k R := max_le_max (by omega) le_rfl
      omega))
    (fun s hs => all_decided_of_view hV' hwf' hheld' hcommits hrr (by
      have : max s R ≤ max k R := max_le_max (by omega) le_rfl
      omega))
    hist

end FinWhale

end LeanDag
