import LeanDag.CausalHistory

/-!
# Support and coverage

The common foundation under both persistence (T3) and the common-ancestor
result (T3c). Both rest on one principle:

> If a block is referenced by the round-`(r+1)` blocks of enough **correct**
> validators, every round-`(r+2)` block reaches it.

"Enough" admits two thresholds, and the difference is the only thing
separating the two theorems downstream.

* `reaches_of_correct_support` — threshold `p - 2f`, where `p` is the number
  of validators holding a round-`(r+1)` block. A round-`(r+2)` block draws
  its n−f referenced creators from those same `p`, so it misses exactly
  `p - (n−f)` of them and cannot dodge `p + f + 1 - n` supporters.

* `reaches_of_correct_support_of_card` — threshold `f+1`, uniform. Since
  `p ≤ n` always, this is the corollary: a round-`(r+2)` block names n−f
  of the `n` validators, so it misses at most `f`.

The `f+1` form is the one to reach for when supporters are *assumed* (T3
gets them free: a quorum of n−f distinct creators contains at least `f+1`
correct ones). The `p` form is needed when supporters are *counted* (T3a can
only guarantee `p - 2f`, which is strictly less than `f+1` when `p < 3f+1`).

The two agree: `p - 2f` is `f+1` net of the validators that never produced a
round-`(r+1)` block. Absentees shrink the requirement exactly as fast as they
shrink what counting can deliver, which is why no progress assumption
appears anywhere.

Correctness of the *supporters* is what makes this work: a correct validator
has one round-`(r+1)` block, so naming it is enough to reach what it
references. A Byzantine supporter could hold two, only one of which
references the target.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The ids present at a given round. -/
def blocksAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  U.ids.filter (fun i => (U.block i).round = n)

/-- The validators holding a block at a given round — the pool `p`. -/
def authorsAt (U : BlockUniverse Validator BlockId Payload) (n : ℕ) : Finset Validator :=
  creatorsOf U.block (blocksAt U n)

@[simp]
theorem mem_blocksAt {i : BlockId} {n : ℕ} :
    i ∈ blocksAt U n ↔ i ∈ U.ids ∧ (U.block i).round = n := by
  simp [blocksAt]

theorem mem_authorsAt {v : Validator} {n : ℕ} :
    v ∈ authorsAt U n ↔ ∃ i ∈ U.ids, (U.block i).round = n ∧ (U.block i).creator = v := by
  simp [authorsAt, mem_creatorsOf]
  tauto

/-- The author pool never exceeds the validator set. This is what turns the
`p - 2f` threshold into the uniform `f+1` one. -/
theorem card_authorsAt_le_univ {n : ℕ} : (authorsAt U n).card ≤ Fintype.card Validator := by
  have h := Finset.card_le_univ (authorsAt U n)
  have := F.card_validators
  omega

/-- The creators of a round-`(n+1)` block's references all hold round-`n`
blocks. This is what confines a round-`(r+2)` block's choices to the same
pool the threshold is measured against. -/
theorem creators_refs_subset_authorsAt {c : BlockId} {n : ℕ}
    (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    creatorsOf U.block (U.block c).refs ⊆ authorsAt U n := by
  intro v hv
  rw [mem_creatorsOf] at hv
  obtain ⟨i, hi_mem, hi_creator⟩ := hv
  rw [mem_authorsAt]
  refine ⟨i, U.complete c hc i hi_mem, ?_, hi_creator⟩
  have := U.round_of_mem_refs hc hi_mem
  omega

/-- **The hitting lemma.** A round-`(n+1)` block cannot avoid referencing a
block satisfying `P`, once `f+1`-or-so *correct* validators have published
round-`n` blocks satisfying it.

This is the primitive under both coverage and M2. It is stated with `P` a
bare predicate rather than a `Finset BlockId` because nothing here takes the
cardinality of the target set — only of `T`, the validators backing it —
which keeps the whole file free of `DecidableEq BlockId`.

The threshold is participation-sensitive: `c` draws its `n - f` referenced
creators from the round-`n` author pool `p`, so it misses at most
`p - (n - f)` of them and cannot dodge `p + f + 1 - n` backers. At
`n = 3f+1` this is the familiar `p - 2f`. -/
theorem exists_mem_refs_of_correct_support
    {P : BlockId → Prop} {n : ℕ} {T : Finset Validator}
    (hT : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = n ∧ P q ∧ (U.block q).creator = v)
    (hT_correct : ∀ v ∈ T, v ∈ (Correct : Finset Validator))
    (hp : (authorsAt U n).card + F.f + 1 ≤ T.card + Fintype.card Validator)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    ∃ q ∈ (U.block c).refs, P q := by
  set A := creatorsOf U.block (U.block c).refs with hA
  have hA_quorum : (Fintype.card Validator - F.f) ≤ A.card := U.creators_quorum hc (by omega)
  have hA_sub : A ⊆ authorsAt U n := creators_refs_subset_authorsAt hc hcr
  have hT_auth : T ⊆ authorsAt U n := by
    intro v hv
    obtain ⟨q, hq_ids, hq_round, _, hq_creator⟩ := hT v hv
    rw [mem_authorsAt]
    exact ⟨q, hq_ids, hq_round, hq_creator⟩
  have hunion : (A ∪ T).card ≤ (authorsAt U n).card :=
    Finset.card_le_card (Finset.union_subset hA_sub hT_auth)
  have hadd := Finset.card_union_add_card_inter A T
  have hinter : 0 < (A ∩ T).card := by
    have := F.card_validators
    omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hinter
  rw [Finset.mem_inter] at hv
  obtain ⟨hv_A, hv_T⟩ := hv
  rw [hA, mem_creatorsOf] at hv_A
  obtain ⟨i, hi_mem, hi_creator⟩ := hv_A
  obtain ⟨q, hq_ids, hq_round, hq_P, hq_creator⟩ := hT v hv_T
  have hi_ids : i ∈ U.ids := U.complete c hc i hi_mem
  have hi_round : (U.block i).round = n := by
    have := U.round_of_mem_refs hc hi_mem
    omega
  have hiq : i = q :=
    U.eq_of_creator_eq hi_ids hq_ids (hT_correct v hv_T) hi_creator hq_creator
      (by rw [hi_round, hq_round])
  exact ⟨i, hi_mem, hiq ▸ hq_P⟩

/-- **The hitting lemma, uniform form.** `f+1` correct backers always
suffice: a round-`(n+1)` block names `n - f` of at most `n` participating
authors, so it misses at most `f`. -/
theorem exists_mem_refs_of_correct_support_of_card
    {P : BlockId → Prop} {n : ℕ} {T : Finset Validator}
    (hT : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = n ∧ P q ∧ (U.block q).creator = v)
    (hT_correct : ∀ v ∈ T, v ∈ (Correct : Finset Validator))
    (hcard : F.f + 1 ≤ T.card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    ∃ q ∈ (U.block c).refs, P q := by
  refine exists_mem_refs_of_correct_support hT hT_correct ?_ hc hcr
  have := card_authorsAt_le_univ (U := U) (n := n)
  omega

/-- **Propagation.** Reaching something is inherited upward: if every block
at round `N` reaches a `P`-block, so does every block above `N`.

Shared by T3 and M2, both of which are otherwise just a base case. The step
needs nothing but nonempty references and transitivity — height is carried
by `Reaches` alone. -/
theorem reaches_pred_of_round_le {P : BlockId → Prop} {N : ℕ}
    (hbase : ∀ c ∈ U.ids, (U.block c).round = N → ∃ b, P b ∧ Reaches U c b)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : N ≤ (U.block c).round) :
    ∃ b, P b ∧ Reaches U c b := by
  suffices H : ∀ m, ∀ c ∈ U.ids, (U.block c).round = m → N ≤ m → ∃ b, P b ∧ Reaches U c b by
    exact H _ c hc rfl hcr
  clear hcr hc c
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro c hc hcm hNm
    rcases eq_or_lt_of_le hNm with heq | hlt
    · exact hbase c hc (by omega)
    · obtain ⟨i, hi_mem⟩ := U.refs_nonempty hc (by omega)
      have hi_ids : i ∈ U.ids := U.complete c hc i hi_mem
      have hi_round := U.round_of_mem_refs hc hi_mem
      obtain ⟨b, hPb, hreach⟩ := ih (U.block i).round (by omega) i hi_ids rfl (by omega)
      exact ⟨b, hPb, Reaches.of_mem_refs hi_mem hreach⟩

/-- **Coverage, participation-sensitive form.** A block backed by
`p + f + 1 - n` correct round-`(r+1)` validators is reached by every
round-`(r+2)` block.

The `P`-instance of the hitting lemma where every target references `b`. -/
theorem reaches_of_correct_support
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ q ∈ U.ids,
      (U.block q).round = r + 1 ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v)
    (hS_correct : ∀ v ∈ S, v ∈ (Correct : Finset Validator))
    (hp : (authorsAt U (r + 1)).card + F.f + 1 ≤ S.card + Fintype.card Validator)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b := by
  obtain ⟨q, hq_mem, hq_ref⟩ :=
    exists_mem_refs_of_correct_support (P := fun q => b ∈ (U.block q).refs)
      hS_support hS_correct hp hc (by omega)
  exact Reaches.of_mem_refs hq_mem (Reaches.single hq_ref)

/-- **Coverage, uniform form.** `f+1` correct supporters always suffice.

This is the form to use when supporters come from a quorum rather than from
counting — see T3, where n−f distinct creators contain `f+1` correct ones
by `card_inter_correct_of_quorum`. -/
theorem reaches_of_correct_support_of_card
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ q ∈ U.ids,
      (U.block q).round = r + 1 ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v)
    (hS_correct : ∀ v ∈ S, v ∈ (Correct : Finset Validator))
    (hcard : F.f + 1 ≤ S.card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b := by
  refine reaches_of_correct_support hS_support hS_correct ?_ hc hcr
  have := card_authorsAt_le_univ (U := U) (n := r + 1)
  omega

/-! ## Support sets

The coverage lemmas above take their support set as a bare `Finset Validator`
so they stay instance-free. These are the concrete sets callers build, and
forming them needs decidable equality on ids.

Mysticeti's *voters* for a leader block are exactly `supporters` at the
following round, which is why these sit here rather than beside the counting
argument that first used them. -/

variable [DecidableEq BlockId]

/-- The validators whose round-`n` block references `b`. -/
def supporters (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((blocksAt U n).filter (fun q => b ∈ (U.block q).refs))

theorem mem_supporters {b : BlockId} {n : ℕ} {v : Validator} :
    v ∈ supporters U b n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v := by
  simp [supporters, mem_creatorsOf]
  tauto

theorem supporters_subset_authorsAt {b : BlockId} {n : ℕ} :
    supporters U b n ⊆ authorsAt U n :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-- Validators that are both correct and back `b` with their round-`n`
block. This is exactly what the coverage lemmas consume. -/
def correctSupporters (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  supporters U b n ∩ (Correct : Finset Validator)

theorem correctSupporters_subset {b : BlockId} {n : ℕ} :
    correctSupporters U b n ⊆ supporters U b n := Finset.inter_subset_left

theorem correctSupporters_correct {b : BlockId} {n : ℕ} {v : Validator}
    (hv : v ∈ correctSupporters U b n) : v ∈ (Correct : Finset Validator) :=
  Finset.mem_of_mem_inter_right hv


/-- The validators whose round-`n` block declines to reference `L`.

The complement of `supporters U L n` *within the round-`n` author pool* —
but only for correct validators. A Byzantine author can appear in both, by
publishing one round-`n` block that votes and another that does not; ruling
that out for correct validators is exactly what
`blames_inter_supporters_subset_byzantine`
does, and is the whole content of M3. -/
def blames (U : BlockUniverse Validator BlockId Payload) (L : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((blocksAt U n).filter (fun q => L ∉ (U.block q).refs))

theorem mem_blames {L : BlockId} {n : ℕ} {v : Validator} :
    v ∈ blames U L n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ L ∉ (U.block q).refs ∧ (U.block q).creator = v := by
  simp [blames, mem_creatorsOf]
  tauto

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

/-- **The counting core of M3.** A quorum of blamers caps the supporters at
`2f`, one short of a quorum.

A correct validator sits on at most one side, so the overlap is confined to
the Byzantine set: `|supporters| ≤ (3f+1) − (2f+1) + f = 2f`. Nothing about
certificates enters, which is why this belongs here rather than beside the
commit rules that consume it. -/
theorem card_supporters_le_of_card_blames {L : BlockId} {n : ℕ}
    (h : (Fintype.card Validator - F.f) ≤ (blames U L n).card) :
    (supporters U L n).card ≤ 2 * F.f := by
  have hunion : (blames U L n ∪ supporters U L n).card ≤ Fintype.card Validator := by
    have := Finset.card_le_univ (blames U L n ∪ supporters U L n)
    have := F.card_validators
    omega
  have hinter : (blames U L n ∩ supporters U L n).card ≤ F.f :=
    le_trans (Finset.card_le_card blames_inter_supporters_subset_byzantine) F.card_byzantine
  have hadd := Finset.card_union_add_card_inter (blames U L n) (supporters U L n)
  omega

end LeanDag
