import LeanDag.Nemo.History

/-!
# Nemo-Nemo: support and coverage

The crash port of `LeanDag/Support.lean`. Both persistence and the
common-ancestor result rest on one principle:

> If a block is referenced by the round-`(r+1)` blocks of enough validators,
> every round-`(r+2)` block reaches it.

The Byzantine core measures "enough" against the `n − f` quorum and filters the
supporters through the `Correct` set. Under crash *every* validator is honest,
so both simplifications collapse into one: the quorum is a bare **majority**
`n/2+1`, and there is no correctness filtering — a supporter has a single
round-`(r+1)` block (`no_equivocation` is universal), so naming it is enough to
reach what it references. The single quorum fact is that two majorities
intersect (`exists_mem_inter`).

"Enough" still admits two thresholds:

* the participation-sensitive form, threshold `authorsAt.card < S.card +
  majority` — a round-`(r+2)` block draws a majority of its referenced creators
  from the round-`(r+1)` author pool, so it cannot dodge every supporter;
* the uniform form, threshold `majority ≤ S.card` — since the pool never
  exceeds `n`, a majority of supporters and a majority of referenced authors
  must meet (`exists_mem_inter`, directly).

The lemma names keep the core's `_correct_support` for cross-arc continuity,
even though no `Correct` set survives the crash simplification.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : Universe Validator BlockId Payload}

/-- The ids present at a given round. -/
def blocksAt (U : Universe Validator BlockId Payload) (n : ℕ) : Finset BlockId :=
  U.ids.filter (fun i => (U.block i).round = n)

/-- The validators holding a block at a given round — the pool `p`. -/
def authorsAt (U : Universe Validator BlockId Payload) (n : ℕ) : Finset Validator :=
  creatorsOf U.block (blocksAt U n)

/-- Membership in `blocksAt`, unfolded. -/
@[simp]
theorem mem_blocksAt {i : BlockId} {n : ℕ} :
    i ∈ blocksAt U n ↔ i ∈ U.ids ∧ (U.block i).round = n := by
  simp [blocksAt]

/-- Membership in `authorsAt`, unfolded: an author of a round is anyone with a block there. -/
theorem mem_authorsAt {v : Validator} {n : ℕ} :
    v ∈ authorsAt U n ↔ ∃ i ∈ U.ids, (U.block i).round = n ∧ (U.block i).creator = v := by
  simp [authorsAt, mem_creatorsOf]
  tauto

/-- The author pool never exceeds the validator set. This is what turns the
participation-sensitive threshold into the uniform `majority` one. -/
theorem card_authorsAt_le_univ {n : ℕ} : (authorsAt U n).card ≤ Fintype.card Validator := by
  rw [← Finset.card_univ]; exact Finset.card_le_univ _

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
block satisfying `P`, once enough validators have published round-`n` blocks
satisfying it.

The crash port of `exists_mem_refs_of_correct_support`: the correctness
filtering is gone (all validators are honest, so `no_equivocation` identifies
the shared block unconditionally), and the `n − f` quorum on `c`'s creators
becomes a `majority`. The threshold is participation-sensitive: `c` draws a
majority of its referenced creators from the round-`n` author pool, so it
cannot dodge every backer. -/
theorem exists_mem_refs_of_correct_support
    {P : BlockId → Prop} {n : ℕ} {T : Finset Validator}
    (hT : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = n ∧ P q ∧ (U.block q).creator = v)
    (hp : (authorsAt U n).card + 1 ≤ T.card + majority Validator)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    ∃ q ∈ (U.block c).refs, P q := by
  set A := creatorsOf U.block (U.block c).refs with hA
  have hA_quorum : majority Validator ≤ A.card := U.creators_quorum hc (by omega)
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
    unfold majority at hA_quorum hp
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
    U.eq_of_creator_eq hi_ids hq_ids (hi_creator.trans hq_creator.symm) (by omega)
  exact ⟨i, hi_mem, hiq ▸ hq_P⟩

/-- **The hitting lemma, uniform form.** A `majority` of backers always
suffices: `c` names a majority of the round-`n` authors, and two majorities of
the pool intersect. The crash port of
`exists_mem_refs_of_correct_support_of_card`. -/
theorem exists_mem_refs_of_correct_support_of_card
    {P : BlockId → Prop} {n : ℕ} {T : Finset Validator}
    (hT : ∀ v ∈ T, ∃ q ∈ U.ids, (U.block q).round = n ∧ P q ∧ (U.block q).creator = v)
    (hcard : majority Validator ≤ T.card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = n + 1) :
    ∃ q ∈ (U.block c).refs, P q := by
  refine exists_mem_refs_of_correct_support hT ?_ hc hcr
  have hle := card_authorsAt_le_univ (U := U) (n := n)
  unfold majority at hcard ⊢
  omega

/-- **Coverage, participation-sensitive form.** A block backed by enough
round-`(r+1)` validators is reached by every round-`(r+2)` block. The
`P`-instance of the hitting lemma where every target references `b`. -/
theorem reaches_of_correct_support
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ q ∈ U.ids,
      (U.block q).round = r + 1 ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v)
    (hp : (authorsAt U (r + 1)).card + 1 ≤ S.card + majority Validator)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b := by
  obtain ⟨q, hq_mem, hq_ref⟩ :=
    exists_mem_refs_of_correct_support (P := fun q => b ∈ (U.block q).refs)
      hS_support hp hc (by omega)
  exact Reaches.of_mem_refs hq_mem (Reaches.single hq_ref)

/-- **Coverage, uniform form.** A `majority` of supporters always suffices.
This is the form to use when supporters come from a quorum rather than from
counting — the crash port of `reaches_of_correct_support_of_card`. -/
theorem reaches_of_correct_support_of_card
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ q ∈ U.ids,
      (U.block q).round = r + 1 ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v)
    (hcard : majority Validator ≤ S.card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b := by
  refine reaches_of_correct_support hS_support ?_ hc hcr
  have hle := card_authorsAt_le_univ (U := U) (n := r + 1)
  unfold majority at hcard ⊢
  omega

/-- **Propagation.** Reaching something is inherited upward: if every block
at round `N` reaches a `P`-block, so does every block above `N`.

A verbatim port of the core lemma of the same name: the step needs nothing
but nonempty references and transitivity — height is carried by `Reaches`
alone, so no quorum content is involved. -/
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

/-! ## Support sets

The coverage lemmas above take their support set as a bare `Finset Validator`
so they stay instance-free. These are the concrete sets callers build, and
forming them needs decidable equality on ids. Under crash there is no
`correctSupporters`-vs-Byzantine ledger — every supporter counts. Nor is there
a `blames` set: the crash protocol has no majority-blame direct skip (the
implementation sets the direct-skip quorum to the full stake), so leaders are
skipped only indirectly. -/

variable [DecidableEq BlockId]

/-- The validators whose round-`n` block references `b`. -/
def supporters (U : Universe Validator BlockId Payload) (b : BlockId) (n : ℕ) :
    Finset Validator :=
  creatorsOf U.block ((blocksAt U n).filter (fun q => b ∈ (U.block q).refs))

/-- Membership in `supporters`, unfolded: a supporter has a round-`n` block referencing `b`. -/
theorem mem_supporters {b : BlockId} {n : ℕ} {v : Validator} :
    v ∈ supporters U b n ↔
      ∃ q ∈ U.ids, (U.block q).round = n ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v := by
  simp [supporters, mem_creatorsOf]
  tauto

/-- Supporters are a subset of the round's authors. -/
theorem supporters_subset_authorsAt {b : BlockId} {n : ℕ} :
    supporters U b n ⊆ authorsAt U n :=
  Finset.image_subset_image (Finset.filter_subset _ _)

end Nemo

end LeanDag
