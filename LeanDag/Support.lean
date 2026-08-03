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
  its 2f+1 referenced creators from those same `p`, so it misses exactly
  `p - (2f+1)` of them and cannot dodge `p - 2f` supporters.

* `reaches_of_correct_support_of_card` — threshold `f+1`, uniform. Since
  `p ≤ 3f+1` always, this is the corollary: a round-`(r+2)` block names 2f+1
  of the 3f+1 validators, so it misses at most `f`.

The `f+1` form is the one to reach for when supporters are *assumed* (T3
gets them free: a quorum of 2f+1 distinct creators contains at least `f+1`
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
theorem card_authorsAt_le_univ {n : ℕ} : (authorsAt U n).card ≤ 3 * F.f + 1 := by
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

/-- **Coverage, participation-sensitive form.** A block backed by `p - 2f`
correct round-`(r+1)` validators is reached by every round-`(r+2)` block.

The support set is given as a plain `Finset Validator` together with a
witness for each member, rather than as `supporters U b (r+1)`, so that this
file needs no decidable equality on ids. -/
theorem reaches_of_correct_support
    {b : BlockId} {r : ℕ} {S : Finset Validator}
    (hS_support : ∀ v ∈ S, ∃ q ∈ U.ids,
      (U.block q).round = r + 1 ∧ b ∈ (U.block q).refs ∧ (U.block q).creator = v)
    (hS_correct : ∀ v ∈ S, v ∈ (Correct : Finset Validator))
    (hp : (authorsAt U (r + 1)).card ≤ S.card + 2 * F.f)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : (U.block c).round = r + 2) :
    Reaches U c b := by
  set A := creatorsOf U.block (U.block c).refs with hA
  -- `c`'s referenced creators form a quorum; they and `S` both sit in the
  -- round-`(r+1)` author pool, and their sizes overflow it.
  have hA_quorum : 2 * F.f + 1 ≤ A.card := U.creators_quorum hc (by omega)
  have hA_sub : A ⊆ authorsAt U (r + 1) := creators_refs_subset_authorsAt hc (by omega)
  have hS_auth : S ⊆ authorsAt U (r + 1) := by
    intro v hv
    obtain ⟨q, hq_ids, hq_round, _, hq_creator⟩ := hS_support v hv
    rw [mem_authorsAt]
    exact ⟨q, hq_ids, hq_round, hq_creator⟩
  have hunion : (A ∪ S).card ≤ (authorsAt U (r + 1)).card :=
    Finset.card_le_card (Finset.union_subset hA_sub hS_auth)
  have hadd := Finset.card_union_add_card_inter A S
  have hinter : 0 < (A ∩ S).card := by omega
  obtain ⟨v, hv⟩ := Finset.card_pos.mp hinter
  rw [Finset.mem_inter] at hv
  obtain ⟨hv_A, hv_S⟩ := hv
  rw [hA, mem_creatorsOf] at hv_A
  obtain ⟨i, hi_mem, hi_creator⟩ := hv_A
  obtain ⟨q, hq_ids, hq_round, hq_ref, hq_creator⟩ := hS_support v hv_S
  -- `v` is correct, so its round-`(r+1)` block is unique: `i = q`.
  have hi_ids : i ∈ U.ids := U.complete c hc i hi_mem
  have hi_round : (U.block i).round = r + 1 := by
    have := U.round_of_mem_refs hc hi_mem
    omega
  have hiq : i = q :=
    U.eq_of_creator_eq hi_ids hq_ids (hS_correct v hv_S) hi_creator hq_creator
      (by rw [hi_round, hq_round])
  exact Reaches.of_mem_refs hi_mem (Reaches.single (by rw [hiq]; exact hq_ref))

/-- **Coverage, uniform form.** `f+1` correct supporters always suffice: a
round-`(r+2)` block names 2f+1 of the 3f+1 validators, so it misses at most
`f` and cannot dodge them all.

This is the form to use when supporters come from a quorum rather than from
counting — see T3, where 2f+1 distinct creators contain `f+1` correct ones
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

end LeanDag
