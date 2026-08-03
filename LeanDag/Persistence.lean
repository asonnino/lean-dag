import LeanDag.Support

/-!
# Persistence

`spec.md` T3 — the theorem the rest of the development exists to support.

If a block `b` at round `r` is referenced by a *quorum* of blocks at round
`r+1`, then every block from round `r+2` onward has `b` in its causal
history. Once a quorum backs a block, it can never be forgotten.

Two things about the statement are worth flagging, both settled during
review and both easy to get wrong:

* **The bound is `r+2`, not `r+1`, and it is tight.** A round-`(r+1)` block
  outside the quorum need not reference `b` at all. With `f = 1` and
  validators `{A,B,C,D}`, let `b` be A's round-`r` block and let `A,B,C`'s
  round-`(r+1)` blocks reference it; D's round-`(r+1)` block may reference
  `{B,C,D}` instead, and since all its references sit at round `r`, `b` is
  not in its causal history. Quorum intersection needs *two* ref-quorums to
  compare, and `r+2` is the first round that has them.

* **The quorum hypothesis is on `Q`'s creator set, not on `Q.card`.** `Q` is
  an arbitrary set of ids, not a block's references, so it carries no
  distinctness invariant of its own; a Byzantine author could otherwise pad
  it with equivocating blocks.

The proof uses quorum intersection exactly **once**, in the base case. Above
that layer, height is carried by transitivity alone. Note also that the
distinct-creators invariant is *not* used anywhere here — the validator
pulled from the intersection is correct by construction, so non-equivocation
(T1) already supplies the uniqueness that identifies the two blocks.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The quorum hypothesis already forces `b` into the universe at round `r`,
so T3 need not assume either. A quorum has at least `2f+1 ≥ 1` authors, so
`Q` is nonempty; any member is in the universe, references `b`, and sits at
round `r+1`, which pins `b` by completeness and the predecessor condition. -/
theorem mem_ids_and_round_of_quorum_support
    {b : BlockId} {r : ℕ} {Q : Finset BlockId} (hQ : Q ⊆ U.ids)
    (hQround : ∀ q ∈ Q, (U.block q).round = r + 1)
    (hQref : ∀ q ∈ Q, b ∈ (U.block q).refs)
    (hQquorum : 2 * F.f + 1 ≤ (creatorsOf U.block Q).card) :
    b ∈ U.ids ∧ (U.block b).round = r := by
  have hQne : Q.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    rintro rfl
    simp [creatorsOf] at hQquorum
  obtain ⟨q, hq⟩ := hQne
  have hq_ids := hQ hq
  have hb_ref := hQref q hq
  refine ⟨U.complete q hq_ids b hb_ref, ?_⟩
  have h1 := U.round_of_mem_refs hq_ids hb_ref
  have h2 := hQround q hq
  omega

/-- **T3 (Persistence).** If `b` is referenced by a quorum of round-`(r+1)`
blocks, every block at round `r+2` or later has `b` in its causal history.

Neither `b ∈ U.ids` nor `(U.block b).round = r` is assumed: both follow from
the quorum hypothesis (`mem_ids_and_round_of_quorum_support`). -/
theorem reaches_of_quorum_support
    {b : BlockId} {r : ℕ}
    {Q : Finset BlockId} (hQ : Q ⊆ U.ids)
    (hQround : ∀ q ∈ Q, (U.block q).round = r + 1)
    (hQref : ∀ q ∈ Q, b ∈ (U.block q).refs)
    (hQquorum : 2 * F.f + 1 ≤ (creatorsOf U.block Q).card)
    {c : BlockId} (hc : c ∈ U.ids) (hcr : r + 2 ≤ (U.block c).round) :
    Reaches U c b := by
  -- Strong induction on the round of `c`.
  suffices H : ∀ n, ∀ c ∈ U.ids, (U.block c).round = n → r + 2 ≤ n → Reaches U c b by
    exact H _ c hc rfl hcr
  clear hcr hc c
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro c hc hcn hrn
    rcases eq_or_lt_of_le hrn with hbase | hstep
    · -- Base case: `c` sits at round `r+2`. The quorum contains at least
      -- `f+1` *correct* creators, and those are exactly the supporters the
      -- uniform coverage lemma consumes.
      refine reaches_of_correct_support_of_card (b := b) (r := r)
        (S := creatorsOf U.block Q ∩ (Correct : Finset Validator)) ?_ ?_ ?_ hc (by omega)
      · intro v hv
        rw [Finset.mem_inter, mem_creatorsOf] at hv
        obtain ⟨⟨q, hq_mem, hq_creator⟩, _⟩ := hv
        exact ⟨q, hQ hq_mem, hQround q hq_mem, hQref q hq_mem, hq_creator⟩
      · exact fun v hv => Finset.mem_of_mem_inter_right hv
      · exact card_inter_correct_of_quorum hQquorum
    · -- Inductive step: no quorum reasoning needed. Any reference of `c`
      -- lands at a strictly smaller round that is still at least `r+2`.
      obtain ⟨i, hi_mem⟩ := U.refs_nonempty hc (by omega)
      have hi_ids : i ∈ U.ids := U.complete c hc i hi_mem
      have hi_round := U.round_of_mem_refs hc hi_mem
      exact Reaches.of_mem_refs hi_mem
        (ih (U.block i).round (by omega) i hi_ids rfl (by omega))

end LeanDag
