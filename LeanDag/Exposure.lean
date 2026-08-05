import LeanDag.History

/-!
# Exposure, and the DoS-protection condition

`dos-equivocation-and-growth.md` §6, results **D11**–**D13**.

`X` is *exposed* in `b`'s history when that history holds two distinct blocks
by `X` at one round. It is a local, checkable test — no quorum, no round bound,
no network assumption — and `DoSValid` is the rule that a block may not
reference an exposed author.

The three results are what make the rule usable rather than merely stateable:

* **D11** — being inflated by `X` and exposing `X` are the *same condition*, so
  the rule fires exactly when there is damage to prevent. This is why nothing
  here has to catch equivocators reliably: an equivocator that is never exposed
  is one that never inflated anything.
* **D12** — exposure is inherited upward, so exclusion is permanent.
* **D13** — the test is view-independent (T6a), so two correct validators
  holding different views never disagree about whether a block is valid.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- Two ids witnessing an equivocation by `X`: distinct, both authored by `X`,
both at one round.

Split out from `ExposedIn` so that D13 can quantify over the *same* witness
condition with and without a view restriction. -/
def EquivPair (U : BlockUniverse Validator BlockId Payload) (X : Validator) (i j : BlockId) :
    Prop :=
  i ≠ j ∧ (U.block i).creator = X ∧ (U.block j).creator = X ∧
    (U.block i).round = (U.block j).round

instance decidableEquivPair (X : Validator) (i j : BlockId) : Decidable (EquivPair U X i j) :=
  inferInstanceAs (Decidable (i ≠ j ∧ _ ∧ _ ∧ _))

omit [DecidableEq BlockId] in
theorem EquivPair.symm {X : Validator} {i j : BlockId} (h : EquivPair U X i j) :
    EquivPair U X j i :=
  ⟨h.1.symm, h.2.2.1, h.2.1, h.2.2.2.symm⟩

/-- **`X` is exposed in `b`'s history**: two distinct blocks by `X` at one
round lie below `b`.

Stated over `history` rather than over `Reaches` so that it is decidable and
countable; `exposedIn_iff_reaches` gives the `Reaches` form for a block of the
universe. -/
def ExposedIn (U : BlockUniverse Validator BlockId Payload) (b : BlockId) (X : Validator) :
    Prop :=
  ∃ i ∈ history U b, ∃ j ∈ history U b, EquivPair U X i j

instance decidableExposedIn (b : BlockId) (X : Validator) : Decidable (ExposedIn U b X) :=
  inferInstanceAs (Decidable (∃ i ∈ history U b, ∃ j ∈ history U b, EquivPair U X i j))

theorem exposedIn_iff_reaches {b : BlockId} {X : Validator} (hb : b ∈ U.ids) :
    ExposedIn U b X ↔
      ∃ i j, Reaches U b i ∧ Reaches U b j ∧ EquivPair U X i j := by
  constructor
  · rintro ⟨i, hi, j, hj, hpair⟩
    exact ⟨i, j, (mem_history_iff hb).mp hi, (mem_history_iff hb).mp hj, hpair⟩
  · rintro ⟨i, j, hi, hj, hpair⟩
    exact ⟨i, (mem_history_iff hb).mpr hi, j, (mem_history_iff hb).mpr hj, hpair⟩

/-- **The DoS-protection condition** (§6): a block may not reference an author
exposed in its own history.

A predicate on the universe, deliberately **not** a field of `ValidWrt`. Every
safety and liveness theorem in the development applies verbatim under it,
because none of them mention it; results that need it take it as an extra
hypothesis. -/
def DoSValid (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator

/-- Decidable on concrete data, so a small DAG can be checked by `decide` —
which is how a witness confirms the condition is satisfiable *and* biting
rather than vacuous. -/
instance decidableDoSValid : Decidable (DoSValid U) :=
  inferInstanceAs (Decidable (∀ b ∈ U.ids, ∀ i ∈ (U.block b).refs,
    ¬ ExposedIn U b (U.block i).creator))

/-! ## D11 — inflation *is* exposure -/

/-- The blocks of `b`'s history authored by `X` at round `n`. The thing the
size results count. -/
def historyBlocksOf (U : BlockUniverse Validator BlockId Payload) (b : BlockId)
    (X : Validator) (n : ℕ) : Finset BlockId :=
  (history U b).filter (fun i => (U.block i).creator = X ∧ (U.block i).round = n)

theorem mem_historyBlocksOf {b i : BlockId} {X : Validator} {n : ℕ} :
    i ∈ historyBlocksOf U b X n ↔
      i ∈ history U b ∧ (U.block i).creator = X ∧ (U.block i).round = n := by
  simp [historyBlocksOf]

/-- **Not exposed** and **at most one block per round** are the same condition.

The counting form of `ExposedIn`, and the whole content of D11: an author that
is never exposed in `b`'s history contributes at most one block per round to
it, so the equivocation bought nothing. -/
theorem not_exposedIn_iff_card_le_one {b : BlockId} {X : Validator} :
    ¬ ExposedIn U b X ↔ ∀ n, (historyBlocksOf U b X n).card ≤ 1 := by
  constructor
  · intro h n
    rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hne
    obtain ⟨hi_hist, hi_creator, hi_round⟩ := mem_historyBlocksOf.mp hi
    obtain ⟨hj_hist, hj_creator, hj_round⟩ := mem_historyBlocksOf.mp hj
    exact h ⟨i, hi_hist, j, hj_hist, hne, hi_creator, hj_creator, by rw [hi_round, hj_round]⟩
  · rintro h ⟨i, hi, j, hj, hne, hi_creator, hj_creator, hround⟩
    have hcard := h (U.block i).round
    rw [Finset.card_le_one] at hcard
    exact hne (hcard i (mem_historyBlocksOf.mpr ⟨hi, hi_creator, rfl⟩)
      j (mem_historyBlocksOf.mpr ⟨hj, hj_creator, hround.symm⟩))

/-- **D11.** Under the DoS condition, for every block and every author exactly
one of two things holds: the author contributed at most one block per round to
that history — so equivocating gained it nothing there — or the block does not
reference it.

The dichotomy is not a theorem about the protocol so much as a reading of the
definitions: *inflated* and *exposed* are the same word. What the DoS condition
adds is the second disjunct. -/
theorem card_le_one_or_not_mem_refs (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    (X : Validator) :
    (∀ n, (historyBlocksOf U b X n).card ≤ 1) ∨
      (∀ i ∈ (U.block b).refs, (U.block i).creator ≠ X) := by
  by_cases hexp : ExposedIn U b X
  · refine Or.inr fun i hi hcreator => hdos b hb i hi ?_
    rwa [hcreator]
  · exact Or.inl (not_exposedIn_iff_card_le_one.mp hexp)

/-! ## D12 — exposure is permanent -/

/-- **D12.** Exposure is inherited by everything above: what one block's
history reveals, every block reaching it reveals too.

So exclusion, once earned, is never lost — which is what makes `DoSValid` a
ratchet rather than a condition an author can wait out. -/
theorem ExposedIn.mono {c b : BlockId} {X : Validator} (hc : c ∈ U.ids)
    (hreach : Reaches U c b) (h : ExposedIn U b X) : ExposedIn U c X := by
  obtain ⟨i, hi, j, hj, hpair⟩ := h
  have hsub := history_subset_of_reaches hc hreach
  exact ⟨i, hsub hi, j, hsub hj, hpair⟩

/-- Exposure passes up a single reference — the form the induction in D17 will
want. -/
theorem ExposedIn.of_mem_refs {c b : BlockId} {X : Validator} (hc : c ∈ U.ids)
    (hb : b ∈ (U.block c).refs) (h : ExposedIn U b X) : ExposedIn U c X :=
  h.mono hc (Reaches.single hb)

/-! ## D13 — exposure is view-independent

T6a (`View.exists_reaches_iff`) says a causal-history question gives the same
answer whether or not the search is confined to a view. Exposure is such a
question, so a validator's local verdict on `DoSValid` is the universe's. -/

/-- Causal history never escapes a view — T6a in `Finset` form. -/
theorem history_subset_view {V : View Validator BlockId Payload U} {b : BlockId}
    (hb : b ∈ V.ids) : history U b ⊆ V.ids :=
  fun _ hi => View.mem_of_reaches hb ((mem_history_iff (V.subset_ids hb)).mp hi)

/-- **D13.** Restricting the search for an equivocation to a view that holds
`b` costs nothing: the witnesses could never have lain outside it.

Two correct validators with different views therefore never disagree about
whether a block is DoS-valid, which is what makes the condition a validity
condition rather than a matter of opinion. -/
theorem exposedIn_iff_of_view {V : View Validator BlockId Payload U} {b : BlockId}
    {X : Validator} (hb : b ∈ V.ids) :
    (∃ i ∈ V.ids, ∃ j ∈ V.ids, i ∈ history U b ∧ j ∈ history U b ∧ EquivPair U X i j) ↔
      ExposedIn U b X := by
  constructor
  · rintro ⟨i, _, j, _, hi, hj, hpair⟩
    exact ⟨i, hi, j, hj, hpair⟩
  · rintro ⟨i, hi, j, hj, hpair⟩
    exact ⟨i, history_subset_view hb hi, j, history_subset_view hb hj, hi, hj, hpair⟩

end LeanDag
