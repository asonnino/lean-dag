import LeanDag.Liveness
import LeanDag.History
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# The novelty budget

`dos-equivocation-and-growth.md` §10.7. The slogan: **legislate novelty,
prove size**.

§10.6 settles that inside the bare model the per-author chain count is
`2^Θ(e)` — the doubling family is valid, and no acceptance rule on cone
*shape* can refuse it without convicting correct blocks (the forced merge of
`Utwin`). What distinguishes the family is invisible to any intrinsic
predicate: its mass is *novel to the observer* — old blocks, never public,
delivered in one reveal. So the rule this file formalizes is observer-
relative: a block is measured by `novelty U V b := history U b \ V`, what
accepting it would newly pull into the view `V`.

Four layers, each usable without the ones after it:

* **The measure.** `novelty`, antitone in the view — which is what makes
  deferral a rate limiter rather than a verdict: a deferred block only ever
  becomes cheaper.
* **The telescope** (pure DAG, no delivery model). If each block of a
  correct author adds at most `κ'` over its self-parent (`StepNovelty`),
  the whole history is linear: `|H(b)| ≤ κ'·r + 1`, by S10's descent.
* **B3** (at the acceptance layer). `viewUpto` accumulates
  `Delivery.accepted` with whole histories — the retained view of S1 —
  and `NoveltyBudget` caps each acceptance: `κ` for a Byzantine author,
  `Κ` for a correct one (the hysteresis pair of §10.7). Then a correct
  validator's view is linear in the round,
  `|V_v(n)| ≤ (3f+1) + (|Correct|·Κ + f·κ)·n`, and through the D3 bridge
  so is the history of its own next block.
* **C3** (the liveness half). After `R`, the novelty of a correct block at
  any correct validator is `1 +` the standing *view gap* toward its author
  (`card_novelty_le_viewGap_add_one`) — and the gap grows by at most `f·κ`
  per round (`card_viewGap_succ_le`), because correct acceptances are
  shared and Byzantine ones are budgeted. The adversary's hidden mass
  appears in neither term, which is what makes the contagion attack of
  §10.7 harmless.
* **The collapse and the capstone.** The gap does not even drift: a
  correct block's cone is a complete record of its author's acceptances
  (`viewUpto_subset_history` — `includes` per round, chained by S10), so
  one delivered block collapses the gap to one round of Byzantine budget
  (C3′, `card_viewGap_succ_le_of_block`), and the hysteresis threshold is
  the derived **constant** `Κ = f·κ + 1` (C3″,
  `card_novelty_le_of_byzBudget`) — the correct clause of the budget is a
  theorem, given only the enforceable Byzantine clause (`ByzBudget`).
  `no_stall_and_card_viewUpto_le` then delivers liveness and linear
  storage from one set of hypotheses.
* **B4** (unconditional). Even the post-`R` base is dispensable: the
  global Byzantine pool (`byzPool`) grows by at most `|Correct|·f·κ` per
  round with **no synchrony at all** — every Byzantine block in a correct
  view entered through some correct validator's budgeted acceptance — so
  storage is linear from round 0 under full asynchrony
  (`card_viewUpto_le_of_refsAccepted`, `no_stall_and_card_viewUpto_le'`).

The one hypothesis the C3 chain takes beyond `Delivery` is
`RefsAccepted` — `refs ⊆ accepted`, the converse of `includes`, i.e. D3's
ordinary case: a correct validator references only what it accepted.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {V W : Finset BlockId} {b i : BlockId} {m n : ℕ}

/-! ## The measure -/

/-- What accepting `b` would newly bring into the view `V`. -/
def novelty (U : BlockUniverse Validator BlockId Payload) (V : Finset BlockId)
    (b : BlockId) : Finset BlockId :=
  history U b \ V

theorem mem_novelty : i ∈ novelty U V b ↔ i ∈ history U b ∧ i ∉ V :=
  Finset.mem_sdiff

@[simp]
theorem novelty_empty : novelty U ∅ b = history U b := by
  simp [novelty]

/-- **Antitone in the view** — the load-bearing property. Deferral is a rate
limiter, not a verdict: as the view grows, every deferred block only gets
cheaper. -/
theorem novelty_anti (h : V ⊆ W) : novelty U W b ⊆ novelty U V b :=
  Finset.sdiff_subset_sdiff (Finset.Subset.refl _) h

theorem card_novelty_anti (h : V ⊆ W) :
    (novelty U W b).card ≤ (novelty U V b).card :=
  Finset.card_le_card (novelty_anti h)

/-- A history costs at most the view plus the novelty. -/
theorem card_history_le_card_add :
    (history U b).card ≤ V.card + (novelty U V b).card := by
  refine le_trans (Finset.card_le_card (?_ : history U b ⊆ V ∪ novelty U V b)) ?_
  · intro i hi
    by_cases hiv : i ∈ V
    · exact Finset.mem_union_left _ hiv
    · exact Finset.mem_union_right _ (mem_novelty.mpr ⟨hi, hiv⟩)
  · exact Finset.card_union_le _ _

/-- A genesis history is a singleton — round 0 needs no budget clause. -/
theorem history_eq_singleton_of_round_zero (hb : b ∈ U.ids)
    (h0 : (U.block b).round = 0) : history U b = {b} := by
  apply Finset.Subset.antisymm
  · intro i hi
    have := round_le_of_mem_history hb hi
    rw [Finset.mem_singleton]
    exact eq_of_mem_history_of_round_eq hb hi (by omega)
  · simp

/-! ## The telescope — pure DAG, no delivery model

If each block of a correct author adds at most `κ'` over its self-parent,
the history is linear in the round. This is §10.7's quotable form: it needs
no schedule, no network, nothing but S10. -/

/-- Stepwise novelty: every correct block adds at most `κ'` blocks over the
history of its self-parent. For a correct author the self-parent is unique
(`no_equivocation`), so the `∀` costs nothing. -/
def StepNovelty (U : BlockUniverse Validator BlockId Payload) (κ' : ℕ) : Prop :=
  ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ p ∈ (U.block b).refs, (U.block p).creator = (U.block b).creator →
      (novelty U (history U p) b).card ≤ κ'

instance : Decidable (StepNovelty U κ') := by
  unfold StepNovelty; infer_instance

private theorem card_history_le_of_stepNovelty_aux {κ' : ℕ}
    (hstep : StepNovelty U κ') :
    ∀ r, ∀ b ∈ U.ids, (U.block b).creator ∈ (Correct : Finset Validator) →
      (U.block b).round = r → (history U b).card ≤ κ' * r + 1 := by
  intro r
  induction r with
  | zero =>
      intro b hb _ hr
      rw [history_eq_singleton_of_round_zero hb hr]
      simp
  | succ r ih =>
      intro b hb hcorr hr
      obtain ⟨p, hp, hpc⟩ := (U.valid b hb).self_parent (by omega)
      have hp_ids : p ∈ U.ids := U.complete b hb p hp
      have hp_round : (U.block p).round + 1 = (U.block b).round :=
        U.round_of_mem_refs hb hp
      have h1 : (history U p).card ≤ κ' * r + 1 :=
        ih p hp_ids (by rw [hpc]; exact hcorr) (by omega)
      have h2 : (novelty U (history U p) b).card ≤ κ' := hstep b hb hcorr p hp hpc
      have h3 : (history U b).card ≤
          (history U p).card + (novelty U (history U p) b).card :=
        card_history_le_card_add
      have hmul : κ' * (r + 1) = κ' * r + κ' := Nat.mul_succ κ' r
      omega

/-- **The telescope.** Under `StepNovelty`, a correct author's history is
linear: `|H(b)| ≤ κ'·r + 1`. Descent along the self-parent chain (S10),
one budget per round. -/
theorem card_history_le_of_stepNovelty {κ' : ℕ} (hstep : StepNovelty U κ')
    (hb : b ∈ U.ids) (hcorr : (U.block b).creator ∈ (Correct : Finset Validator)) :
    (history U b).card ≤ κ' * (U.block b).round + 1 :=
  card_history_le_of_stepNovelty_aux hstep (U.block b).round b hb hcorr rfl

/-! ## The accumulated view -/

variable {D : Delivery U} {v w : Validator}

/-- Everything `v` has retained by round `n`: the whole histories of
everything it accepted at any round up to `n` — the retained view of S1,
accumulated. This is what novelty is measured against, and the reason C3
works: accepting a block means holding its entire cone. -/
def viewUpto (D : Delivery U) (v : Validator) : ℕ → Finset BlockId
  | 0 => (D.accepted v 0).biUnion (history U)
  | n + 1 => viewUpto D v n ∪ (D.accepted v (n + 1)).biUnion (history U)

theorem viewUpto_succ (n : ℕ) :
    viewUpto D v (n + 1) =
      viewUpto D v n ∪ (D.accepted v (n + 1)).biUnion (history U) := rfl

theorem viewUpto_mono (h : m ≤ n) : viewUpto D v m ⊆ viewUpto D v n := by
  induction n with
  | zero =>
      obtain rfl : m = 0 := Nat.le_zero.mp h
      exact Finset.Subset.refl _
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with hlt | hge
      · intro x hx
        rw [viewUpto_succ]
        exact Finset.mem_union_left _ (ih (by omega) hx)
      · obtain rfl : m = n + 1 := by omega
        exact Finset.Subset.refl _

/-- An accepted block's whole history is retained. -/
theorem history_subset_viewUpto {a : BlockId} (hmn : m ≤ n)
    (ha : a ∈ D.accepted v m) : history U a ⊆ viewUpto D v n := by
  refine Finset.Subset.trans ?_ (viewUpto_mono hmn)
  cases m with
  | zero => exact Finset.subset_biUnion_of_mem (history U) ha
  | succ m =>
      intro x hx
      rw [viewUpto_succ]
      exact Finset.mem_union_right _
        (Finset.subset_biUnion_of_mem (history U) ha hx)

/-- Nothing retained by round `n` sits above round `n`. -/
theorem round_le_of_mem_viewUpto (hi : i ∈ viewUpto D v n) :
    (U.block i).round ≤ n := by
  induction n with
  | zero =>
      obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
      obtain ⟨ha_ids, ha_round⟩ := D.held_spec v 0 a (D.accepted_sub v 0 ha)
      have := round_le_of_mem_history ha_ids hia
      omega
  | succ n ih =>
      rw [viewUpto_succ] at hi
      rcases Finset.mem_union.mp hi with h | h
      · have := ih h; omega
      · obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp h
        obtain ⟨ha_ids, ha_round⟩ := D.held_spec v (n + 1) a (D.accepted_sub v (n + 1) ha)
        have := round_le_of_mem_history ha_ids hia
        omega

/-! ## The budget -/

/-- **The novelty budget** (§10.7): every acceptance was affordable — at
most `κ` novel blocks for a Byzantine author, `Κ` for a correct one. The
two thresholds are the hysteresis pair: `κ` is policy, chosen small; `Κ`
must be large enough that correct blocks always pass, and C3 below is the
theorem that a bounded `Κ` exists to choose. Round 0 needs no clause:
genesis histories are singletons. -/
def NoveltyBudget (D : Delivery U) (κ Κ : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (novelty U (viewUpto D v n) b).card ≤
      if (U.block b).creator ∈ (Correct : Finset Validator) then Κ else κ

/-- The **enforceable half** of the budget: only the Byzantine clause. This
is the rule a validator can actually run — defer any Byzantine-authored
block costing more than `κ` — and it is all the gap analysis needs. The
correct clause is *derived* from it (`card_novelty_le_of_byzBudget`): a
validator enforcing `κ` never meets a correct block over `f·κ + 1`. -/
def ByzBudget (D : Delivery U) (κ : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ D.accepted v (n + 1),
    (U.block b).creator ∉ (Correct : Finset Validator) →
    (novelty U (viewUpto D v n) b).card ≤ κ

theorem NoveltyBudget.byzBudget {κ Κ : ℕ} (h : NoveltyBudget D κ Κ) :
    ByzBudget D κ := fun v hv n b hb hbc => by
  have := h v hv n b hb
  rwa [if_neg hbc] at this

omit [DecidableEq BlockId] in
/-- One acceptance per author: the frontier splits into at most `|Correct|`
correct-authored blocks… -/
private theorem card_filter_correct_le (v : Validator) (n : ℕ) :
    ((D.accepted v n).filter
      fun b => (U.block b).creator ∈ (Correct : Finset Validator)).card ≤
      (Correct : Finset Validator).card := by
  refine Finset.card_le_card_of_injOn (fun b => (U.block b).creator) ?_ ?_
  · intro b hb
    exact (Finset.mem_filter.mp hb).2
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_filter] at hi hj
    exact D.accepted_inj v n i hi.1 j hj.1 hij

omit [DecidableEq BlockId] in
/-- …and at most `f` Byzantine-authored ones. -/
private theorem card_filter_not_correct_le (v : Validator) (n : ℕ) :
    ((D.accepted v n).filter
      fun b => (U.block b).creator ∉ (Correct : Finset Validator)).card ≤ F.f := by
  refine le_trans ?_ F.card_byzantine
  refine Finset.card_le_card_of_injOn (fun b => (U.block b).creator) ?_ ?_
  · intro b hb
    have := (Finset.mem_filter.mp hb).2
    simp only [mem_correct, not_not] at this
    exact this
  · intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_filter] at hi hj
    exact D.accepted_inj v n i hi.1 j hj.1 hij

/-- The Byzantine spend of one round: at most `f` acceptances, `κ` each. -/
private theorem sum_novelty_not_correct_le {κ : ℕ} (hbyz : ByzBudget D κ)
    (hv : v ∈ (Correct : Finset Validator)) (n : ℕ) :
    ∑ t ∈ (D.accepted v (n + 1)).filter
        (fun t => (U.block t).creator ∉ (Correct : Finset Validator)),
      (novelty U (viewUpto D v n) t).card ≤ F.f * κ :=
  calc ∑ t ∈ (D.accepted v (n + 1)).filter
        (fun t => (U.block t).creator ∉ (Correct : Finset Validator)),
        (novelty U (viewUpto D v n) t).card
      ≤ ∑ _t ∈ (D.accepted v (n + 1)).filter
          (fun t => (U.block t).creator ∉ (Correct : Finset Validator)), κ :=
        Finset.sum_le_sum fun t ht =>
          hbyz v hv n t (Finset.mem_of_mem_filter t ht) (Finset.mem_filter.mp ht).2
    _ = ((D.accepted v (n + 1)).filter
          (fun t => (U.block t).creator ∉ (Correct : Finset Validator))).card * κ :=
        Finset.sum_const_nat fun _ _ => rfl
    _ ≤ F.f * κ := Nat.mul_le_mul_right κ (card_filter_not_correct_le v (n + 1))

/-! ## B3 — the view bound -/

/-- The generic one-round step: any per-block novelty bounds on the correct
and Byzantine acceptances bound the view's growth. `card_viewUpto_succ_le`
instantiates it with the assumed budget; the capstone instantiates the
correct side with the *derived* threshold instead. -/
private theorem card_viewUpto_succ_le_of_bounds {κc κb n : ℕ}
    (hc : ∀ b ∈ D.accepted v (n + 1),
      (U.block b).creator ∈ (Correct : Finset Validator) →
      (novelty U (viewUpto D v n) b).card ≤ κc)
    (hbz : ∀ b ∈ D.accepted v (n + 1),
      (U.block b).creator ∉ (Correct : Finset Validator) →
      (novelty U (viewUpto D v n) b).card ≤ κb) :
    (viewUpto D v (n + 1)).card ≤
      (viewUpto D v n).card +
        ((Correct : Finset Validator).card * κc + F.f * κb) := by
  have hcover : viewUpto D v (n + 1) ⊆
      viewUpto D v n ∪
        (D.accepted v (n + 1)).biUnion (fun t => novelty U (viewUpto D v n) t) := by
    rw [viewUpto_succ]
    intro i hi
    rcases Finset.mem_union.mp hi with h | h
    · exact Finset.mem_union_left _ h
    · by_cases hiv : i ∈ viewUpto D v n
      · exact Finset.mem_union_left _ hiv
      · obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp h
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.mpr ⟨a, ha, mem_novelty.mpr ⟨hia, hiv⟩⟩)
  have hsum : ∑ t ∈ D.accepted v (n + 1), (novelty U (viewUpto D v n) t).card ≤
      (Correct : Finset Validator).card * κc + F.f * κb := by
    rw [← Finset.sum_filter_add_sum_filter_not (D.accepted v (n + 1))
      (fun t => (U.block t).creator ∈ (Correct : Finset Validator))]
    have hcs : ∑ t ∈ (D.accepted v (n + 1)).filter
          (fun t => (U.block t).creator ∈ (Correct : Finset Validator)),
        (novelty U (viewUpto D v n) t).card ≤
        (Correct : Finset Validator).card * κc :=
      calc ∑ t ∈ (D.accepted v (n + 1)).filter
            (fun t => (U.block t).creator ∈ (Correct : Finset Validator)),
            (novelty U (viewUpto D v n) t).card
          ≤ ∑ _t ∈ (D.accepted v (n + 1)).filter
              (fun t => (U.block t).creator ∈ (Correct : Finset Validator)), κc :=
            Finset.sum_le_sum fun t ht =>
              hc t (Finset.mem_of_mem_filter t ht) (Finset.mem_filter.mp ht).2
        _ = ((D.accepted v (n + 1)).filter
              (fun t => (U.block t).creator ∈ (Correct : Finset Validator))).card * κc :=
            Finset.sum_const_nat fun _ _ => rfl
        _ ≤ (Correct : Finset Validator).card * κc :=
            Nat.mul_le_mul_right κc (card_filter_correct_le v (n + 1))
    have hbs : ∑ t ∈ (D.accepted v (n + 1)).filter
          (fun t => (U.block t).creator ∉ (Correct : Finset Validator)),
        (novelty U (viewUpto D v n) t).card ≤ F.f * κb :=
      calc ∑ t ∈ (D.accepted v (n + 1)).filter
            (fun t => (U.block t).creator ∉ (Correct : Finset Validator)),
            (novelty U (viewUpto D v n) t).card
          ≤ ∑ _t ∈ (D.accepted v (n + 1)).filter
              (fun t => (U.block t).creator ∉ (Correct : Finset Validator)), κb :=
            Finset.sum_le_sum fun t ht =>
              hbz t (Finset.mem_of_mem_filter t ht) (Finset.mem_filter.mp ht).2
        _ = ((D.accepted v (n + 1)).filter
              (fun t => (U.block t).creator ∉ (Correct : Finset Validator))).card * κb :=
            Finset.sum_const_nat fun _ _ => rfl
        _ ≤ F.f * κb := Nat.mul_le_mul_right κb (card_filter_not_correct_le v (n + 1))
    omega
  calc (viewUpto D v (n + 1)).card
      ≤ (viewUpto D v n ∪
          (D.accepted v (n + 1)).biUnion
            (fun t => novelty U (viewUpto D v n) t)).card :=
        Finset.card_le_card hcover
    _ ≤ (viewUpto D v n).card +
          ((D.accepted v (n + 1)).biUnion
            (fun t => novelty U (viewUpto D v n) t)).card :=
        Finset.card_union_le _ _
    _ ≤ (viewUpto D v n).card +
          ∑ t ∈ D.accepted v (n + 1), (novelty U (viewUpto D v n) t).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ (viewUpto D v n).card +
          ((Correct : Finset Validator).card * κc + F.f * κb) :=
        Nat.add_le_add_left hsum _

/-- One round of growth: `|Correct|` acceptances at `Κ` plus `f` at `κ`. -/
theorem card_viewUpto_succ_le {κ Κ : ℕ} (hbud : NoveltyBudget D κ Κ)
    (hv : v ∈ (Correct : Finset Validator)) (n : ℕ) :
    (viewUpto D v (n + 1)).card ≤
      (viewUpto D v n).card +
        ((Correct : Finset Validator).card * Κ + F.f * κ) :=
  card_viewUpto_succ_le_of_bounds
    (fun b hb hbc => by have h := hbud v hv n b hb; rwa [if_pos hbc] at h)
    (fun b hb hbc => by have h := hbud v hv n b hb; rwa [if_neg hbc] at h)

/-- Round 0 is free: at most `3f+1` genesis singletons. -/
theorem card_viewUpto_zero_le : (viewUpto D v 0).card ≤ 3 * F.f + 1 := by
  calc (viewUpto D v 0).card
      ≤ ∑ a ∈ D.accepted v 0, (history U a).card := Finset.card_biUnion_le
    _ = ∑ _a ∈ D.accepted v 0, 1 :=
        Finset.sum_congr rfl fun a ha => by
          obtain ⟨ha_ids, ha_round⟩ := D.held_spec v 0 a (D.accepted_sub v 0 ha)
          rw [history_eq_singleton_of_round_zero ha_ids ha_round,
            Finset.card_singleton]
    _ = (D.accepted v 0).card := by simp
    _ ≤ 3 * F.f + 1 := by
        have himg : ((D.accepted v 0).image fun i => (U.block i).creator).card =
            (D.accepted v 0).card :=
          Finset.card_image_of_injOn fun i hi j hj hij =>
            D.accepted_inj v 0 i hi j hj hij
        rw [← himg, ← F.card_validators, ← Finset.card_univ]
        exact Finset.card_le_univ _

/-- **B3.** Under the novelty budget, a correct validator's accumulated view
is linear in the round: `(3f+1) + (|Correct|·Κ + f·κ)·n`. At `β = f` the
increment is `(2f+1)·Κ + f·κ` — §10.7's constant. -/
theorem card_viewUpto_le {κ Κ : ℕ} (hbud : NoveltyBudget D κ Κ)
    (hv : v ∈ (Correct : Finset Validator)) (n : ℕ) :
    (viewUpto D v n).card ≤
      (3 * F.f + 1) + ((Correct : Finset Validator).card * Κ + F.f * κ) * n := by
  induction n with
  | zero => simpa using card_viewUpto_zero_le (D := D) (v := v)
  | succ n ih =>
      have hstep := card_viewUpto_succ_le hbud hv n
      have hmul : ((Correct : Finset Validator).card * Κ + F.f * κ) * (n + 1) =
          ((Correct : Finset Validator).card * Κ + F.f * κ) * n +
            ((Correct : Finset Validator).card * Κ + F.f * κ) :=
        Nat.mul_succ _ _
      omega

/-- The D3 direction: a block whose references were all accepted costs at
most one more than the accumulated view. -/
theorem card_history_le_card_viewUpto_add_one (hb : b ∈ U.ids)
    (hrefs : (U.block b).refs ⊆ D.accepted v n) :
    (history U b).card ≤ (viewUpto D v n).card + 1 := by
  have hsub : history U b ⊆ insert b (viewUpto D v n) := by
    intro i hi
    rcases (mem_history_succ_iff hb).mp hi with rfl | ⟨j, hj, hij⟩
    · exact Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem
        (history_subset_viewUpto (le_refl n) (hrefs hj) hij)
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- **B3, through the D3 bridge**: the history of a correct validator's own
next block is linear in the round — the shape §10.6 proves unreachable
without the budget. -/
theorem card_history_le_of_noveltyBudget {κ Κ : ℕ} (hbud : NoveltyBudget D κ Κ)
    (hv : v ∈ (Correct : Finset Validator)) (hb : b ∈ U.ids)
    (hrefs : (U.block b).refs ⊆ D.accepted v n) :
    (history U b).card ≤
      (3 * F.f + 1) +
        ((Correct : Finset Validator).card * Κ + F.f * κ) * n + 1 :=
  (card_history_le_card_viewUpto_add_one hb hrefs).trans
    (Nat.add_le_add_right (card_viewUpto_le hbud hv n) 1)

/-! ## C3 — the liveness half

What a correct validator must be willing to fetch so that no correct block
is ever deferred. The answer: one plus the standing *view gap* toward the
block's author — and the gap grows only by the budget's own Byzantine
spend, `f·κ` per round. The adversary's hidden mass never appears in
either bound. -/

/-- The standing divergence between two correct validators' retained views:
what `w` holds that `v` does not. -/
def viewGap (D : Delivery U) (v w : Validator) (n : ℕ) : Finset BlockId :=
  viewUpto D w n \ viewUpto D v n

/-- **C3a.** After `R`, a block built from `w`'s acceptances is, at any
correct `v`, at most one plus the gap toward `w`: its correct references
are shared (delivered and accepted at `v` too), and its Byzantine
references sit whole inside `w`'s view. -/
theorem card_novelty_le_viewGap_add_one {R : ℕ} (hED : EventuallyDelivers D R)
    (hn : R ≤ n) (hv : v ∈ (Correct : Finset Validator)) (hb : b ∈ U.ids)
    (hrefs : (U.block b).refs ⊆ D.accepted w n) :
    (novelty U (viewUpto D v n) b).card ≤ (viewGap D v w n).card + 1 := by
  have hsub : novelty U (viewUpto D v n) b ⊆ insert b (viewGap D v w n) := by
    intro i hi
    obtain ⟨hih, hiv⟩ := mem_novelty.mp hi
    rcases (mem_history_succ_iff hb).mp hih with rfl | ⟨t, ht, hit⟩
    · exact Finset.mem_insert_self _ _
    · have htw : t ∈ D.accepted w n := hrefs ht
      obtain ⟨ht_ids, ht_round⟩ := D.held_spec w n t (D.accepted_sub w n htw)
      by_cases htc : (U.block t).creator ∈ (Correct : Finset Validator)
      · exact absurd (history_subset_viewUpto (le_refl n)
          (D.accepts_correct v hv n t (hED n hn v hv t ht_ids ht_round htc) htc)
          hit) hiv
      · exact Finset.mem_insert_of_mem (Finset.mem_sdiff.mpr
          ⟨history_subset_viewUpto (le_refl n) htw hit, hiv⟩)
  exact (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)

/-- **C3b.** After `R` the gap grows by at most `f·κ` per round: correct
acceptances are shared, and Byzantine ones are budgeted at the moment `w`
takes them. -/
theorem card_viewGap_succ_le {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hn : R ≤ n + 1)
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) :
    (viewGap D v w (n + 1)).card ≤ (viewGap D v w n).card + F.f * κ := by
  have hsub : viewGap D v w (n + 1) ⊆
      viewGap D v w n ∪
        ((D.accepted w (n + 1)).filter
          (fun t => (U.block t).creator ∉ (Correct : Finset Validator))).biUnion
          (fun t => novelty U (viewUpto D w n) t) := by
    intro i hi
    obtain ⟨hiw, hiv⟩ := Finset.mem_sdiff.mp hi
    have hiv' : i ∉ viewUpto D v n := fun h => hiv (viewUpto_mono (Nat.le_succ n) h)
    rw [viewUpto_succ] at hiw
    rcases Finset.mem_union.mp hiw with h | h
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨h, hiv'⟩)
    · obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp h
      obtain ⟨ht_ids, ht_round⟩ :=
        D.held_spec w (n + 1) t (D.accepted_sub w (n + 1) ht)
      by_cases htc : (U.block t).creator ∈ (Correct : Finset Validator)
      · exact absurd (history_subset_viewUpto (le_refl (n + 1))
          (D.accepts_correct v hv (n + 1) t
            (hED (n + 1) hn v hv t ht_ids ht_round htc) htc) hit) hiv
      · by_cases hiw' : i ∈ viewUpto D w n
        · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hiw', hiv'⟩)
        · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
            ⟨t, Finset.mem_filter.mpr ⟨ht, htc⟩, mem_novelty.mpr ⟨hit, hiw'⟩⟩)
  calc (viewGap D v w (n + 1)).card
      ≤ (viewGap D v w n ∪
          ((D.accepted w (n + 1)).filter
            (fun t => (U.block t).creator ∉ (Correct : Finset Validator))).biUnion
            (fun t => novelty U (viewUpto D w n) t)).card :=
        Finset.card_le_card hsub
    _ ≤ (viewGap D v w n).card +
          (((D.accepted w (n + 1)).filter
            (fun t => (U.block t).creator ∉ (Correct : Finset Validator))).biUnion
            (fun t => novelty U (viewUpto D w n) t)).card :=
        Finset.card_union_le _ _
    _ ≤ (viewGap D v w n).card +
          ∑ t ∈ (D.accepted w (n + 1)).filter
            (fun t => (U.block t).creator ∉ (Correct : Finset Validator)),
            (novelty U (viewUpto D w n) t).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ (viewGap D v w n).card + F.f * κ :=
        Nat.add_le_add_left (sum_novelty_not_correct_le hbyz hw n) _

/-- **C3c.** The gap, telescoped from `R`: the standing divergence at `R`
plus the budget's spend rate. Nothing else — in particular, nothing the
adversary built in private. -/
theorem card_viewGap_le {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) (hn : R ≤ n) :
    (viewGap D v w n).card ≤ (viewGap D v w R).card + (n - R) * (F.f * κ) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hRn ih =>
      have hstep := card_viewGap_succ_le hbyz hED (hRn.trans (Nat.le_succ n)) hv hw
      have hsub : n + 1 - R = (n - R) + 1 := by omega
      calc (viewGap D v w (n + 1)).card
          ≤ (viewGap D v w n).card + F.f * κ := hstep
        _ ≤ ((viewGap D v w R).card + (n - R) * (F.f * κ)) + F.f * κ :=
            Nat.add_le_add_right ih _
        _ = (viewGap D v w R).card + (n + 1 - R) * (F.f * κ) := by
            rw [hsub, Nat.succ_mul, Nat.add_assoc]

/-- **C3.** After `R`, the hysteresis threshold a correct block ever needs
is `gap(R) + (n-R)·f·κ + 1`: the divergence standing at `R`, the budget's
own spend since, and the block itself. The adversary's hidden mass never
enters — which is what makes a bounded `Κ` satisfiable, and the contagion
attack of §10.7 harmless. -/
theorem card_novelty_correct_le {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hn : R ≤ n)
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) (hb : b ∈ U.ids)
    (hrefs : (U.block b).refs ⊆ D.accepted w n) :
    (novelty U (viewUpto D v n) b).card ≤
      (viewGap D v w R).card + (n - R) * (F.f * κ) + 1 :=
  (card_novelty_le_viewGap_add_one hED hn hv hb hrefs).trans
    (Nat.add_le_add_right (card_viewGap_le hbyz hED hv hw hn) 1)

/-! ## The gap collapses — the DAG is its own repair channel

`card_viewGap_le` above lets the gap drift by `f·κ` per round, which would
make the hysteresis threshold a function of time. It does not drift. The
repair mechanism §10.7 asked for already exists in `Delivery`: `includes`
puts every round's acceptances among the next block's references, and the
self-parent chain (S10) carries every earlier round forward — so a correct
validator's block is, in its cone, a complete record of everything its
author ever accepted. One such block delivered post-`R` erases the whole
standing gap; what remains is at most the author's *current* Byzantine
frontier, priced by the budget. No cone-sharing protocol is needed. -/

/-- A correct validator's block carries everything its author ever
accepted: `includes` per round, chained by the self-parent (S10). -/
theorem viewUpto_subset_history (hw : w ∈ (Correct : Finset Validator))
    {b : BlockId} (hb : b ∈ U.ids) (hbc : (U.block b).creator = w)
    (hbr : (U.block b).round = n + 1) :
    viewUpto D w n ⊆ history U b := by
  induction n generalizing b with
  | zero =>
      intro i hi
      obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp hi
      exact history_subset_of_reaches hb
        (Reaches.single (D.includes w hw 0 b hb hbc hbr ht)) hit
  | succ n ih =>
      intro i hi
      rw [viewUpto_succ] at hi
      rcases Finset.mem_union.mp hi with h | h
      · obtain ⟨p, hp, hpc⟩ := (U.valid b hb).self_parent (by omega)
        have hp_ids : p ∈ U.ids := U.complete b hb p hp
        have hp_round : (U.block p).round + 1 = (U.block b).round :=
          U.round_of_mem_refs hb hp
        exact history_subset_of_reaches hb (Reaches.single hp)
          (ih hp_ids (hpc.trans hbc) (by omega) h)
      · obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp h
        exact history_subset_of_reaches hb
          (Reaches.single (D.includes w hw (n + 1) b hb hbc hbr ht)) hit

/-- **C3′ — the gap is constant, not a drift.** After `R`, as long as the
author has a current block (which L1 supplies), the divergence between two
correct validators' views is at most **one round of Byzantine budget**:
`w`'s round-`(n+1)` block hands `v` all of `viewUpto w n` at once, and the
remainder is `w`'s budgeted Byzantine frontier. -/
theorem card_viewGap_succ_le_of_block {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hn : R ≤ n + 1)
    (hv : v ∈ (Correct : Finset Validator))
    (hw : w ∈ (Correct : Finset Validator)) {c : BlockId} (hc : c ∈ U.ids)
    (hcc : (U.block c).creator = w) (hcr : (U.block c).round = n + 1) :
    (viewGap D v w (n + 1)).card ≤ F.f * κ := by
  have hcheld : c ∈ D.held v (n + 1) :=
    hED (n + 1) hn v hv c hc hcr (by rw [hcc]; exact hw)
  have hcacc : c ∈ D.accepted v (n + 1) :=
    D.accepts_correct v hv (n + 1) c hcheld (by rw [hcc]; exact hw)
  have hwv : viewUpto D w n ⊆ viewUpto D v (n + 1) :=
    (viewUpto_subset_history hw hc hcc hcr).trans
      (history_subset_viewUpto (le_refl (n + 1)) hcacc)
  have hsub : viewGap D v w (n + 1) ⊆
      ((D.accepted w (n + 1)).filter
        (fun t => (U.block t).creator ∉ (Correct : Finset Validator))).biUnion
        (fun t => novelty U (viewUpto D w n) t) := by
    intro i hi
    obtain ⟨hiw, hiv⟩ := Finset.mem_sdiff.mp hi
    rw [viewUpto_succ] at hiw
    rcases Finset.mem_union.mp hiw with h | h
    · exact absurd (hwv h) hiv
    · obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp h
      obtain ⟨ht_ids, ht_round⟩ :=
        D.held_spec w (n + 1) t (D.accepted_sub w (n + 1) ht)
      by_cases htc : (U.block t).creator ∈ (Correct : Finset Validator)
      · exact absurd (history_subset_viewUpto (le_refl (n + 1))
          (D.accepts_correct v hv (n + 1) t
            (hED (n + 1) hn v hv t ht_ids ht_round htc) htc) hit) hiv
      · exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, htc⟩,
          mem_novelty.mpr ⟨hit, fun hmem => hiv (hwv hmem)⟩⟩
  exact (Finset.card_le_card hsub).trans
    (Finset.card_biUnion_le.trans (sum_novelty_not_correct_le hbyz hw n))

/-- **C3″ — the correct side of the budget is a theorem.** A validator
enforcing only the Byzantine clause `κ` never meets a correct block over
`f·κ + 1` after `R`: the gap toward its author, collapsed through the
author's own self-parent, plus the block itself. So the hysteresis
threshold is the *constant* `Κ = f·κ + 1` — derived, not assumed, and
better than §10.7's designed `f·κ + 3f+1`. -/
theorem card_novelty_le_of_byzBudget {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hn : R ≤ n + 1)
    (hv : v ∈ (Correct : Finset Validator)) (hb : b ∈ U.ids)
    (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hbr : (U.block b).round = n + 2)
    (hrefs : (U.block b).refs ⊆ D.accepted (U.block b).creator (n + 1)) :
    (novelty U (viewUpto D v (n + 1)) b).card ≤ F.f * κ + 1 := by
  obtain ⟨p, hp, hpc⟩ := (U.valid b hb).self_parent (by omega)
  have hp_ids : p ∈ U.ids := U.complete b hb p hp
  have hp_round : (U.block p).round + 1 = (U.block b).round :=
    U.round_of_mem_refs hb hp
  exact (card_novelty_le_viewGap_add_one hED hn hv hb hrefs).trans
    (Nat.add_le_add_right
      (card_viewGap_succ_le_of_block hbyz hED hn hv hbc hp_ids hpc (by omega)) 1)

/-! ## The capstone — liveness and storage from one set of hypotheses -/

/-- D3's ordinary case as a protocol property: a correct validator's block
references **only** what it accepted — the converse of `includes`;
together they say `refs = accepted`. -/
def RefsAccepted (D : Delivery U) : Prop :=
  ∀ w ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = w → (U.block b).round = n + 1 →
    (U.block b).refs ⊆ D.accepted w n

/-- **B3′ — linear storage from the enforceable rule alone.** After `R`, a
correct validator's view grows by at most
`|Correct|·(f·κ + 1) + f·κ` per round, under nothing but the Byzantine
budget and the reference discipline: the correct side is supplied by
C3″. -/
theorem card_viewUpto_le_of_byzBudget {κ R : ℕ} (hbyz : ByzBudget D κ)
    (hED : EventuallyDelivers D R) (hra : RefsAccepted D)
    (hv : v ∈ (Correct : Finset Validator)) {n : ℕ} (hn : R + 1 ≤ n) :
    (viewUpto D v n).card ≤ (viewUpto D v (R + 1)).card +
      (n - (R + 1)) *
        ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ) := by
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hRn ih =>
      obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
      have hstep : (viewUpto D v (m + 2)).card ≤ (viewUpto D v (m + 1)).card +
          ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ) := by
        refine card_viewUpto_succ_le_of_bounds ?_ ?_
        · intro b hb hbc
          obtain ⟨hb_ids, hb_round⟩ :=
            D.held_spec v (m + 2) b (D.accepted_sub v (m + 2) hb)
          exact card_novelty_le_of_byzBudget hbyz hED (by omega) hv hb_ids hbc
            hb_round (hra (U.block b).creator hbc (m + 1) b hb_ids rfl hb_round)
        · intro b hb hbc
          exact hbyz v hv (m + 1) b hb hbc
      have hsub : m + 2 - (R + 1) = (m + 1 - (R + 1)) + 1 := by omega
      calc (viewUpto D v (m + 2)).card
          ≤ (viewUpto D v (m + 1)).card +
              ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ) :=
            hstep
        _ ≤ ((viewUpto D v (R + 1)).card +
              (m + 1 - (R + 1)) *
                ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ)) +
              ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ) :=
            Nat.add_le_add_right ih _
        _ = (viewUpto D v (R + 1)).card +
              (m + 2 - (R + 1)) *
                ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ) := by
            rw [hsub, Nat.succ_mul, Nat.add_assoc]

/-- **The composed statement — DoS resistance in one theorem.** One set of
hypotheses — growth (`Live`), quorum delivery, post-`R` delivery, the
*enforceable* budget, and the reference discipline — supports liveness and
linear storage **simultaneously**: no correct validator ever stalls, and no
correct validator's retained view grows faster than
`|Correct|·(f·κ+1) + f·κ` per round. The two conclusions do not compete:
liveness never needs a Byzantine block (D15b, and post-`R` the quorum is
derivable from the correct set alone,
`card_creators_accepted_of_eventuallyDelivers`), and by C3″ enforcing the
budget never defers a correct one. -/
theorem no_stall_and_card_viewUpto_le {κ R N : ℕ} (H : Live U D N)
    (hd : DeliversQuorum D) (hED : EventuallyDelivers D R)
    (hbyz : ByzBudget D κ) (hra : RefsAccepted D) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n, R + 1 ≤ n →
        (viewUpto D v n).card ≤ (viewUpto D v (R + 1)).card +
          (n - (R + 1)) *
            ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ) :=
  ⟨no_stall H hd, fun _v hv _n hn => card_viewUpto_le_of_byzBudget hbyz hED hra hv hn⟩

/-! ## B4 — unconditional linear storage

The capstone above still measures from a post-`R` base. That base is
itself linear, and for a reason that needs no synchrony at all: **every
Byzantine block in any correct view entered through some correct
validator's budgeted acceptance.** A Byzantine block reaches a correct
view either as a direct acceptance — priced `≤ κ` by `ByzBudget` — or
inside an accepted *correct* block's cone; but a correct block's cone sits
inside its author's own earlier view (`RefsAccepted`), so the mass was
already in the pool. The global Byzantine pool therefore grows by at most
`|Correct|·f·κ` per round from round 0, with no delivery guarantee
anywhere — which closes the pre-`R` residue of §10.7 and makes the DoS
bound fully asynchronous. -/

theorem viewUpto_subset_ids : viewUpto D v n ⊆ U.ids := by
  induction n with
  | zero =>
      intro i hi
      obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
      exact history_subset_ids (D.held_spec v 0 a (D.accepted_sub v 0 ha)).1 hia
  | succ n ih =>
      intro i hi
      rw [viewUpto_succ] at hi
      rcases Finset.mem_union.mp hi with h | h
      · exact ih h
      · obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp h
        exact history_subset_ids
          (D.held_spec v (n + 1) a (D.accepted_sub v (n + 1) ha)).1 hia

theorem viewUpto_zero_eq : viewUpto D v 0 = D.accepted v 0 := by
  apply Finset.Subset.antisymm
  · intro i hi
    obtain ⟨a, ha, hia⟩ := Finset.mem_biUnion.mp hi
    obtain ⟨ha_ids, ha_round⟩ := D.held_spec v 0 a (D.accepted_sub v 0 ha)
    rw [history_eq_singleton_of_round_zero ha_ids ha_round,
      Finset.mem_singleton] at hia
    exact hia ▸ ha
  · intro a ha
    exact Finset.mem_biUnion.mpr ⟨a, ha, mem_history_self⟩

/-- The correct part of a view counts itself: one block per correct author
per round (`no_equivocation`), so at most `|Correct|·(n+1)`. -/
private theorem card_filter_correct_viewUpto_le (v : Validator) (n : ℕ) :
    ((viewUpto D v n).filter
      fun i => (U.block i).creator ∈ (Correct : Finset Validator)).card ≤
      (Correct : Finset Validator).card * (n + 1) := by
  calc ((viewUpto D v n).filter
        fun i => (U.block i).creator ∈ (Correct : Finset Validator)).card
      ≤ ((Correct : Finset Validator) ×ˢ Finset.range (n + 1)).card := by
        refine Finset.card_le_card_of_injOn
          (fun i => ((U.block i).creator, (U.block i).round)) ?_ ?_
        · intro i hi
          obtain ⟨hiv, hic⟩ := Finset.mem_filter.mp hi
          have hr : (U.block i).round < n + 1 := by
            have := round_le_of_mem_viewUpto hiv; omega
          exact Finset.mem_product.mpr ⟨hic, Finset.mem_range.mpr hr⟩
        · intro i hi j hj hij
          simp only [Finset.mem_coe, Finset.mem_filter] at hi hj
          have h1 : (U.block i).creator = (U.block j).creator :=
            congrArg Prod.fst hij
          have h2 : (U.block i).round = (U.block j).round :=
            congrArg Prod.snd hij
          exact U.no_equivocation i (viewUpto_subset_ids hi.1) j
            (viewUpto_subset_ids hj.1) hi.2 h1 h2
    _ = (Correct : Finset Validator).card * (n + 1) := by
        rw [Finset.card_product, Finset.card_range]

/-- The **global Byzantine pool**: every Byzantine-authored block sitting
in any correct validator's retained view. -/
def byzPool (D : Delivery U) (n : ℕ) : Finset BlockId :=
  (Correct : Finset Validator).biUnion fun w =>
    (viewUpto D w n).filter
      fun i => (U.block i).creator ∉ (Correct : Finset Validator)

theorem mem_byzPool {i : BlockId} :
    i ∈ byzPool D n ↔ ∃ w ∈ (Correct : Finset Validator),
      i ∈ viewUpto D w n ∧
        (U.block i).creator ∉ (Correct : Finset Validator) := by
  constructor
  · intro h
    obtain ⟨w, hw, hmem⟩ := Finset.mem_biUnion.mp h
    obtain ⟨hiv, hic⟩ := Finset.mem_filter.mp hmem
    exact ⟨w, hw, hiv, hic⟩
  · rintro ⟨w, hw, hiv, hic⟩
    exact Finset.mem_biUnion.mpr ⟨w, hw, Finset.mem_filter.mpr ⟨hiv, hic⟩⟩

/-- Round 0 seeds the pool with at most `f` Byzantine geneses per correct
validator. -/
theorem card_byzPool_zero_le :
    (byzPool D 0).card ≤ (Correct : Finset Validator).card * F.f :=
  calc (byzPool D 0).card
      ≤ ∑ w ∈ (Correct : Finset Validator),
          ((viewUpto D w 0).filter
            fun i => (U.block i).creator ∉ (Correct : Finset Validator)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ _w ∈ (Correct : Finset Validator), F.f :=
        Finset.sum_le_sum fun w _ => by
          rw [viewUpto_zero_eq]
          exact card_filter_not_correct_le w 0
    _ = (Correct : Finset Validator).card * F.f :=
        Finset.sum_const_nat fun _ _ => rfl

/-- **The accounting step.** A Byzantine block enters the pool only as a
direct budgeted acceptance: if it arrived inside a correct block's cone,
`RefsAccepted` puts it in that block's author's *earlier* view — it was in
the pool already. So the pool grows by at most `|Correct|·f·κ` per round. -/
theorem card_byzPool_succ_le {κ : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (n : ℕ) :
    (byzPool D (n + 1)).card ≤
      (byzPool D n).card + (Correct : Finset Validator).card * (F.f * κ) := by
  have hsub : byzPool D (n + 1) ⊆ byzPool D n ∪
      (Correct : Finset Validator).biUnion (fun w =>
        ((D.accepted w (n + 1)).filter
          fun t => (U.block t).creator ∉ (Correct : Finset Validator)).biUnion
          fun t => novelty U (viewUpto D w n) t) := by
    intro i hi
    obtain ⟨w, hw, hiv, hic⟩ := mem_byzPool.mp hi
    rw [viewUpto_succ] at hiv
    rcases Finset.mem_union.mp hiv with h | h
    · exact Finset.mem_union_left _ (mem_byzPool.mpr ⟨w, hw, h, hic⟩)
    · obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp h
      by_cases hiw : i ∈ viewUpto D w n
      · exact Finset.mem_union_left _ (mem_byzPool.mpr ⟨w, hw, hiw, hic⟩)
      obtain ⟨ht_ids, ht_round⟩ :=
        D.held_spec w (n + 1) t (D.accepted_sub w (n + 1) ht)
      by_cases htc : (U.block t).creator ∈ (Correct : Finset Validator)
      · -- inside a correct block's cone: already in its author's view
        rcases (mem_history_succ_iff ht_ids).mp hit with rfl | ⟨s, hs, his⟩
        · exact absurd htc hic
        · exact Finset.mem_union_left _ (mem_byzPool.mpr
            ⟨(U.block t).creator, htc,
              history_subset_viewUpto (le_refl n)
                (hra (U.block t).creator htc n t ht_ids rfl ht_round hs) his,
              hic⟩)
      · -- a direct Byzantine acceptance: fresh, budgeted novelty
        exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨w, hw,
          Finset.mem_biUnion.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, htc⟩,
            mem_novelty.mpr ⟨hit, hiw⟩⟩⟩)
  calc (byzPool D (n + 1)).card
      ≤ (byzPool D n ∪
          (Correct : Finset Validator).biUnion (fun w =>
            ((D.accepted w (n + 1)).filter
              fun t => (U.block t).creator ∉ (Correct : Finset Validator)).biUnion
              fun t => novelty U (viewUpto D w n) t)).card :=
        Finset.card_le_card hsub
    _ ≤ (byzPool D n).card +
          ((Correct : Finset Validator).biUnion (fun w =>
            ((D.accepted w (n + 1)).filter
              fun t => (U.block t).creator ∉ (Correct : Finset Validator)).biUnion
              fun t => novelty U (viewUpto D w n) t)).card :=
        Finset.card_union_le _ _
    _ ≤ (byzPool D n).card +
          ∑ w ∈ (Correct : Finset Validator),
            (((D.accepted w (n + 1)).filter
              fun t => (U.block t).creator ∉ (Correct : Finset Validator)).biUnion
              fun t => novelty U (viewUpto D w n) t).card :=
        Nat.add_le_add_left Finset.card_biUnion_le _
    _ ≤ (byzPool D n).card + ∑ _w ∈ (Correct : Finset Validator), F.f * κ :=
        Nat.add_le_add_left (Finset.sum_le_sum fun w hw =>
          Finset.card_biUnion_le.trans (sum_novelty_not_correct_le hbyz hw n)) _
    _ = (byzPool D n).card + (Correct : Finset Validator).card * (F.f * κ) := by
        rw [Finset.sum_const_nat fun _ _ => rfl]

/-- The pool, telescoped: linear from round 0. -/
theorem card_byzPool_le {κ : ℕ} (hbyz : ByzBudget D κ) (hra : RefsAccepted D)
    (n : ℕ) :
    (byzPool D n).card ≤ (Correct : Finset Validator).card * F.f +
      n * ((Correct : Finset Validator).card * (F.f * κ)) := by
  induction n with
  | zero => simpa using card_byzPool_zero_le (D := D)
  | succ n ih =>
      have hstep := card_byzPool_succ_le hbyz hra n
      have hmul : (n + 1) * ((Correct : Finset Validator).card * (F.f * κ)) =
          n * ((Correct : Finset Validator).card * (F.f * κ)) +
            (Correct : Finset Validator).card * (F.f * κ) :=
        Nat.succ_mul _ _
      omega

/-- **B4 — unconditional linear storage.** Under nothing but the
enforceable budget and the reference discipline — no synchrony, no `R`, no
delivery guarantee — every correct validator's retained view is linear in
the round: at most one block per correct author per round, plus the global
Byzantine pool. This is the §10.7 pre-`R` conjecture, closed: the base the
capstone measures from is itself linear, so the DoS bound holds from
round 0 under full asynchrony. -/
theorem card_viewUpto_le_of_refsAccepted {κ : ℕ} (hbyz : ByzBudget D κ)
    (hra : RefsAccepted D) (hv : v ∈ (Correct : Finset Validator)) (n : ℕ) :
    (viewUpto D v n).card ≤
      (Correct : Finset Validator).card * (n + 1) +
        ((Correct : Finset Validator).card * F.f +
          n * ((Correct : Finset Validator).card * (F.f * κ))) := by
  have hbyzpart : ((viewUpto D v n).filter
      fun i => (U.block i).creator ∉ (Correct : Finset Validator)).card ≤
      (byzPool D n).card :=
    Finset.card_le_card fun i hi => by
      obtain ⟨hiv, hic⟩ := Finset.mem_filter.mp hi
      exact mem_byzPool.mpr ⟨v, hv, hiv, hic⟩
  calc (viewUpto D v n).card
      = ((viewUpto D v n).filter
          fun i => (U.block i).creator ∈ (Correct : Finset Validator)).card +
        ((viewUpto D v n).filter
          fun i => (U.block i).creator ∉ (Correct : Finset Validator)).card :=
        (Finset.card_filter_add_card_filter_not _).symm
    _ ≤ (Correct : Finset Validator).card * (n + 1) +
          ((Correct : Finset Validator).card * F.f +
            n * ((Correct : Finset Validator).card * (F.f * κ))) :=
        Nat.add_le_add (card_filter_correct_viewUpto_le v n)
          (hbyzpart.trans (card_byzPool_le hbyz hra n))

/-- **The capstone, unconditional.** `EventuallyDelivers` is gone: growth
plus quorum delivery give liveness (L1 is asynchrony-only), and the
enforceable budget plus the reference discipline give linear storage from
round 0 — DoS resistance under full asynchrony, in one theorem. -/
theorem no_stall_and_card_viewUpto_le' {κ N : ℕ} (H : Live U D N)
    (hd : DeliversQuorum D) (hbyz : ByzBudget D κ) (hra : RefsAccepted D) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto D v n).card ≤
          (Correct : Finset Validator).card * (n + 1) +
            ((Correct : Finset Validator).card * F.f +
              n * ((Correct : Finset Validator).card * (F.f * κ))) :=
  ⟨no_stall H hd, fun _v hv n => card_viewUpto_le_of_refsAccepted hbyz hra hv n⟩

end LeanDag
