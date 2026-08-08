import LeanDag.DoS.Novelty
import LeanDag.DoS.Exclusion

/-!
# The two conditions, composed

`dos-equivocation-and-growth.md` §6. Theorem B (`dos_resistance`) does not
assume DoS validity; the budget alone bounds the Byzantine share of a
correct view by a *rate* — `|Correct|·f·κ` per round, sustained forever.
DoS validity is what terminates it. Once every Byzantine author is exposed
to the correct population (`AllExposed`), D17's propagation makes every
later valid block silent about every Byzantine author; through `includes`
a correct validator then *accepts* nothing Byzantine-authored, so the
global Byzantine pool freezes at its current value
(`byzPool_subset_of_allExposed`) — and the view bound's slope decays to
the correct-production rate:

> `|V_v(n)| ≤ |Correct|·(n+1) + |byzPool(m+1)|`   (**B5**)

for every `n ≥ m+1`: linear with slope `|Correct|`, Byzantine term
constant. With the budget the constant is explicit,
`|Correct|·f·(1 + (m+1)·κ)`. The division of labour, stated as one
theorem: the budget paces what an author can inject; exclusion ends it.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {D : Delivery U} {v w : Validator} {m n : ℕ}

/-- **Exposure-complete at `m`**: every correct block of round `m+1` is
exposed to every Byzantine author — the state D16 manufactures once all
`f` authors have equivocated toward the correct population. -/
def AllExposed (U : BlockUniverse Validator BlockId Payload) (m : ℕ) : Prop :=
  ∀ X : Validator, X ∉ (Correct : Finset Validator) →
    ∀ c ∈ U.ids, (U.block c).round = m + 1 →
      (U.block c).creator ∈ (Correct : Finset Validator) → ExposedIn U c X

instance : Decidable (AllExposed U m) := by
  unfold AllExposed; infer_instance

/-- After exposure-complete, a correct validator accepts nothing
Byzantine-authored: its next block would have to reference the acceptance
(`includes`), and D17 forbids any valid block that far up from naming an
exposed author. -/
theorem accepted_correct_of_allExposed (hdos : DoSValid U)
    (hexp : AllExposed U m) (hv : v ∈ (Correct : Finset Validator))
    (hn : m + 1 ≤ n)
    (hpop : ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n + 1) :
    ∀ t ∈ D.accepted v n, (U.block t).creator ∈ (Correct : Finset Validator) := by
  intro t ht
  by_contra htc
  obtain ⟨b, hb, hbc, hbr⟩ := hpop
  have href : t ∈ (U.block b).refs := D.includes v hv n b hb hbc hbr ht
  exact not_mem_creators_refs_of_correct_exposed hdos
    (hexp (U.block t).creator htc) hb (by omega)
    (mem_creatorsOf.mpr ⟨t, href, rfl⟩)

theorem byzPool_mono (h : m ≤ n) : byzPool D m ⊆ byzPool D n := by
  intro i hi
  obtain ⟨w, hw, hiv, hic⟩ := mem_byzPool.mp hi
  exact mem_byzPool.mpr ⟨w, hw, viewUpto_mono h hiv, hic⟩

/-- The freeze step: a round in which every correct acceptance is
correct-authored adds nothing to the pool — B4's accounting with the
Byzantine branch empty. -/
theorem byzPool_succ_subset (hra : RefsAccepted D)
    (hacc : ∀ w ∈ (Correct : Finset Validator), ∀ t ∈ D.accepted w (n + 1),
      (U.block t).creator ∈ (Correct : Finset Validator)) :
    byzPool D (n + 1) ⊆ byzPool D n := by
  intro i hi
  obtain ⟨w, hw, hiv, hic⟩ := mem_byzPool.mp hi
  rw [viewUpto_succ] at hiv
  rcases Finset.mem_union.mp hiv with h | h
  · exact mem_byzPool.mpr ⟨w, hw, h, hic⟩
  · obtain ⟨t, ht, hit⟩ := Finset.mem_biUnion.mp h
    obtain ⟨ht_ids, ht_round⟩ :=
      D.held_spec w (n + 1) t (D.accepted_sub w (n + 1) ht)
    have htc := hacc w hw t ht
    rcases (mem_history_succ_iff ht_ids).mp hit with rfl | ⟨s, hs, his⟩
    · exact absurd htc hic
    · exact mem_byzPool.mpr ⟨(U.block t).creator, htc,
        history_subset_viewUpto (le_refl n)
          (hra (U.block t).creator htc n t ht_ids rfl ht_round hs) his, hic⟩

/-- **The pool freezes.** After exposure-complete at `m`, the global
Byzantine pool never grows past its round-`(m+1)` value. Population is
needed only for the rounds actually stepped through — each correct
validator must have the next block whose references D17 constrains. -/
theorem byzPool_subset_of_allExposed (hdos : DoSValid U)
    (hra : RefsAccepted D) (hexp : AllExposed U m) (hn : m + 1 ≤ n)
    (hpop : ∀ r, m + 3 ≤ r → r ≤ n + 1 → Populated U r) :
    byzPool D n ⊆ byzPool D (m + 1) := by
  induction n, hn using Nat.le_induction with
  | base => exact Finset.Subset.refl _
  | succ n hmn ih =>
      refine (byzPool_succ_subset hra ?_).trans
        (ih fun r h1 h2 => hpop r h1 (by omega))
      intro w hw t ht
      exact accepted_correct_of_allExposed hdos hexp hw (by omega)
        (hpop (n + 2) (by omega) (by omega) w hw) t ht

/-- **B5 — the slope decays to the correct-production rate.** After
exposure-complete at `m`, a correct view is the correct part — one block
per author per round — plus a **constant**: the pool as it stood when the
last author was caught. The Byzantine term stops growing. -/
theorem card_viewUpto_le_of_allExposed (hdos : DoSValid U)
    (hra : RefsAccepted D) (hexp : AllExposed U m)
    (hv : v ∈ (Correct : Finset Validator)) (hn : m + 1 ≤ n)
    (hpop : ∀ r, m + 3 ≤ r → r ≤ n + 1 → Populated U r) :
    (viewUpto D v n).card ≤
      (Correct : Finset Validator).card * (n + 1) + (byzPool D (m + 1)).card := by
  have hbyzpart : ((viewUpto D v n).filter
      fun i => (U.block i).creator ∉ (Correct : Finset Validator)).card ≤
      (byzPool D (m + 1)).card := by
    refine Finset.card_le_card fun i hi => ?_
    obtain ⟨hiv, hic⟩ := Finset.mem_filter.mp hi
    exact byzPool_subset_of_allExposed hdos hra hexp hn hpop
      (mem_byzPool.mpr ⟨v, hv, hiv, hic⟩)
  calc (viewUpto D v n).card
      = ((viewUpto D v n).filter
          fun i => (U.block i).creator ∈ (Correct : Finset Validator)).card +
        ((viewUpto D v n).filter
          fun i => (U.block i).creator ∉ (Correct : Finset Validator)).card :=
        (Finset.card_filter_add_card_filter_not _).symm
    _ ≤ (Correct : Finset Validator).card * (n + 1) + (byzPool D (m + 1)).card :=
        Nat.add_le_add (card_viewUpto_filter_correct_le v n) hbyzpart

/-- **B5, with the constant made explicit by the budget**: the frozen pool
is at most `|Correct|·f·(1 + (m+1)·κ)`. The budget paces what an author
can inject before being caught; exclusion ends it — one theorem. -/
theorem card_viewUpto_le_of_allExposed' {κ : ℕ} (hdos : DoSValid U)
    (hbyz : ByzBudget D κ) (hra : RefsAccepted D) (hexp : AllExposed U m)
    (hv : v ∈ (Correct : Finset Validator)) (hn : m + 1 ≤ n)
    (hpop : ∀ r, m + 3 ≤ r → r ≤ n + 1 → Populated U r) :
    (viewUpto D v n).card ≤
      (Correct : Finset Validator).card * (n + 1) +
        ((Correct : Finset Validator).card * F.f +
          (m + 1) * ((Correct : Finset Validator).card * (F.f * κ))) :=
  (card_viewUpto_le_of_allExposed hdos hra hexp hv hn hpop).trans
    (Nat.add_le_add_left (card_byzPool_le hbyz hra (m + 1)) _)

end LeanDag
