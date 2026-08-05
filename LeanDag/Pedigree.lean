import LeanDag.Adoption
import Mathlib.Data.Fintype.BigOperators

/-!
# Pedigrees, and the general bound

`dos-equivocation-and-growth.md` §10.5, the multi-equivocator case — the
last open piece of C1′.

`Adoption.lean` closed the count when at most one author is exposed:
distinct tops need distinct namer authors. With several exposed authors that
argument stalls, because exposed chains can name each other's tops and the
flat per-cone system never grounds. What grounds it is **nesting**: an
adopted top lies *inside* its adopter's history, so iterating "who adopted
the adopter" climbs through strictly higher rounds and strictly nested
cones, and must end at `b` — the only unreferenced block. Three facts turn
that climb into a count:

1. **Pedigrees exist** (`exists_pedigree`): every top climbs to `b` through
   adopters, and the authors met on the way — together with the top's own —
   are **pairwise distinct**: a repeat would put the lower block on the
   repeated author's chain (D21/D22), handing it a child and unmaking the
   top.
2. **Pedigrees determine** (`pedigree_deterministic`): each step is unique —
   one adopted top per (adopter, author), by the adoption collapse — so a
   top is a function of its pedigree's *author list*.
3. **Author lists are few**: duplicate-free over `3f+1` validators, hence
   length at most `3f+1`, hence at most `(3f+2)^(3f+1)` of them (embedding
   lists into `Fin (3f+1) → Option Validator`).

Together: `|topsOf U b X| ≤ (3f+2)^(3f+1) =: c(f)`, and therefore

> **C1′** (`card_historyBlocksOf_le`): an author contributes at most `c(f)`
> blocks *per round* to any history, and
> **the general bound** (`card_history_le`):
> `|H(b)| ≤ (3f+1)·c(f)·(r+1)` — linear in `r`, for every `f`.

`c(f)` is astronomically loose — the `f ≤ 1` theorem gives `7(r+1)` where
this gives `4·5⁴·(r+1)` — but it is *constant in `r`*, which is the whole
of C1′: no compounding, at any fault budget.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The block itself tops its own chain: nothing in its history can
reference it. -/
theorem self_mem_topsOf {b : BlockId} (hb : b ∈ U.ids) :
    b ∈ topsOf U b (U.block b).creator := by
  refine mem_topsOf.mpr ⟨mem_history_self, rfl, ?_⟩
  intro c hc _ hbc
  have hc_ids := history_subset_ids hb hc
  have h1 := U.round_of_mem_refs hc_ids hbc
  have h2 := round_le_of_mem_history hb hc
  omega

/-- A same-author block strictly inside a history is on the root's chain
(D21/D22), so it has a same-author child there. The tool that unmakes
would-be tops. -/
theorem exists_child_of_mem_history_of_creator_eq (hdos : DoSValid U) {s t : BlockId}
    (hs : s ∈ U.ids) (hts : t ∈ history U s)
    (hc : (U.block t).creator = (U.block s).creator) (hne : t ≠ s) :
    ∃ q ∈ history U s, (U.block q).creator = (U.block s).creator ∧
      t ∈ (U.block q).refs := by
  have hle := round_le_of_mem_history hs hts
  have hlt : (U.block t).round < (U.block s).round := by
    rcases Nat.lt_or_ge (U.block t).round (U.block s).round with h | h
    · exact h
    · exact absurd (eq_of_mem_history_of_round_eq hs hts (by omega)) hne
  obtain ⟨q, hq, hqc, hqr⟩ := exists_self_ancestor hs
    (t := (U.block t).round + 1) (by omega)
  have hq_ids := history_subset_ids hs hq
  obtain ⟨p, hp, hpc⟩ := (U.valid q hq_ids).self_parent (by omega)
  have hpr := U.round_of_mem_refs hq_ids hp
  have hqsub : history U q ⊆ history U s :=
    history_subset_of_reaches hs ((mem_history_iff hs).mp hq)
  have hpt : p = t :=
    eq_of_not_exposedIn (not_exposedIn_self_creator hdos hs)
      (hqsub (mem_history_of_mem_refs hq_ids hp)) hts
      (hpc.trans hqc) hc (by omega)
  exact ⟨q, hq, hqc, hpt ▸ hp⟩

/-- `t` is adopted under `T`: some block of `T`'s own author, inside `T`'s
history, references `t`. By D21/D22 such a block sits on `T`'s chain, so
per (`T`, author-of-`t`) the adopted top is unique
(`top_eq_of_mem_namer_history`). -/
def AdoptedUnder (U : BlockUniverse Validator BlockId Payload) (b t T : BlockId) : Prop :=
  ∃ j ∈ history U b, j ∈ history U T ∧
    (U.block j).creator = (U.block T).creator ∧ t ∈ (U.block j).refs

/-- An adoption pedigree: the climb from a top to `b`, recording the
adopters' authors. -/
inductive PedigreeTo (U : BlockUniverse Validator BlockId Payload) (b : BlockId) :
    BlockId → List Validator → Prop
  | base : PedigreeTo U b b []
  | step {t T : BlockId} {l : List Validator} :
      t ∈ topsOf U b (U.block t).creator →
      AdoptedUnder U b t T →
      PedigreeTo U b T l →
      PedigreeTo U b t ((U.block T).creator :: l)

/-- Every author on a pedigree is realised by a *top* strictly above the
pedigree's base, whose history contains the base. The nesting that makes
pedigree authors distinct. -/
theorem pedigree_spec {b : BlockId} (hb : b ∈ U.ids) {s : BlockId} {l : List Validator}
    (hped : PedigreeTo U b s l) :
    s ∈ history U b ∧
      ∀ W ∈ l, ∃ s', s' ∈ history U b ∧ (U.block s').creator = W ∧
        s' ∈ topsOf U b (U.block s').creator ∧ s ∈ history U s' ∧
        (U.block s).round < (U.block s').round := by
  induction hped with
  | base => exact ⟨mem_history_self, fun W hW => by simp at hW⟩
  | @step t T l htop hadopt hrest ih =>
      obtain ⟨j, hjb, hjT, hjc, htref⟩ := hadopt
      have hTb : T ∈ history U b := ih.1
      have hT_ids : T ∈ U.ids := history_subset_ids hb hTb
      have hj_ids : j ∈ U.ids := history_subset_ids hb hjb
      have htT : t ∈ history U T :=
        history_subset_of_reaches hT_ids ((mem_history_iff hT_ids).mp hjT)
          (mem_history_of_mem_refs hj_ids htref)
      have hround_tj := U.round_of_mem_refs hj_ids htref
      have hround_jT := round_le_of_mem_history hT_ids hjT
      refine ⟨(mem_topsOf.mp htop).1, ?_⟩
      intro W hW
      rcases List.mem_cons.mp hW with rfl | hWl
      · refine ⟨T, hTb, rfl, ?_, htT, by omega⟩
        cases hrest with
        | base => exact self_mem_topsOf hb
        | step htop' _ _ => exact htop'
      · obtain ⟨s', hs'b, hs'c, hs'top, hTs', hTr⟩ := ih.2 W hWl
        have hs'_ids : s' ∈ U.ids := history_subset_ids hb hs'b
        exact ⟨s', hs'b, hs'c, hs'top,
          history_subset_of_reaches hs'_ids ((mem_history_iff hs'_ids).mp hTs') htT,
          by omega⟩

/-- **Pedigrees exist, with fresh authors all the way.** Every top climbs to
`b` through adopters whose authors, together with its own, are pairwise
distinct — a repeated author would put the earlier block on the later one's
chain and hand it a child. -/
theorem exists_pedigree (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    ∀ (n : ℕ) (t : BlockId), (U.block b).round - (U.block t).round ≤ n →
      t ∈ topsOf U b (U.block t).creator →
      ∃ l, PedigreeTo U b t l ∧ ((U.block t).creator :: l).Nodup := by
  intro n
  induction n with
  | zero =>
      intro t hfuel htop
      obtain ⟨htb, -, -⟩ := mem_topsOf.mp htop
      have hle := round_le_of_mem_history hb htb
      have : t = b := eq_of_mem_history_of_round_eq hb htb (by omega)
      subst this
      exact ⟨[], .base, List.nodup_singleton _⟩
  | succ n ih =>
      intro t hfuel htop
      by_cases hbt : t = b
      · subst hbt
        exact ⟨[], .base, List.nodup_singleton _⟩
      obtain ⟨htb, -, httop⟩ := mem_topsOf.mp htop
      obtain ⟨j, hjb, htref⟩ := exists_referencer hb htb hbt
      have hj_ids : j ∈ U.ids := history_subset_ids hb hjb
      obtain ⟨T, hTtop, hjT⟩ := exists_top_of_mem_history hb hjb rfl
      have hTc : (U.block T).creator = (U.block j).creator := (mem_topsOf.mp hTtop).2.1
      have hTb : T ∈ history U b := (mem_topsOf.mp hTtop).1
      have hT_ids := history_subset_ids hb hTb
      have hround_tj := U.round_of_mem_refs hj_ids htref
      have hround_jT := round_le_of_mem_history hT_ids hjT
      have hround_Tb := round_le_of_mem_history hb hTb
      have hTtop' : T ∈ topsOf U b (U.block T).creator := by
        rw [hTc]; exact hTtop
      obtain ⟨l, hped, hnodup⟩ := ih T (by omega) hTtop'
      have hadopt : AdoptedUnder U b t T := ⟨j, hjb, hjT, hTc.symm, htref⟩
      have hfull : PedigreeTo U b t ((U.block T).creator :: l) := .step htop hadopt hped
      refine ⟨(U.block T).creator :: l, hfull, ?_⟩
      rw [List.nodup_cons]
      refine ⟨?_, hnodup⟩
      intro hmem
      obtain ⟨-, hall⟩ := pedigree_spec hb hfull
      obtain ⟨s', hs'b, hs'c, -, hts', hround⟩ := hall _ hmem
      have hs'_ids := history_subset_ids hb hs'b
      have hne : t ≠ s' := by intro h; rw [h] at hround; omega
      obtain ⟨q, hq, hqc, htq⟩ :=
        exists_child_of_mem_history_of_creator_eq hdos hs'_ids hts' hs'c.symm hne
      have hqb : q ∈ history U b :=
        history_subset_of_reaches hb ((mem_history_iff hb).mp hs'b) hq
      exact httop q hqb (hqc.trans hs'c) htq

/-- Inverting one pedigree step against a cons list. -/
theorem pedigree_cons_inv {b t : BlockId} {W : Validator} {l : List Validator}
    (h : PedigreeTo U b t (W :: l)) :
    ∃ T, (U.block T).creator = W ∧ t ∈ topsOf U b (U.block t).creator ∧
      AdoptedUnder U b t T ∧ PedigreeTo U b T l := by
  cases h with
  | step htop hadopt hrest => exact ⟨_, rfl, htop, hadopt, hrest⟩

/-- **Pedigrees determine.** Two tops of one author with the same pedigree
author-list are equal: each step downward is the unique adopted top of that
author under that adopter (the adoption collapse). -/
theorem pedigree_deterministic (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    ∀ {l : List Validator} {t₁ t₂ : BlockId},
      PedigreeTo U b t₁ l → PedigreeTo U b t₂ l →
      (U.block t₁).creator = (U.block t₂).creator → t₁ = t₂ := by
  intro l
  induction l with
  | nil =>
      intro t₁ t₂ h₁ h₂ _
      cases h₁
      cases h₂
      rfl
  | cons W l ih =>
      intro t₁ t₂ h₁ h₂ hcreator
      obtain ⟨T₁, hW₁, htop₁, hadopt₁, hrest₁⟩ := pedigree_cons_inv h₁
      obtain ⟨T₂, hW₂, htop₂, hadopt₂, hrest₂⟩ := pedigree_cons_inv h₂
      have hTT : T₂ = T₁ := ih hrest₂ hrest₁ (hW₂.trans hW₁.symm)
      subst hTT
      obtain ⟨j₁, hj₁b, hj₁T, hj₁c, ht₁ref⟩ := hadopt₁
      obtain ⟨j₂, hj₂b, hj₂T, hj₂c, ht₂ref⟩ := hadopt₂
      have hT_ids : T₂ ∈ U.ids :=
        history_subset_ids hb (pedigree_spec hb hrest₁).1
      have hXexp : ¬ ExposedIn U T₂ (U.block T₂).creator :=
        not_exposedIn_self_creator hdos hT_ids
      have htop₂' : t₂ ∈ topsOf U b (U.block t₁).creator := by
        rw [hcreator]; exact htop₂
      rcases le_total (U.block j₁).round (U.block j₂).round with hle | hle
      · have hchain : j₁ ∈ history U j₂ :=
          mem_history_of_creator_eq_of_not_exposedIn hT_ids hXexp hj₁T hj₂T
            hj₁c hj₂c hle
        have hj₂_ids : j₂ ∈ U.ids := history_subset_ids hb hj₂b
        have ht₁j₂ : t₁ ∈ history U j₂ :=
          history_subset_of_reaches hj₂_ids ((mem_history_iff hj₂_ids).mp hchain)
            (mem_history_of_mem_refs (history_subset_ids hb hj₁b) ht₁ref)
        exact top_eq_of_mem_namer_history hdos hb htop₁ htop₂' hj₂b ht₂ref ht₁j₂
      · have hchain : j₂ ∈ history U j₁ :=
          mem_history_of_creator_eq_of_not_exposedIn hT_ids hXexp hj₂T hj₁T
            hj₂c hj₁c hle
        have hj₁_ids : j₁ ∈ U.ids := history_subset_ids hb hj₁b
        have ht₂j₁ : t₂ ∈ history U j₁ :=
          history_subset_of_reaches hj₁_ids ((mem_history_iff hj₁_ids).mp hchain)
            (mem_history_of_mem_refs (history_subset_ids hb hj₂b) ht₂ref)
        exact (top_eq_of_mem_namer_history hdos hb htop₂' htop₁ hj₁b ht₁ref
          ht₂j₁).symm

/-- **The general top count.** A top is determined by its own author and its
pedigree's duplicate-free author list, of which there are at most
`(3f+2)^(3f+1)`. -/
theorem card_topsOf_le_pow (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    (X : Validator) :
    (topsOf U b X).card ≤ (3 * F.f + 2) ^ (3 * F.f + 1) := by
  classical
  have hex : ∀ t ∈ topsOf U b X,
      ∃ l, PedigreeTo U b t l ∧ ((U.block t).creator :: l).Nodup := by
    intro t ht
    have htc : (U.block t).creator = X := (mem_topsOf.mp ht).2.1
    exact exists_pedigree hdos hb _ t (le_refl _) (by rw [htc]; exact ht)
  have hinj : (topsOf U b X).card
      ≤ Fintype.card (Fin (3 * F.f + 1) → Option Validator) := by
    rw [← Finset.card_univ]
    refine Finset.card_le_card_of_injOn
      (fun t => (fun k : Fin (3 * F.f + 1) =>
        (if h : ∃ l, PedigreeTo U b t l ∧ ((U.block t).creator :: l).Nodup
          then h.choose else [])[(k : ℕ)]?))
      (fun _ _ => Finset.mem_univ _) ?_
    intro t₁ h₁ t₂ h₂ heq
    rw [Finset.mem_coe] at h₁ h₂
    have hex₁ := hex t₁ h₁
    have hex₂ := hex t₂ h₂
    simp only [dif_pos hex₁, dif_pos hex₂] at heq
    have hlen₁ : hex₁.choose.length ≤ 3 * F.f := by
      have hlc := hex₁.choose_spec.2.length_le_card
      rw [F.card_validators] at hlc
      simp only [List.length_cons] at hlc
      omega
    have hlen₂ : hex₂.choose.length ≤ 3 * F.f := by
      have hlc := hex₂.choose_spec.2.length_le_card
      rw [F.card_validators] at hlc
      simp only [List.length_cons] at hlc
      omega
    have hlists : hex₁.choose = hex₂.choose := by
      apply List.ext_getElem?'
      intro n hn
      have hn' : n < 3 * F.f + 1 := by
        have hmax : max hex₁.choose.length hex₂.choose.length ≤ 3 * F.f :=
          max_le hlen₁ hlen₂
        omega
      have := congrFun heq ⟨n, hn'⟩
      simpa using this
    have hped₂ : PedigreeTo U b t₂ hex₁.choose := by
      rw [hlists]; exact hex₂.choose_spec.1
    have hcreator : (U.block t₁).creator = (U.block t₂).creator :=
      ((mem_topsOf.mp h₁).2.1).trans ((mem_topsOf.mp h₂).2.1).symm
    exact pedigree_deterministic hdos hb hex₁.choose_spec.1 hped₂ hcreator
  calc (topsOf U b X).card
      ≤ Fintype.card (Fin (3 * F.f + 1) → Option Validator) := hinj
    _ = (3 * F.f + 2) ^ (3 * F.f + 1) := by
        rw [Fintype.card_fun, Fintype.card_option, Fintype.card_fin, F.card_validators]

/-- An author's per-round contribution never exceeds its chain count: each
round-`n` block sits on the chain of a distinct top. -/
theorem card_historyBlocksOf_le_card_topsOf (hdos : DoSValid U) {b : BlockId}
    (hb : b ∈ U.ids) (X : Validator) (n : ℕ) :
    (historyBlocksOf U b X n).card ≤ (topsOf U b X).card := by
  classical
  refine Finset.card_le_card_of_injOn
    (fun i => if h : ∃ t ∈ topsOf U b X, i ∈ history U t then h.choose else i) ?_ ?_
  · intro i hi
    simp only [Finset.mem_coe] at hi
    obtain ⟨hih, hic, -⟩ := mem_historyBlocksOf.mp hi
    have hex := exists_top_of_mem_history hb hih hic
    refine Finset.mem_coe.mpr ?_
    change (if h : ∃ t ∈ topsOf U b X, i ∈ history U t then h.choose else i) ∈ topsOf U b X
    rw [dif_pos hex]
    exact hex.choose_spec.1
  · intro i₁ h₁ i₂ h₂ heq
    simp only [Finset.mem_coe] at h₁ h₂
    obtain ⟨hi₁h, hi₁c, hi₁r⟩ := mem_historyBlocksOf.mp h₁
    obtain ⟨hi₂h, hi₂c, hi₂r⟩ := mem_historyBlocksOf.mp h₂
    have hex₁ := exists_top_of_mem_history hb hi₁h hi₁c
    have hex₂ := exists_top_of_mem_history hb hi₂h hi₂c
    simp only [dif_pos hex₁, dif_pos hex₂] at heq
    obtain ⟨htmem, hi₁t⟩ := hex₁.choose_spec
    have hi₂t : i₂ ∈ history U hex₁.choose := heq ▸ hex₂.choose_spec.2
    obtain ⟨htb, htc, -⟩ := mem_topsOf.mp htmem
    have ht_ids : hex₁.choose ∈ U.ids := history_subset_ids hb htb
    exact eq_of_not_exposedIn (not_exposedIn_self_creator hdos ht_ids) hi₁t hi₂t
      (hi₁c.trans htc.symm) (hi₂c.trans htc.symm) (by rw [hi₁r, hi₂r])

/-- **C1′, in full.** Under `DoSValid` with self-parents, an author
contributes at most `c(f) = (3f+2)^(3f+1)` blocks per round to any history —
a constant in `r`, for every `f`. Compounding is impossible. -/
theorem card_historyBlocksOf_le (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids)
    (X : Validator) (n : ℕ) :
    (historyBlocksOf U b X n).card ≤ (3 * F.f + 2) ^ (3 * F.f + 1) :=
  le_trans (card_historyBlocksOf_le_card_topsOf hdos hb X n)
    (card_topsOf_le_pow hdos hb X)

/-- **The general bound.** Every DoS-valid history is linear in its round,
at every fault budget:

> `|H(b)| ≤ (3f+1) · (3f+2)^(3f+1) · (r+1)`

The constant is far from tight — `f ≤ 1` has `7(r+1)` by the adoption
theorem — but it is constant in `r`, which is C1′'s whole demand. -/
theorem card_history_le (hdos : DoSValid U) {b : BlockId} (hb : b ∈ U.ids) :
    (history U b).card
      ≤ (3 * F.f + 1) * (3 * F.f + 2) ^ (3 * F.f + 1) * ((U.block b).round + 1) := by
  classical
  calc (history U b).card
      = ∑ W ∈ Finset.univ,
          ((history U b).filter fun i => (U.block i).creator = W).card :=
        Finset.card_eq_sum_card_fiberwise (fun i _ => Finset.mem_univ _)
    _ ≤ ∑ _W ∈ (Finset.univ : Finset Validator),
          (3 * F.f + 2) ^ (3 * F.f + 1) * ((U.block b).round + 1) := by
        refine Finset.sum_le_sum ?_
        intro W _
        calc ((history U b).filter fun i => (U.block i).creator = W).card
            ≤ (topsOf U b W).card * ((U.block b).round + 1) :=
              card_filter_creator_le_card_topsOf hdos hb W
          _ ≤ (3 * F.f + 2) ^ (3 * F.f + 1) * ((U.block b).round + 1) :=
              Nat.mul_le_mul_right _ (card_topsOf_le_pow hdos hb W)
    _ = (3 * F.f + 1) * ((3 * F.f + 2) ^ (3 * F.f + 1) * ((U.block b).round + 1)) := by
        rw [Finset.sum_const_nat (fun _ _ => rfl), Finset.card_univ, F.card_validators]
    _ = (3 * F.f + 1) * (3 * F.f + 2) ^ (3 * F.f + 1) * ((U.block b).round + 1) := by
        rw [Nat.mul_assoc]

end LeanDag
