import LeanDag.BlackMarlin.Model.Order
import Mathlib.Data.Finset.Sort
import LeanDag.BlackMarlin.Helpers.Ledger

/-!
# Black Marlin — the sequence layer

Generated proof layer; not part of the audit surface. The delivered
sequence agrees between records that agree, grows by extension, carries
each author-and-round at most once, and delivers a correct author's block
itself rather than a twin of it.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {f f₁ f₂ : Flush U} {τ : TopoSort U} {n m ρ : ℕ}

/-! ## The flushed sequence -/

/-- Records that agree below a round flush the same segments there. -/
theorem segment_congr (h : ∀ σ, σ < n → f₁.block σ = f₂.block σ) (hρ : ρ < n) :
    segment U f₁ τ ρ = segment U f₂ τ ρ := by
  have hbelow : deliveredBelow U f₁ ρ = deliveredBelow U f₂ ρ := by
    unfold deliveredBelow
    refine Finset.biUnion_congr rfl (fun σ hσ => ?_)
    rw [h σ (by simp only [Finset.mem_range] at hσ; omega)]
  unfold segment
  rw [h ρ hρ, hbelow]

/-- **Records that agree below a round flush the same sequence.** -/
theorem ledgerSeq_agree (h : ∀ σ, σ < n → f₁.block σ = f₂.block σ) :
    ledgerSeq U f₁ τ n = ledgerSeq U f₂ τ n := by
  unfold ledgerSeq
  refine List.flatMap_congr (fun ρ hρ => ?_)
  exact segment_congr h (by simpa using hρ)

/-- **And the sequence only extends.** -/
theorem ledgerSeq_prefix (h : n ≤ m) :
    ledgerSeq U f τ n <+: ledgerSeq U f τ m := by
  have step : ∀ k, ledgerSeq U f τ n <+: ledgerSeq U f τ (n + k) := by
    intro k
    induction k with
    | zero => simpa using List.prefix_refl (ledgerSeq U f τ n)
    | succ k ih =>
        refine List.IsPrefix.trans ih ?_
        rw [show n + (k + 1) = (n + k) + 1 by omega]
        unfold ledgerSeq
        rw [List.range_succ, List.flatMap_append]
        exact List.prefix_append _ _
  have := step (m - n)
  rwa [show n + (m - n) = m by omega] at this

/-! ## The filter -/

omit Rot [DecidableEq BlockId] in
theorem filterFirstFrom_append : ∀ (l₁ l₂ : List BlockId) (seen : Finset (Validator × ℕ)),
    filterFirstFrom U (l₁ ++ l₂) seen =
      ((filterFirstFrom U l₁ seen).1 ++
        (filterFirstFrom U l₂ (filterFirstFrom U l₁ seen).2).1,
       (filterFirstFrom U l₂ (filterFirstFrom U l₁ seen).2).2) := by
  intro l₁
  induction l₁ with
  | nil => intro l₂ seen; simp [filterFirstFrom]
  | cons b bs ih =>
      intro l₂ seen
      by_cases hb : key U b ∈ seen
      · simp only [List.cons_append, filterFirstFrom, if_pos hb]
        exact ih l₂ seen
      · simp only [List.cons_append, filterFirstFrom, if_neg hb]
        rw [ih l₂ (insert (key U b) seen)]

omit Rot [DecidableEq BlockId] in
/-- Emitted blocks are blocks of the flushed sequence. -/
theorem filterFirstFrom_subset : ∀ (l : List BlockId) (seen : Finset (Validator × ℕ)),
    ∀ b ∈ (filterFirstFrom U l seen).1, b ∈ l := by
  intro l
  induction l with
  | nil => intro seen b hb; simpa [filterFirstFrom] using hb
  | cons c cs ih =>
      intro seen b hb
      by_cases hc : key U c ∈ seen
      · rw [filterFirstFrom, if_pos hc] at hb
        exact List.mem_cons_of_mem c (ih seen b hb)
      · rw [filterFirstFrom, if_neg hc] at hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem c (ih _ b hb')

omit Rot [DecidableEq BlockId] in
/-- An emitted block's key was not already delivered. -/
theorem filterFirstFrom_key_notMem : ∀ (l : List BlockId) (seen : Finset (Validator × ℕ)),
    ∀ b ∈ (filterFirstFrom U l seen).1, key U b ∉ seen := by
  intro l
  induction l with
  | nil => intro seen b hb; simpa [filterFirstFrom] using hb
  | cons c cs ih =>
      intro seen b hb
      by_cases hc : key U c ∈ seen
      · rw [filterFirstFrom, if_pos hc] at hb
        exact ih seen b hb
      · rw [filterFirstFrom, if_neg hc] at hb
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact hc
        · exact fun hmem => ih _ b hb' (Finset.mem_insert_of_mem hmem)

omit Rot [DecidableEq BlockId] in
/-- **Integrity.** No author-and-round is emitted twice. -/
theorem filterFirstFrom_pairwise : ∀ (l : List BlockId) (seen : Finset (Validator × ℕ)),
    (filterFirstFrom U l seen).1.Pairwise (fun a b => key U a ≠ key U b) := by
  intro l
  induction l with
  | nil => intro seen; simp [filterFirstFrom]
  | cons c cs ih =>
      intro seen
      by_cases hc : key U c ∈ seen
      · rw [filterFirstFrom, if_pos hc]; exact ih seen
      · rw [filterFirstFrom, if_neg hc]
        refine List.pairwise_cons.mpr ⟨fun b hb => ?_, ih _⟩
        intro hkey
        exact filterFirstFrom_key_notMem cs _ b hb
          (hkey ▸ Finset.mem_insert_self (key U c) seen)

omit Rot [DecidableEq BlockId] in
/-- **Every key of the flushed sequence is emitted**, by that block or by
one of the same author and round. -/
theorem filterFirstFrom_key_mem : ∀ (l : List BlockId) (seen : Finset (Validator × ℕ)),
    ∀ b ∈ l, key U b ∈ seen ∨ ∃ c ∈ (filterFirstFrom U l seen).1, key U c = key U b := by
  intro l
  induction l with
  | nil => intro seen b hb; simp at hb
  | cons c cs ih =>
      intro seen b hb
      by_cases hc : key U c ∈ seen
      · rw [filterFirstFrom, if_pos hc]
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inl hc
        · exact ih seen b hb'
      · rw [filterFirstFrom, if_neg hc]
        rcases List.mem_cons.mp hb with rfl | hb'
        · exact Or.inr ⟨b, List.mem_cons_self, rfl⟩
        · rcases ih (insert (key U c) seen) b hb' with hin | ⟨d, hd, hdk⟩
          · rcases Finset.mem_insert.mp hin with heq | hin'
            · exact Or.inr ⟨c, List.mem_cons_self, heq.symm⟩
            · exact Or.inl hin'
          · exact Or.inr ⟨d, List.mem_cons_of_mem c hd, hdk⟩

/-! ## What a validator outputs -/

theorem notMem_deliveredBelow {L : BlockId} (hL : f.block ρ = some L) :
    L ∉ deliveredBelow U f ρ := by
  intro hmem
  obtain ⟨σ, hσ, hin⟩ := Finset.mem_biUnion.mp hmem
  rw [Finset.mem_range] at hσ
  cases hM : f.block σ with
  | none => rw [hM] at hin; simp at hin
  | some M =>
      rw [hM] at hin
      have hMr := (f.isAnchor σ M hM).2.1
      have hLr := (f.isAnchor ρ L hL).2.1
      have := round_le_of_mem_history (f.isAnchor σ M hM).1 hin
      omega

/-- **The anchor is last in its segment.** L26 flushes `past(B) \ 𝒟` and
L30 then emits `B`; a topological sort of `history U B \ 𝒟` puts `B`
last of its own accord, so the two are one list. -/
theorem idxOf_le_idxOf_anchor {L b : BlockId} (hL : f.block ρ = some L)
    (hb : b ∈ segment U f τ ρ) :
    (segment U f τ ρ).idxOf b ≤ (segment U f τ ρ).idxOf L := by
  have hLids : L ∈ U.ids := (f.isAnchor ρ L hL).1
  unfold segment at hb ⊢
  rw [hL] at hb ⊢
  have hbmem := (τ.mem _ b).mp hb
  have hLmem : L ∈ history U L \ deliveredBelow U f ρ :=
    Finset.mem_sdiff.mpr ⟨mem_history_self, notMem_deliveredBelow hL⟩
  exact τ.topo _ b L hbmem hLmem
    ((mem_history_iff hLids).mp (Finset.mem_sdiff.mp hbmem).1)

/-- Everything flushed is a block of the universe. -/
theorem mem_ledgerSeq_mem_ids {b : BlockId} (hb : b ∈ ledgerSeq U f τ n) : b ∈ U.ids := by
  rw [ledgerSeq, List.mem_flatMap] at hb
  obtain ⟨ρ, -, hbs⟩ := hb
  unfold segment at hbs
  cases hL : f.block ρ with
  | none => rw [hL] at hbs; simp at hbs
  | some L =>
      rw [hL] at hbs
      exact history_subset_ids (f.isAnchor ρ L hL).1
        (Finset.mem_sdiff.mp ((τ.mem _ b).mp hbs)).1

/-- **Records that agree below a round output the same list.** Definition
1's Total order follows: neither can deliver two blocks in opposite
orders, because there is one list. -/
theorem deliverSeq_agree (h : ∀ σ, σ < n → f₁.block σ = f₂.block σ) :
    deliverSeq U f₁ τ n = deliverSeq U f₂ τ n := by
  unfold deliverSeq
  rw [ledgerSeq_agree h]

/-- **And what is output is never retracted**: the list through a round
is a prefix of the list through any later one. -/
theorem deliverSeq_prefix (h : n ≤ m) :
    deliverSeq U f τ n <+: deliverSeq U f τ m := by
  obtain ⟨l, hl⟩ := ledgerSeq_prefix (f := f) (τ := τ) h
  unfold deliverSeq
  rw [← hl, filterFirstFrom_append]
  exact List.prefix_append _ _

/-- **Integrity.** No author-and-round is output twice. -/
theorem deliverSeq_pairwise :
    (deliverSeq U f τ n).Pairwise (fun a b => key U a ≠ key U b) :=
  filterFirstFrom_pairwise _ _

/-- Everything output was flushed, hence is a block of the universe. -/
theorem deliverSeq_mem_ids {b : BlockId} (hb : b ∈ deliverSeq U f τ n) : b ∈ U.ids :=
  mem_ledgerSeq_mem_ids (filterFirstFrom_subset _ _ b hb)

/-- **Every author-and-round flushed is output**, by that block or by one
of the same author and round. -/
theorem deliverSeq_key_mem {b : BlockId} (hb : b ∈ ledgerSeq U f τ n) :
    ∃ c ∈ deliverSeq U f τ n, key U c = key U b := by
  rcases filterFirstFrom_key_mem (U := U) (ledgerSeq U f τ n) ∅ b hb with hin | h
  · simp at hin
  · exact h

/-- **And for a correct author, by the block itself.** A correct
validator has one block per round, so the filter of L27 has no twin to
prefer. -/
theorem deliverSeq_of_correct {b : BlockId} (hb : b ∈ ledgerSeq U f τ n)
    (hc : (U.block b).creator ∈ (Correct : Finset Validator)) :
    b ∈ deliverSeq U f τ n := by
  obtain ⟨c, hcmem, hkey⟩ := deliverSeq_key_mem hb
  have hcb : c = b :=
    U.eq_of_creator_eq (deliverSeq_mem_ids hcmem) (mem_ledgerSeq_mem_ids hb) hc
      (congrArg Prod.fst hkey) rfl (congrArg Prod.snd hkey)
  exact hcb ▸ hcmem

/-- **What a flushed anchor's cone holds is flushed**, at that round or
at a lower one where it was first reached. -/
theorem mem_ledgerSeq_of_mem_history :
    ∀ (ρ : ℕ) (L b : BlockId), f.block ρ = some L → b ∈ history U L → ρ < n →
      b ∈ ledgerSeq U f τ n := by
  intro ρ
  induction ρ using Nat.strong_induction_on with
  | _ ρ ih =>
      intro L b hL hb hρn
      by_cases hd : b ∈ deliveredBelow U f ρ
      · obtain ⟨σ, hσ, hin⟩ := Finset.mem_biUnion.mp hd
        rw [Finset.mem_range] at hσ
        cases hM : f.block σ with
        | none => rw [hM] at hin; simp at hin
        | some M =>
            rw [hM] at hin
            exact ih σ hσ M b hM hin (by omega)
      · rw [ledgerSeq]
        refine List.mem_flatMap.mpr ⟨ρ, by simpa using hρn, ?_⟩
        unfold segment
        rw [hL]
        exact (τ.mem _ b).mpr (Finset.mem_sdiff.mpr ⟨hb, hd⟩)

/-! ## A sort exists

`TopoSort` would make every result above vacuous if nothing satisfied
it. Where identifiers run downward along references — as they do
whenever ids are assigned in production order — sorting by identifier is
one. -/

omit F Rot [DecidableEq BlockId] in
theorem idxOf_le_of_pairwise {α : Type*} [LinearOrder α] :
    ∀ {l : List α}, l.Pairwise (· ≤ ·) → l.Nodup → ∀ {a b : α}, a ∈ l → b ∈ l →
      a ≤ b → l.idxOf a ≤ l.idxOf b := by
  intro l
  induction l with
  | nil => intro _ _ a b ha; simp at ha
  | cons c cs ih =>
      intro hs hn a b ha hb hab
      by_cases hac : a = c
      · subst hac; simp
      · have hacs : a ∈ cs := (List.mem_cons.mp ha).resolve_left hac
        have hbc : b ≠ c := by
          intro hbe
          subst hbe
          exact hac (le_antisymm hab (List.rel_of_pairwise_cons hs hacs))
        have hbcs : b ∈ cs := (List.mem_cons.mp hb).resolve_left hbc
        rw [List.idxOf_cons_ne cs (Ne.symm hac), List.idxOf_cons_ne cs (Ne.symm hbc)]
        exact Nat.succ_le_succ
          (ih (List.Pairwise.of_cons hs) (List.Nodup.of_cons hn) hacs hbcs hab)

section IdOrder

variable {Id : Type*} [LinearOrder Id] {W : BlockUniverse Validator Id Payload}

/-- **Sorting by identifier is a topological sort**, when a block's
references carry smaller identifiers — which is how ids are assigned in
production order. This is what keeps `TopoSort` from being vacuous. -/
def TopoSort.ofIdOrder (W : BlockUniverse Validator Id Payload)
    (h : ∀ b : Id, ∀ j ∈ (W.block b).refs, j < b) : TopoSort W where
  sort s := s.sort (· ≤ ·)
  mem _ _ := Finset.mem_sort _
  nodup _ := Finset.sort_nodup _ _
  topo s a b ha hb hr := by
    refine idxOf_le_of_pairwise (Finset.pairwise_sort s _) (Finset.sort_nodup _ _)
      ((Finset.mem_sort _).mpr ha) ((Finset.mem_sort _).mpr hb) ?_
    clear ha hb
    induction hr with
    | refl => exact le_refl _
    | tail _ hstep ihr => exact le_trans (le_of_lt (h _ _ hstep)) ihr

/-- **The same sort, in a form the kernel evaluates.** `Finset.sort`
rests on a merge sort the kernel does not reduce, so a witness filters
`List.finRange` instead: the same order, structurally computed, which is
what lets a concrete model settle the delivered sequence by `decide`. -/
def TopoSort.ofFinOrder {n : ℕ} (W : BlockUniverse Validator (Fin n) Payload)
    (h : ∀ b : Fin n, ∀ j ∈ (W.block b).refs, j < b) : TopoSort W where
  sort s := (List.finRange n).filter (fun x => decide (x ∈ s))
  mem s b := by simp
  nodup s := (List.nodup_finRange n).filter _
  topo s a b ha hb hr := by
    refine idxOf_le_of_pairwise
      ((List.pairwise_le_finRange n).filter _) ((List.nodup_finRange n).filter _)
      (by simp [ha]) (by simp [hb]) ?_
    clear ha hb
    induction hr with
    | refl => exact le_refl _
    | tail _ hstep ihr => exact le_trans (le_of_lt (h _ _ hstep)) ihr

end IdOrder

end BlackMarlin

end LeanDag
