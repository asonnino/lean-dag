import LeanDag.FinWhale.Consistency

/-!
# FinWhale — commit sequences and the delivered order

Lemma 12 settles one slot at a time. The properties Byzantine atomic
broadcast asks for are about the whole sequence, and this file carries
the argument the rest of the way.

`commitSeq` is a validator's committed leader sequence: the committed
blocks of its decided slots, in slot order. **Lemma 13** says two such
sequences are always prefix-comparable, which is Lemma 12 plus the fact
that a validator commits up to its first undecided slot and no further.

`linearise` is the delivery order: walk the leader sequence, and after
each leader append the blocks of its causal history that have not been
delivered yet. Two facts about it finish the safety half of the paper.
**Theorem 14** is that the delivered sequences are prefix-comparable,
because `linearise` only ever appends — a longer leader sequence extends
the delivery order rather than revising it. **Theorem 15** is that no
block is delivered twice, because each round appends only what the
accumulator does not already hold.

Both are proved for a `linearise` that takes the causal histories as a
parameter, so they say what the paper's proofs say: the order is a
function of the committed leader sequence and nothing else.
-/

namespace LeanDag

namespace FinWhale

variable {BlockId : Type*} [DecidableEq BlockId]

/-- **The committed leader sequence** of the first `k` slots. -/
def commitSeq (dec : ℕ → Verdict BlockId) : ℕ → List BlockId
  | 0 => []
  | k + 1 => commitSeq dec k ++ (match dec k with
      | Verdict.commit b => [b]
      | Verdict.skip => []
      | Verdict.undecided => [])

omit [DecidableEq BlockId] in
/-- Verdicts agreeing below `k` give the same sequence. -/
theorem commitSeq_congr {dec dec' : ℕ → Verdict BlockId} :
    ∀ k, (∀ s, s < k → dec s = dec' s) → commitSeq dec k = commitSeq dec' k := by
  intro k
  induction k with
  | zero => intro _; rfl
  | succ k ih =>
    intro h
    simp only [commitSeq, ih fun s hs => h s (by omega), h k (by omega)]

omit [DecidableEq BlockId] in
/-- Scanning further extends the sequence. -/
theorem commitSeq_prefix (dec : ℕ → Verdict BlockId) {k k' : ℕ} (h : k ≤ k') :
    commitSeq dec k <+: commitSeq dec k' := by
  induction k' with
  | zero =>
    have hk : k = 0 := by omega
    subst hk; exact List.prefix_rfl
  | succ k' ih =>
    rcases Nat.lt_or_ge k (k' + 1) with hlt | hge
    · exact (ih (by omega)).trans (by simp only [commitSeq]; exact List.prefix_append _ _)
    · have hk : k = k' + 1 := by omega
      subst hk; exact List.prefix_rfl

omit [DecidableEq BlockId] in
/-- **Lemma 13.** Two validators' committed leader sequences are
prefix-comparable. Each validator commits up to its first undecided slot,
Lemma 12 makes the two agree wherever both have decided, and the shorter
decided prefix is a prefix of the longer. -/
theorem lemma13 {dec dec' : ℕ → Verdict BlockId} {k k' : ℕ}
    (hagree : ∀ s, dec s ≠ Verdict.undecided → dec' s ≠ Verdict.undecided → dec s = dec' s)
    (hk : ∀ s, s < k → dec s ≠ Verdict.undecided)
    (hk' : ∀ s, s < k' → dec' s ≠ Verdict.undecided) :
    commitSeq dec k <+: commitSeq dec' k' ∨ commitSeq dec' k' <+: commitSeq dec k := by
  rcases le_total k k' with hle | hle
  · refine Or.inl ?_
    rw [commitSeq_congr k fun s hs => hagree s (hk s hs) (hk' s (by omega))]
    exact commitSeq_prefix dec' hle
  · refine Or.inr ?_
    rw [← commitSeq_congr k' fun s hs => hagree s (hk s (by omega)) (hk' s hs)]
    exact commitSeq_prefix dec hle

/-- **The delivery order.** Each committed leader contributes the blocks
of its causal history that no earlier leader delivered. -/
def linearise (hist : BlockId → List BlockId) (ls : List BlockId) : List BlockId :=
  ls.foldl (fun acc l => acc ++ (hist l).filter (fun b => b ∉ acc)) []

/-- The accumulator only grows at its end. -/
theorem linearise_foldl_append (hist : BlockId → List BlockId) :
    ∀ (ls : List BlockId) (acc : List BlockId),
      ∃ t, ls.foldl (fun acc l => acc ++ (hist l).filter (fun b => b ∉ acc)) acc = acc ++ t := by
  intro ls
  induction ls with
  | nil => intro acc; exact ⟨[], by simp⟩
  | cons l ls ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (acc ++ (hist l).filter (fun b => b ∉ acc))
    exact ⟨(hist l).filter (fun b => b ∉ acc) ++ t,
      by simp only [List.foldl_cons, ht, List.append_assoc]⟩

/-- **Theorem 14 (Total Order).** A longer committed leader sequence
delivers an extension of what a shorter one delivers, so two validators
never disagree on the order of what both have delivered. With Lemma 13
this is the total order property: the two leader sequences are
prefix-comparable, hence so are the two delivery orders. -/
theorem theorem14 (hist : BlockId → List BlockId) {ls ls' : List BlockId}
    (h : ls <+: ls') : linearise hist ls <+: linearise hist ls' := by
  obtain ⟨t, rfl⟩ := h
  obtain ⟨u, hu⟩ := linearise_foldl_append hist t (linearise hist ls)
  refine ⟨u, ?_⟩
  simpa [linearise, List.foldl_append] using hu.symm

/-- **Theorem 15 (Integrity).** No block is delivered twice: each leader
appends only what the accumulator does not already hold, and a causal
history lists each block once. -/
theorem theorem15 (hist : BlockId → List BlockId) (hnd : ∀ l, (hist l).Nodup)
    (ls : List BlockId) : (linearise hist ls).Nodup := by
  have key : ∀ (ls : List BlockId) (acc : List BlockId), acc.Nodup →
      (ls.foldl (fun acc l => acc ++ (hist l).filter (fun b => b ∉ acc)) acc).Nodup := by
    intro ls
    induction ls with
    | nil => intro acc h; exact h
    | cons l ls ih =>
      intro acc h
      refine ih _ ?_
      rw [List.nodup_append]
      refine ⟨h, (hnd l).filter _, ?_⟩
      intro a ha b hb hab
      have hnot := List.of_mem_filter hb
      simp only [decide_eq_true_eq] at hnot
      exact hnot (hab ▸ ha)
  exact key ls [] List.nodup_nil

section EndToEnd

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {Payload : Type*} {D : Dag Validator BlockId Payload}

/-- **Safety, end to end.** Two validators running the reverse pass on
sub-DAGs of one valid DAG deliver prefix-comparable sequences.

Everything the statement assumes is either a fact about the DAG or a
faithfulness condition on the model: `hwf`/`hwf'` say each validator
follows the decision rule, `hdc`/`hdc'`/`hds`/`hds'` say a view's direct
verdict is a direct verdict of the universe, `hch` says the tie-break
picks among the anchor's candidates, `hslot`/`hslot'` say a committed
verdict names a block of its own slot, `hbound` says both validators have
finitely many decided slots, and `hk`/`hk'` say each commit sequence stops
at its first undecided slot. -/
theorem safety {dc dc' : ℕ → BlockId → Prop} {ds ds' : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec dec' : ℕ → Verdict BlockId}
    (hwf : WellFormed dc ds choose dec) (hwf' : WellFormed dc' ds' choose dec')
    (hch : ChooseSound D choose)
    (hdc : ∀ r l, dc r l → l ∈ slotBlocks D r ∧ DirectCommit D l)
    (hdc' : ∀ r l, dc' r l → l ∈ slotBlocks D r ∧ DirectCommit D l)
    (hds : ∀ r, ds r → DirectSkip D r) (hds' : ∀ r, ds' r → DirectSkip D r)
    (hslot : ∀ r A, dec r = Verdict.commit A → A ∈ slotBlocks D r)
    (hslot' : ∀ r A, dec' r = Verdict.commit A → A ∈ slotBlocks D r)
    {N : ℕ} (hbound : ∀ s, N ≤ s → dec s = Verdict.undecided ∧ dec' s = Verdict.undecided)
    {k k' : ℕ} (hk : ∀ s, s < k → dec s ≠ Verdict.undecided)
    (hk' : ∀ s, s < k' → dec' s ≠ Verdict.undecided)
    (hist : BlockId → List BlockId) :
    linearise hist (commitSeq dec k) <+: linearise hist (commitSeq dec' k') ∨
      linearise hist (commitSeq dec' k') <+: linearise hist (commitSeq dec k) := by
  -- a committed verdict names a block of its slot, which is a block of
  -- the DAG at that round; above `r + 2` that is what `Above` asks for
  have habove : ∀ (dq : ℕ → Verdict BlockId),
      (∀ r A, dq r = Verdict.commit A → A ∈ slotBlocks D r) →
      ∀ r a A, r + 2 < a → dq a = Verdict.commit A → A ∈ D.ids ∧ r + 3 ≤ (D.block A).round := by
    intro dq hq r a A hra hcom
    have := hq a A hcom
    simp only [slotBlocks, blocksAt, Finset.mem_filter] at this
    exact ⟨this.1.1, by omega⟩
  rcases lemma13
      (lemma12 hwf hwf' (exclusions_of_dag hch hdc hdc' hds hds')
        (habove dec hslot) (habove dec' hslot') hbound) hk hk' with h | h
  · exact Or.inl (theorem14 hist h)
  · exact Or.inr (theorem14 hist h)

end EndToEnd

end FinWhale

end LeanDag
