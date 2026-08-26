import LeanDag.FinWhale.Anchor

/-!
# FinWhale — the anchor recursion, and Lemma 12

A validator's decisions are a verdict per leader slot. The reverse pass
fixes them: a slot decided by the direct rules takes that verdict, and
otherwise the validator finds its **anchor** — the first slot above
`r + 2` that is not skipped — and reads the slot off the anchor's causal
history, marking the slot undecided if the anchor is.

`WellFormed` is that, as a predicate on a verdict assignment rather than
a procedure. `Anchor` is the first-non-skipped-slot condition.

Two facts close Lemma 12.

**The anchor is a function of the verdicts above.** `anchor_unique` says
two validators agreeing on every slot above `r` pick the same anchor,
because the anchor is determined by which of those slots are skipped.

**The tie-break is a function of the anchor.** `IndirectCommit` mentions
no view, and `choose` — the paper's "deterministic rule" for selecting
among conflicting candidates — takes only the anchor and the round. So
once the anchors agree, the indirect verdicts agree.

That is the whole of the difference from Black Marlin, where the same
kind of deterministic choice was unsafe. There the two validators
descended from *different* anchors and the choice saw different data;
here the anchor is pinned by agreement above, and the data is the
anchor's history, which is the same block's history for both.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- A validator's verdict for a leader slot. -/
inductive Verdict (BlockId : Type*) where
  /-- The slot is decided, and this block of it is committed. -/
  | commit (b : BlockId)
  /-- The slot is decided, and no block of it is committed. -/
  | skip
  /-- The slot is not yet decided. -/
  | undecided
  deriving DecidableEq

/-- **The anchor of `r`**: the first slot above `r + 2` that is not
skipped. -/
def Anchor (dec : ℕ → Verdict BlockId) (r a : ℕ) : Prop :=
  r + 2 < a ∧ dec a ≠ Verdict.skip ∧ ∀ a', r + 2 < a' → a' < a → dec a' = Verdict.skip

/-- **The reverse pass, as a condition on the verdicts.** A slot with a
direct commit takes it; a slot with a direct skip is skipped; otherwise
the anchor decides, and an undecided anchor leaves the slot undecided.
`choose` is the paper's deterministic rule for picking among candidates,
and takes only the anchor and the round. -/
structure WellFormed (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) (dec : ℕ → Verdict BlockId) : Prop where
  /-- A direct commit is taken. -/
  direct_commit : ∀ r, ∀ l ∈ slotBlocks D r, DirectCommit D l → dec r = Verdict.commit l
  /-- A direct skip is taken. -/
  direct_skip : ∀ r, DirectSkip D r → dec r = Verdict.skip
  /-- An undecided anchor leaves the slot undecided. -/
  indirect_undecided : ∀ r a, Anchor dec r a → dec a = Verdict.undecided →
    dec r = Verdict.undecided
  /-- A committed anchor decides the slot, by the deterministic rule if it
  finds a candidate and by a skip otherwise. -/
  indirect_commit : ∀ r a A, Anchor dec r a → dec a = Verdict.commit A →
    dec r = (match choose A r with
      | some b => Verdict.commit b
      | none => Verdict.skip)
  /-- The deterministic rule only ever names a block the indirect
  condition admits. -/
  choose_sound : ∀ A r b, choose A r = some b → IndirectCommit D A r b

/-- **The anchor is fixed by the verdicts above the slot.** Two
assignments agreeing above `r` have the same anchor for `r`. -/
theorem anchor_unique {dec dec' : ℕ → Verdict BlockId} {r a a' : ℕ}
    (hagree : ∀ s, r < s → dec s = dec' s)
    (h : Anchor dec r a) (h' : Anchor dec' r a') : a = a' := by
  obtain ⟨hra, hna, hmin⟩ := h
  obtain ⟨hra', hna', hmin'⟩ := h'
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · exact absurd ((hagree a (by omega)) ▸ hna) (by rw [hmin' a hra hlt]; simp)
  · exact heq
  · exact absurd ((hagree a' (by omega)).symm ▸ hna') (by rw [hmin a' hra' hgt]; simp)

/-- **Lemma 12.** Two validators that agree on every slot above `r` agree
at `r`, whenever both have decided it.

Every route is closed. If either has a direct commit, `lemma12_direct`
and the anchor exclusions settle it; if either has a direct skip, the
same; otherwise both decided from their anchors, which `anchor_unique`
makes one slot, whose verdict they agree on, so both apply `choose` to
the same anchor and round. -/
theorem lemma12 {choose : BlockId → ℕ → Option BlockId}
    {dec dec' : ℕ → Verdict BlockId} {r a a' : ℕ}
    (hwf : WellFormed D choose dec) (hwf' : WellFormed D choose dec')
    (hagree : ∀ s, r < s → dec s = dec' s)
    (ha : Anchor dec r a) (ha' : Anchor dec' r a')
    (hA : ∃ A, dec a = Verdict.commit A) :
    dec r = dec' r := by
  obtain ⟨A, hAcom⟩ := hA
  have heq : a = a' := anchor_unique hagree ha ha'
  subst heq
  have hra : r + 2 < a := ha.1
  have hA' : dec' a = Verdict.commit A := (hagree a (by omega)) ▸ hAcom
  rw [hwf.indirect_commit r a A ha hAcom, hwf'.indirect_commit r a A ha' hA']

/-- **The conflicting pattern is unreachable where anyone could decide
directly.** The paper's remark, in the two halves it needs: a direct
commit of `b` bars an indirect commit of a conflicting block, and a
direct skip bars an indirect commit outright. So `choose` is only ever
consulted where no validator has a direct verdict, and then all
validators consult it on the same anchor. -/
theorem choose_only_where_no_direct {choose : BlockId → ℕ → Option BlockId}
    {dec : ℕ → Verdict BlockId} (hwf : WellFormed D choose dec)
    {A : BlockId} {r : ℕ} {b b' : BlockId}
    (hb : b ∈ D.ids) (hb' : b' ∈ D.ids) (hbslot : b ∈ slotBlocks D r)
    (hlead : (D.block b).creator = D.leader r)
    (hconf : Conflicting D b b') (hfast : FastCommit D b) :
    choose A r ≠ some b' := fun hch =>
  no_indirectCommit_of_fastCommit hb hb' hbslot hlead hconf hfast
    (hwf.choose_sound A r b' hch)

end FinWhale

end LeanDag
