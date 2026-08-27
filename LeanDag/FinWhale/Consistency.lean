import LeanDag.FinWhale.Anchor
import LeanDag.FinWhale.Model.Verdict

/-!
# FinWhale — the anchor recursion, and Lemma 12

Two facts close Lemma 12 over the reverse pass of `Model/Verdict.lean`.

**The anchor is a function of the verdicts above.** `anchor_unique` says
two validators agreeing on every slot above `r` pick the same anchor,
because the anchor is determined by which of those slots are skipped.

**The tie-break is a function of the anchor.** `IndirectCommit` mentions
no view, and `choose` takes only the anchor and the round. So once the
anchors agree, the indirect verdicts agree.

That is the whole of the difference from Black Marlin, where the same
kind of deterministic choice was unsafe. There the two validators
descended from *different* anchors and the choice saw different data;
here the anchor is pinned by agreement above, and the data is the
anchor's history, which is the same block's history for both.

`exclusions_of_dag` discharges the interface Lemma 12 consumes under the
reading that a view is a sub-DAG; `View.lean` replaces that reading with
views themselves. `chooseSound_least` checks the exhibited tie-break
against `ChooseSound`.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

omit [DecidableEq BlockId] in
/-- **The anchor is fixed by the verdicts above the slot.** Two
assignments that agree wherever both have decided pick the same anchor,
because the anchor is the first slot above `r + 2` that is not skipped,
and a skip is a decision. -/
theorem anchor_unique {dec dec' : ℕ → Verdict BlockId} {r a a' : ℕ}
    (hagree : ∀ s, r + 2 < s → dec s ≠ Verdict.undecided → dec' s ≠ Verdict.undecided →
      dec s = dec' s)
    (hda : dec a ≠ Verdict.undecided) (hda' : dec' a' ≠ Verdict.undecided)
    (h : Anchor dec r a) (h' : Anchor dec' r a') : a = a' := by
  obtain ⟨hra, hna, hmin⟩ := h
  obtain ⟨hra', hna', hmin'⟩ := h'
  rcases lt_trichotomy a a' with hlt | heq | hgt
  · have hsk : dec' a = Verdict.skip := hmin' a hra hlt
    exact absurd (by rw [hagree a hra hda (by rw [hsk]; simp), hsk]) hna
  · exact heq
  · have hsk : dec a' = Verdict.skip := hmin a' hra' hgt
    exact absurd (by rw [← hagree a' hra' (by rw [hsk]; simp) hda', hsk]) hna'

omit [DecidableEq BlockId] in
/-- **Lemma 12, in full.** Two validators never decide a leader slot
differently.

The induction is the paper's maximality argument, made downward-explicit:
both DAGs are finite, so nothing above some `N` is decided, and the proof
runs on the distance from `N`. At each slot either some direct rule fires
— and the exclusions settle it — or both validators decided from an
anchor, and then the anchors coincide. That last step is what the
induction is for: if the anchors differed, the lower of the two is
skipped by one validator and committed by the other, and it lies above
`r`, so the induction hypothesis already forbids it. -/
theorem lemma12
    {dc dc' : ℕ → BlockId → Prop} {ds ds' : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec dec' : ℕ → Verdict BlockId}
    {Above : ℕ → BlockId → Prop}
    (hwf : WellFormed dc ds choose dec) (hwf' : WellFormed dc' ds' choose dec')
    (hex : Exclusions dc dc' ds ds' choose Above)
    (habove : ∀ r a A, r + 2 < a → dec a = Verdict.commit A → Above r A)
    (habove' : ∀ r a A, r + 2 < a → dec' a = Verdict.commit A → Above r A)
    {N : ℕ} (hbound : ∀ s, N ≤ s → dec s = Verdict.undecided ∧ dec' s = Verdict.undecided) :
    ∀ r, dec r ≠ Verdict.undecided → dec' r ≠ Verdict.undecided → dec r = dec' r := by
  suffices h : ∀ d r, N ≤ r + d →
      dec r ≠ Verdict.undecided → dec' r ≠ Verdict.undecided → dec r = dec' r by
    intro r h1 h2
    exact h N r (by omega) h1 h2
  intro d
  induction d with
  | zero =>
    intro r hN h1 _
    exact absurd (hbound r (by omega)).1 h1
  | succ d ih =>
    intro r hN h1 h2
    -- the induction hypothesis, at every slot above `r`
    have IH : ∀ s, r < s → dec s ≠ Verdict.undecided → dec' s ≠ Verdict.undecided →
        dec s = dec' s := fun s hs => ih s (by omega)
    by_cases hdc : ∃ l, dc r l
    · obtain ⟨l, hl⟩ := hdc
      rw [hwf.direct_commit r l hl]
      by_cases hdc' : ∃ l', dc' r l'
      · obtain ⟨l', hl'⟩ := hdc'
        rw [hwf'.direct_commit r l' hl', hex.commit_unique r l l' hl hl']
      · by_cases hds' : ds' r
        · exact absurd hds' (hex.commit_bars_skip r l hl)
        · -- the other validator decided from an anchor, and the direct
          -- commit pins the rule that anchor applies
          obtain ⟨a', ha'⟩ := hwf'.has_anchor r hdc' hds' h2
          rcases hva' : dec' a' with A' | - | -
          · obtain ⟨b, hb⟩ := hex.commit_forces_choose r l A' (habove' r a' A' ha'.1 hva') hl
            rw [hwf'.indirect_commit r a' A' hdc' hds' ha' hva', hb,
              hex.commit_pins_choose r l A' b hl hb]
          · exact absurd hva' ha'.2.1
          · exact absurd (hwf'.indirect_undecided r a' hdc' hds' ha' hva') h2
    · by_cases hds : ds r
      · rw [hwf.direct_skip r hds]
        by_cases hdc' : ∃ l', dc' r l'
        · obtain ⟨l', hl'⟩ := hdc'
          exact absurd hds (hex.commit_bars_skip' r l' hl')
        · by_cases hds' : ds' r
          · rw [hwf'.direct_skip r hds']
          · obtain ⟨a', ha'⟩ := hwf'.has_anchor r hdc' hds' h2
            rcases hva' : dec' a' with A' | - | -
            · rw [hwf'.indirect_commit r a' A' hdc' hds' ha' hva']
              rcases hch : choose A' r with - | b
              · rfl
              · exact absurd hch (hex.skip_bars_choose r A' b hds)
            · exact absurd hva' ha'.2.1
            · exact absurd (hwf'.indirect_undecided r a' hdc' hds' ha' hva') h2
      · by_cases hdc' : ∃ l', dc' r l'
        · obtain ⟨l', hl'⟩ := hdc'
          obtain ⟨a, ha⟩ := hwf.has_anchor r hdc hds h1
          rcases hva : dec a with A | - | -
          · obtain ⟨b, hb⟩ := hex.commit_forces_choose' r l' A (habove r a A ha.1 hva) hl'
            rw [hwf.indirect_commit r a A hdc hds ha hva, hb,
              hex.commit_pins_choose' r l' A b hl' hb, hwf'.direct_commit r l' hl']
          · exact absurd hva ha.2.1
          · exact absurd (hwf.indirect_undecided r a hdc hds ha hva) h1
        · by_cases hds' : ds' r
          · rw [hwf'.direct_skip r hds']
            obtain ⟨a, ha⟩ := hwf.has_anchor r hdc hds h1
            rcases hva : dec a with A | - | -
            · rw [hwf.indirect_commit r a A hdc hds ha hva]
              rcases hch : choose A r with - | b
              · rfl
              · exact absurd hch (hex.skip_bars_choose' r A b hds')
            · exact absurd hva ha.2.1
            · exact absurd (hwf.indirect_undecided r a hdc hds ha hva) h1
          · -- both validators decided `r` from an anchor
            obtain ⟨a, ha⟩ := hwf.has_anchor r hdc hds h1
            obtain ⟨a', ha'⟩ := hwf'.has_anchor r hdc' hds' h2
            have hda : dec a ≠ Verdict.undecided := fun hu =>
              h1 (hwf.indirect_undecided r a hdc hds ha hu)
            have hda' : dec' a' ≠ Verdict.undecided := fun hu =>
              h2 (hwf'.indirect_undecided r a' hdc' hds' ha' hu)
            -- the anchors coincide: the lower of two differing anchors is
            -- skipped by one validator and not by the other, and it lies
            -- above `r`, where the induction hypothesis already applies
            have heqa : a = a' :=
              anchor_unique (fun s hs => IH s (by omega)) hda hda' ha ha'
            subst heqa
            rcases hva : dec a with A | - | -
            · have hsame : dec' a = Verdict.commit A := by
                rw [← IH a (by have := ha.1; omega) hda hda', hva]
              rw [hwf.indirect_commit r a A hdc hds ha hva,
                hwf'.indirect_commit r a A hdc' hds' ha' hsame]
            · exact absurd hva ha.2.1
            · exact absurd hva hda

open scoped Classical in
/-- And it satisfies the interface. -/
theorem chooseSound_least [LinearOrder BlockId] : ChooseSound D (chooseLeast D) where
  sound := by
    intro A r b h
    simp only [chooseLeast] at h
    split at h
    · rename_i hne
      have hb : (((slotBlocks D r).filter (fun b => IndirectCommit D A r b)).min' hne) = b :=
        Option.some.inj h
      have hmem := Finset.min'_mem ((slotBlocks D r).filter (fun b => IndirectCommit D A r b)) hne
      rw [hb] at hmem
      exact (Finset.mem_filter.1 hmem).2
    · exact absurd h (by simp)
  total := by
    intro A r ⟨b, hb⟩
    have hne : ((slotBlocks D r).filter (fun b => IndirectCommit D A r b)).Nonempty :=
      ⟨b, Finset.mem_filter.2 ⟨hb.1, hb⟩⟩
    refine ⟨((slotBlocks D r).filter (fun b => IndirectCommit D A r b)).min' hne, ?_⟩
    simp only [chooseLeast, dif_pos hne]

/-- **Lemma 12's side conditions, discharged on the DAG.** Each
validator's direct verdicts are direct verdicts of the universe, because
a view is a sub-DAG and the rules are existential in it. Under that
reading every field is one of the theorems above: Lemma 8 for the two
commit fields, Lemmas 6 and 7 for the skip fields, and Lemmas 3 and 5 for
the two that say the anchor can always see a direct commit. -/
theorem exclusions_of_dag {choose : BlockId → ℕ → Option BlockId}
    (hch : ChooseSound D choose)
    {dc dc' : ℕ → BlockId → Prop} {ds ds' : ℕ → Prop}
    (hdc : ∀ r l, dc r l → l ∈ slotBlocks D r ∧ DirectCommit D l)
    (hdc' : ∀ r l, dc' r l → l ∈ slotBlocks D r ∧ DirectCommit D l)
    (hds : ∀ r, ds r → DirectSkip D r) (hds' : ∀ r, ds' r → DirectSkip D r) :
    Exclusions dc dc' ds ds' choose (fun r A => A ∈ D.ids ∧ r + 3 ≤ (D.block A).round) := by
  -- a slot's blocks share the leader and the round, so two of them conflict
  have hconf : ∀ (r : ℕ) (l b : BlockId), l ∈ slotBlocks D r → b ∈ slotBlocks D r → l ≠ b →
      Conflicting D l b ∧ l ∈ D.ids ∧ b ∈ D.ids ∧ (D.block l).creator = D.leader r := by
    intro r l b hl hb hne
    simp only [slotBlocks, blocksAt, Finset.mem_filter] at hl hb
    exact ⟨⟨hne, by rw [hl.1.2, hb.1.2], by rw [hl.2, hb.2]⟩, hl.1.1, hb.1.1, hl.2⟩
  refine
    { commit_unique := fun r l l' h h' =>
        direct_commit_unique (hdc r l h).1 (hdc' r l' h').1 (hdc r l h).2 (hdc' r l' h').2
      commit_bars_skip := fun r l h hs =>
        no_directSkip_of_commit (hdc r l h).1 (hdc r l h).2 (hds' r hs)
      commit_bars_skip' := fun r l h hs =>
        no_directSkip_of_commit (hdc' r l h).1 (hdc' r l h).2 (hds r hs)
      commit_forces_choose := fun r l A hA h =>
        hch.total A r ⟨l, indirectCommit_of_directCommit hA.1 hA.2 (hdc r l h).1 (hdc r l h).2⟩
      commit_forces_choose' := fun r l A hA h =>
        hch.total A r ⟨l, indirectCommit_of_directCommit hA.1 hA.2 (hdc' r l h).1 (hdc' r l h).2⟩
      skip_bars_choose := fun r A b hs hchb =>
        no_indirectCommit_of_directSkip (hds r hs) (hch.sound A r b hchb)
      skip_bars_choose' := fun r A b hs hchb =>
        no_indirectCommit_of_directSkip (hds' r hs) (hch.sound A r b hchb)
      commit_pins_choose := ?_
      commit_pins_choose' := ?_ } <;>
  · intro r l A b h hchb
    by_contra hne
    obtain ⟨hlslot, hcom⟩ := by first | exact hdc r l h | exact hdc' r l h
    have hind := hch.sound A r b hchb
    obtain ⟨hcf, hlids, hbids, hlead⟩ := hconf r l b hlslot hind.1 (Ne.symm hne)
    exact no_indirectCommit_of_directCommit hlids hbids hlslot hlead hcf hcom hind

end FinWhale

end LeanDag
