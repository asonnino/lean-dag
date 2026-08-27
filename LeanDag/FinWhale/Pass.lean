import LeanDag.FinWhale.View
import Mathlib.Order.Interval.Finset.Nat

/-!
# FinWhale — the reverse pass, as a procedure

`WellFormed` states what the reverse pass must satisfy; nothing so far
produces an assignment satisfying it, so every result above it is
conditional on a validator's verdicts being well formed. This file
defines the pass and proves that they are.

The definition runs the slots downward from the horizon. `slotVerdict`
decides one slot from the verdicts above it — a direct commit if there is
one, a direct skip if there is one, and otherwise the first slot above
`r + 2` that is not skipped, read through the tie-break. `passFrom`
threads that down from `N + 1`, where nothing is decided, to `0`.

Two facts make the definition usable. Slots above `N` are undecided
(`passFrom_gt`), which is `hbound`; and at or below `N` the pass agrees
with `slotVerdict` applied to itself (`decOf_eq`), which is the equation
the five `WellFormed` fields are read off.

What this does not discharge is `hk` — that a commit sequence stops at
its first undecided slot is a condition on the horizon the caller picks,
and `all_decided` is what establishes it.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] [LinearOrder BlockId] {Payload : Type*}

/-- The blocks of a slot that are directly committed. At most one, by
`direct_commit_unique`. -/
def directCommits (D : Dag Validator BlockId Payload) (r : ℕ) : Finset BlockId :=
  (slotBlocks D r).filter (fun l => DirectCommit D l)

/-- The candidates for the anchor of `r`: the slots above `r + 2` and
below the horizon that the verdicts above do not skip. -/
def anchorCands (N : ℕ) (above : ℕ → Verdict BlockId) (r : ℕ) : Finset ℕ :=
  (Finset.Ioc (r + 2) N).filter (fun a => above a ≠ Verdict.skip)

/-- **The indirect verdict**: read the first non-skipped slot above
`r + 2` through the tie-break. Where there is none the slot stays
undecided, which is what an undecided anchor gives too. -/
def anchorVerdict (choose : BlockId → ℕ → Option BlockId) (N : ℕ)
    (above : ℕ → Verdict BlockId) (r : ℕ) : Verdict BlockId :=
  if hc : (anchorCands N above r).Nonempty then
    match above ((anchorCands N above r).min' hc) with
    | Verdict.commit A =>
        match choose A r with
        | some b => Verdict.commit b
        | none => Verdict.skip
    | _ => Verdict.undecided
  else Verdict.undecided

/-- **One slot's verdict, from the verdicts above it.** -/
def slotVerdict (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) (N : ℕ)
    (above : ℕ → Verdict BlockId) (r : ℕ) : Verdict BlockId :=
  if h : (directCommits D r).Nonempty then Verdict.commit ((directCommits D r).min' h)
  else if DirectSkip D r then Verdict.skip
  else anchorVerdict choose N above r

/-- **The pass, from slot `s` downward.** Slots below `s` are left
undecided; slot `s` is decided from the verdicts above it, and those are
what the pass from `s + 1` gives. -/
def passFrom (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) (N : ℕ) (s : ℕ) : ℕ → Verdict BlockId :=
  if h : N < s then fun _ => Verdict.undecided
  else fun r =>
    if r = s then slotVerdict D choose N (passFrom D choose N (s + 1)) s
    else passFrom D choose N (s + 1) r
termination_by N + 1 - s
decreasing_by all_goals omega

/-- **The verdicts of a validator whose view is `D`.** -/
def decOf (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) (N : ℕ) : ℕ → Verdict BlockId :=
  passFrom D choose N 0

variable {D : Dag Validator BlockId Payload} {choose : BlockId → ℕ → Option BlockId} {N : ℕ}

/-- Above the horizon nothing is decided. -/
theorem passFrom_of_gt {s : ℕ} (h : N < s) :
    passFrom D choose N s = fun _ => Verdict.undecided := by
  rw [passFrom]
  simp [h]

/-- At or above the slot the pass has reached, the pass is the pass from
that slot. -/
theorem passFrom_of_ge : ∀ k s r : ℕ, N + 1 - s ≤ k → s ≤ r →
    passFrom D choose N s r = passFrom D choose N r r := by
  intro k
  induction k with
  | zero =>
    intro s r hk hr
    rw [passFrom, dif_pos (by omega), passFrom, dif_pos (by omega)]
  | succ k ih =>
    intro s r hk hr
    rcases Nat.lt_or_ge N s with h | h
    · rw [passFrom_of_gt h, passFrom_of_gt (by omega)]
    · rcases eq_or_lt_of_le hr with rfl | hlt
      · rfl
      · rw [passFrom, dif_neg (by omega)]
        simp only [if_neg (by omega : ¬ r = s)]
        exact ih (s + 1) r (by omega) (by omega)


omit [LinearOrder BlockId] in
/-- The indirect verdict reads the verdicts above `r + 2` and no others,
so assignments agreeing there give the same answer. -/
theorem anchorVerdict_congr {above above' : ℕ → Verdict BlockId} {r : ℕ}
    (h : ∀ a, r + 2 < a → a ≤ N → above a = above' a) :
    anchorVerdict choose N above r = anchorVerdict choose N above' r := by
  have hc : anchorCands N above r = anchorCands N above' r := by
    ext a
    simp only [anchorCands, Finset.mem_filter, Finset.mem_Ioc]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, by rw [← h a h1 h2]; exact h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨h1, h2⟩, by rw [h a h1 h2]; exact h3⟩
  unfold anchorVerdict
  by_cases hne : (anchorCands N above' r).Nonempty
  · have hne0 : (anchorCands N above r).Nonempty := hc ▸ hne
    rw [dif_pos hne0, dif_pos hne]
    have hmin : (anchorCands N above r).min' hne0 = (anchorCands N above' r).min' hne := by
      congr 1
    rw [hmin]
    have hb : r + 2 < (anchorCands N above' r).min' hne ∧
        (anchorCands N above' r).min' hne ≤ N := by
      have hmem := Finset.min'_mem _ hne
      simp only [anchorCands, Finset.mem_filter, Finset.mem_Ioc] at hmem
      exact hmem.1
    rw [h _ hb.1 hb.2]
  · rw [dif_neg (fun hx => hne (hc ▸ hx)), dif_neg hne]

/-- The same, for the whole slot verdict: the direct rules read the DAG,
not the verdicts. -/
theorem slotVerdict_congr {above above' : ℕ → Verdict BlockId} {r : ℕ}
    (h : ∀ a, r + 2 < a → a ≤ N → above a = above' a) :
    slotVerdict D choose N above r = slotVerdict D choose N above' r := by
  unfold slotVerdict
  rw [anchorVerdict_congr h]

/-- **The equation the pass satisfies.** At or below the horizon, a
slot's verdict is `slotVerdict` applied to the pass itself. -/
theorem decOf_eq {r : ℕ} (hr : r ≤ N) :
    decOf D choose N r = slotVerdict D choose N (decOf D choose N) r := by
  have hself : passFrom D choose N 0 r = passFrom D choose N r r :=
    passFrom_of_ge (N + 1) 0 r (by omega) (by omega)
  rw [decOf, hself, passFrom, dif_neg (by omega), if_pos rfl]
  refine slotVerdict_congr fun a h1 h2 => ?_
  rw [passFrom_of_ge (N + 1) (r + 1) a (by omega) (by omega),
    passFrom_of_ge (N + 1) 0 a (by omega) (by omega)]

/-- Above the horizon the pass decides nothing. -/
theorem decOf_of_gt {r : ℕ} (hr : N < r) : decOf D choose N r = Verdict.undecided := by
  rw [decOf, passFrom_of_ge (N + 1) 0 r (by omega) (by omega), passFrom_of_gt hr]

/-! ## The pass is well formed -/

variable {D : Dag Validator BlockId Payload}

omit [LinearOrder BlockId] in
/-- A slot with a direct skip lies two rounds below the horizon: the skip
exhibits round-`(r+2)` blocks. -/
theorem round_le_of_directSkip {N r : ℕ} (hN : ∀ b ∈ D.ids, (D.block b).round ≤ N)
    (h : DirectSkip D r) : r + 2 ≤ N := by
  obtain ⟨-, nonev, hnon, hnonb⟩ := h
  have := params_arith (Validator := Validator)
  have hpos : 0 < nonev.card := by simp only [spQuorum] at hnon; omega
  obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
  obtain ⟨b, hb, -, -⟩ := hnonb v hv
  simp only [blocksAt, Finset.mem_filter] at hb
  have := hN b hb.1
  omega

/-- **The anchor the pass finds is the anchor.** Where the candidates are
nonempty their least member is the first non-skipped slot above
`r + 2`. -/
theorem anchor_min' {r : ℕ} (hne : (anchorCands N (decOf D choose N) r).Nonempty) :
    Anchor (decOf D choose N) r ((anchorCands N (decOf D choose N) r).min' hne) := by
  have hb : r + 2 < (anchorCands N (decOf D choose N) r).min' hne ∧
      (anchorCands N (decOf D choose N) r).min' hne ≤ N ∧
      decOf D choose N ((anchorCands N (decOf D choose N) r).min' hne) ≠ Verdict.skip := by
    have hmem := Finset.min'_mem _ hne
    simp only [anchorCands, Finset.mem_filter, Finset.mem_Ioc] at hmem
    exact ⟨hmem.1.1, hmem.1.2, hmem.2⟩
  refine ⟨hb.1, hb.2.2, fun t ht1 ht2 => ?_⟩
  by_contra hskip
  have hmemt : t ∈ anchorCands N (decOf D choose N) r := by
    simp only [anchorCands, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨ht1, by have := hb.2.1; omega⟩, hskip⟩
  have hle : (anchorCands N (decOf D choose N) r).min' hne ≤ t := Finset.min'_le _ t hmemt
  omega

/-- And an anchor below the horizon is that least member. -/
theorem eq_min'_of_anchor {r a : ℕ} (hanc : Anchor (decOf D choose N) r a) (ha : a ≤ N) :
    ∃ hne : (anchorCands N (decOf D choose N) r).Nonempty,
      (anchorCands N (decOf D choose N) r).min' hne = a := by
  have hmem : a ∈ anchorCands N (decOf D choose N) r := by
    simp only [anchorCands, Finset.mem_filter, Finset.mem_Ioc]
    exact ⟨⟨hanc.1, ha⟩, hanc.2.1⟩
  refine ⟨⟨a, hmem⟩, ?_⟩
  have hle := Finset.min'_le _ a hmem
  rcases eq_or_lt_of_le hle with h | h
  · exact h
  · exact absurd (anchor_min' ⟨a, hmem⟩).2.1
      (by rw [hanc.2.2 _ (anchor_min' ⟨a, hmem⟩).1 h]; simp)

/-- An anchor above the horizon means no candidate at all: everything
between is skipped, and nothing above the horizon is decided. -/
theorem anchorCands_eq_empty {r a : ℕ} (hanc : Anchor (decOf D choose N) r a) (ha : N < a) :
    ¬ (anchorCands N (decOf D choose N) r).Nonempty := by
  rintro ⟨t, ht⟩
  simp only [anchorCands, Finset.mem_filter, Finset.mem_Ioc] at ht
  exact ht.2 (hanc.2.2 t ht.1.1 (by omega))

/-- **The reverse pass is well formed.** Its direct rules are the DAG's
own, and `choose` is whatever deterministic rule the validator applies.
`hN` is the horizon: no block of the view sits above it. -/
theorem wellFormed_decOf {N : ℕ} (hN : ∀ b ∈ D.ids, (D.block b).round ≤ N)
    (choose : BlockId → ℕ → Option BlockId) :
    WellFormed (fun r l => l ∈ slotBlocks D r ∧ DirectCommit D l)
      (fun r => DirectSkip D r) choose (decOf D choose N) where
  direct_commit r l := by
    rintro ⟨hslot, hcom⟩
    have hru : (D.block l).round = r ∧ l ∈ D.ids := by
      simp only [slotBlocks, blocksAt, Finset.mem_filter] at hslot
      exact ⟨hslot.1.2, hslot.1.1⟩
    have hr : r ≤ N := by have := hN l hru.2; omega
    have hne : (directCommits D r).Nonempty := ⟨l, Finset.mem_filter.2 ⟨hslot, hcom⟩⟩
    rw [decOf_eq hr, slotVerdict, dif_pos hne]
    have hmem : (directCommits D r).min' hne ∈ slotBlocks D r ∧
        DirectCommit D ((directCommits D r).min' hne) := by
      have h := Finset.min'_mem _ hne
      simp only [directCommits, Finset.mem_filter] at h
      exact h
    rw [direct_commit_unique hmem.1 hslot hmem.2 hcom]
  direct_skip r hskip := by
    have hr : r ≤ N := by have := round_le_of_directSkip hN hskip; omega
    have hne : ¬ (directCommits D r).Nonempty := by
      rintro ⟨l, hl⟩
      simp only [directCommits, Finset.mem_filter] at hl
      exact no_directSkip_of_commit hl.1 hl.2 hskip
    rw [decOf_eq hr, slotVerdict, dif_neg hne, if_pos hskip]
  indirect_undecided r a hdc hds hanc hau := by
    rcases Nat.lt_or_ge N r with hr | hr
    · exact decOf_of_gt hr
    have hne : ¬ (directCommits D r).Nonempty := by
      rintro ⟨l, hl⟩
      simp only [directCommits, Finset.mem_filter] at hl
      exact hdc ⟨l, hl.1, hl.2⟩
    rw [decOf_eq hr, slotVerdict, dif_neg hne, if_neg hds, anchorVerdict]
    rcases Nat.lt_or_ge N a with hbig | hsmall
    · rw [dif_neg (anchorCands_eq_empty hanc hbig)]
    · obtain ⟨hc, hmin⟩ := eq_min'_of_anchor hanc hsmall
      rw [dif_pos hc, hmin, hau]
  indirect_commit r a A hdc hds hanc hcom := by
    have ha : a ≤ N := by
      by_contra hbig
      rw [decOf_of_gt (by omega : N < a)] at hcom
      cases hcom
    have hr : r ≤ N := by have := hanc.1; omega
    have hne : ¬ (directCommits D r).Nonempty := by
      rintro ⟨l, hl⟩
      simp only [directCommits, Finset.mem_filter] at hl
      exact hdc ⟨l, hl.1, hl.2⟩
    obtain ⟨hc, hmin⟩ := eq_min'_of_anchor hanc ha
    rw [decOf_eq hr, slotVerdict, dif_neg hne, if_neg hds, anchorVerdict, dif_pos hc, hmin,
      hcom]
    rfl
  has_anchor r hdc hds hdecided := by
    rcases Nat.lt_or_ge N r with hr | hr
    · exact absurd (decOf_of_gt hr) hdecided
    have hne : ¬ (directCommits D r).Nonempty := by
      rintro ⟨l, hl⟩
      simp only [directCommits, Finset.mem_filter] at hl
      exact hdc ⟨l, hl.1, hl.2⟩
    by_cases hc : (anchorCands N (decOf D choose N) r).Nonempty
    · exact ⟨_, anchor_min' hc⟩
    · have hund : decOf D choose N r = Verdict.undecided := by
        rw [decOf_eq hr, slotVerdict, dif_neg hne, if_neg hds, anchorVerdict, dif_neg hc]
      exact absurd hund hdecided

/-! ## What the pass discharges -/

/-- **A committed verdict names a block of its slot.** Either the pass
took a direct commit, which is one, or the tie-break named it, and
`ChooseSound` says what it names is a candidate. -/
theorem mem_slotBlocks_of_decOf {D' : Dag Validator BlockId Payload} {N : ℕ}
    {choose : BlockId → ℕ → Option BlockId}
    (hsub : ∀ r, slotBlocks D' r ⊆ slotBlocks D r) (hch : ChooseSound D choose)
    {r : ℕ} {A : BlockId} (h : decOf D' choose N r = Verdict.commit A) :
    A ∈ slotBlocks D r := by
  rcases Nat.lt_or_ge N r with hr | hr
  · rw [decOf_of_gt hr] at h; cases h
  rw [decOf_eq hr, slotVerdict] at h
  by_cases hne : (directCommits D' r).Nonempty
  · rw [dif_pos hne] at h
    have hmem : (directCommits D' r).min' hne ∈ slotBlocks D' r := by
      have hx := Finset.min'_mem _ hne
      simp only [directCommits, Finset.mem_filter] at hx
      exact hx.1
    have : (directCommits D' r).min' hne = A := by injection h
    exact hsub r (this ▸ hmem)
  · rw [dif_neg hne] at h
    by_cases hskip : DirectSkip D' r
    · rw [if_pos hskip] at h; cases h
    rw [if_neg hskip, anchorVerdict] at h
    by_cases hc : (anchorCands N (decOf D' choose N) r).Nonempty
    · rw [dif_pos hc] at h
      rcases hv : decOf D' choose N ((anchorCands N (decOf D' choose N) r).min' hc) with A' | - | -
      · rcases hch2 : choose A' r with - | b
        · simp only [hv, hch2] at h
          cases h
        · simp only [hv, hch2] at h
          have hb : b = A := by injection h
          exact hb ▸ (hch.sound A' r b hch2).1
      · simp only [hv] at h
        cases h
      · simp only [hv] at h
        cases h
    · rw [dif_neg hc] at h; cases h

/-- **Safety, with the verdicts computed rather than assumed.** Two
validators running the reverse pass on their own views of one DAG deliver
prefix-comparable sequences.

Three of `safety_of_views`' hypotheses are gone: `WellFormed`, because
the pass satisfies it; the slot condition, because the pass names only
slot blocks; and finiteness, because nothing above the horizon is
decided. What is left is `hk` — how far each validator's sequence runs —
which is a choice of horizon, and `all_decided` is what establishes
it. -/
theorem safety_of_pass {V V' : Finset BlockId} (hV : IsView D V) (hV' : IsView D V')
    {choose : BlockId → ℕ → Option BlockId} (hch : ChooseSound D choose) {N : ℕ}
    (hNV : ∀ b ∈ V, (D.block b).round ≤ N) (hNV' : ∀ b ∈ V', (D.block b).round ≤ N)
    {k k' : ℕ}
    (hk : ∀ s, s < k → decOf (restrict D V hV) choose N s ≠ Verdict.undecided)
    (hk' : ∀ s, s < k' → decOf (restrict D V' hV') choose N s ≠ Verdict.undecided)
    (hist : BlockId → List BlockId) :
    linearise hist (commitSeq (decOf (restrict D V hV) choose N) k) <+:
        linearise hist (commitSeq (decOf (restrict D V' hV') choose N) k') ∨
      linearise hist (commitSeq (decOf (restrict D V' hV') choose N) k') <+:
        linearise hist (commitSeq (decOf (restrict D V hV) choose N) k) :=
  safety_of_views hV hV' (wellFormed_decOf hNV choose) (wellFormed_decOf hNV' choose) hch
    (fun _ _ h => mem_slotBlocks_of_decOf (fun _ => slotBlocks_restrict) hch h)
    (fun _ _ h => mem_slotBlocks_of_decOf (fun _ => slotBlocks_restrict) hch h)
    (fun s (hs : N + 1 ≤ s) => ⟨decOf_of_gt (by omega), decOf_of_gt (by omega)⟩) hk hk' hist

end FinWhale

end LeanDag
