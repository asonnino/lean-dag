import LeanDagTest.HammerheadTwo.Agreement
import LeanDag.HammerheadTwo.Progress.Proof
import Mathlib.Tactic.IntervalCases

/-!
# Hammerhead 2.0 witnesses — progress on data

`LiveOn` quantifies over every DAG the rule calls good, so it cannot be
decided in general; a *test rule* makes it finite. `hhLive` is Mysticeti
with `Good U Rnd N := U = Usun ∧ Rnd = 1 ∧ N = 8` — `Usun` decides
rounds up to `5`, one wave below `8` — so `hhLive.LiveOn` at a schedule
is a statement about five slots and five rounds of `Usun`, settled leaf
by leaf: a wrong verdict fails the build. `Good` is a bare data field
that no law constrains, which is what makes the test rule legitimate.

What the file exhibits:

* **HH8a applied on data.** From the height-`0` run at interval `4` and
  gap `0`, `Progress.holds` yields a height-`1` run. Its configuration
  `1` is read through HH3 against `run2`: `count 1 = 2`, `start 1 = 5`,
  `anchor 0 = 5` — the healthy step. The theorem supplies existence; the
  values are forced on every inhabitant of the type by `update` and
  HH3, which is the strongest reading a `Nonempty` conclusion admits.
* **Progress from height one.** At interval `1` a height-`1` run on the
  full view extends to height `2` by the theorem, at gap `0` and at gap
  `1` alike, and HH3 identifies the result with `runP1`.
* **A gap that matters.** `Usk` is `Usun` with one block referenced by
  its author alone, so slot `2` is directly skipped: `LiveOn` at gap
  `0` is *false* there and at gap `1` true, and the theorem's anchor —
  slot `3` — skips slot `2`, which lies past the threshold:
  `anchor_least` is exercised through the theorem.
* **`LiveOn` is not automatic.** One round further, `N = 9`, `Usun` is
  not live at gap `0`: round `6` has no committed slot. And `UpdBounded`
  fails for rules that leave the range.
* `EveryHeight` reaches height `1` under horizon `8` at interval `4` and
  height `2` at interval `1`; height `2` at interval `4` needs `13`.
-/

namespace LeanDagTest
namespace HammerheadTwo

set_option maxRecDepth 2000000

open LeanDag LeanDag.HammerheadTwo

/-- (E) the `with` spelling -/
def hhLive : LiveRule (Fin 4) (Fin 32) Unit :=
  { mysticeti with Good := fun U Rnd N => U = Usun ∧ Rnd = 1 ∧ N = 8 }

/-- (E) the `where` spelling -/
def hhLive' : LiveRule (Fin 4) (Fin 32) Unit where
  toBaseRule := mysticeti
  Good := fun U Rnd N => U = Usun ∧ Rnd = 1 ∧ N = 8

example : hhLive.toBaseRule = hhRule32 := rfl
example : hhLive.full Usun = Vsun := rfl
example : hhLive.full Usun = LeanDag.View.full Usun := rfl
example : hhLive.waveLength = 3 := rfl

-- `Good` is a genuine predicate.
example : hhLive.Good Usun 1 8 := ⟨rfl, rfl, rfl⟩
example : ¬ hhLive.Good Usun 1 9 := fun h => absurd h.2.2 (by decide)

abbrev sched1 : Slots (Fin 4) := Sched hhLeader hhWin 1 (by decide) (by decide)

/-- `LiveOn` at count `1`, gap `0`, on `Usun`: slots `1`–`5` commit directly. -/
theorem hhLive_liveOn : hhLive.LiveOn sched1 0 := by
  rintro U Rnd N ⟨rfl, rfl, rfl⟩
  have hw : hhLive.waveLength = 3 := rfl
  refine ⟨?_, ?_⟩
  · intro κ h1 h2
    simp only [Sched_slotRound, Nat.div_one] at h1 h2
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 ∨ κ = 4 ∨ κ = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · exact ⟨some 5, Decided.directCommit (S := sched1)
        (by decide) (by decide)⟩
    · exact ⟨some 10, Decided.directCommit (S := sched1)
        (by decide) (by decide)⟩
    · exact ⟨some 15, Decided.directCommit (S := sched1)
        (by decide) (by decide)⟩
    · exact ⟨some 16, Decided.directCommit (S := sched1)
        (by decide) (by decide)⟩
    · exact ⟨some 21, Decided.directCommit (S := sched1)
        (by decide) (by decide)⟩
  · intro r h1 h2
    have : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, by simp, 5, Decided.directCommit (S := sched1)
        (by decide) (by decide)⟩
    · exact ⟨2, by simp, by simp, 10, Decided.directCommit (S := sched1)
        (by decide) (by decide)⟩
    · exact ⟨3, by simp, by simp, 15, Decided.directCommit (S := sched1)
        (by decide) (by decide)⟩
    · exact ⟨4, by simp, by simp, 16, Decided.directCommit (S := sched1)
        (by decide) (by decide)⟩
    · exact ⟨5, by simp, by simp, 21, Decided.directCommit (S := sched1)
        (by decide) (by decide)⟩

abbrev hhUpd : UpdateRule hhLive.toBaseRule := Aimd.rule hhRule32 hhP hhLeader hhWin

theorem hhUpd_bounded : UpdBounded hhP hhUpd :=
  (Aimd.holds (Fin 4) (Fin 32) Unit hhRule32 hhP hhLeader hhWin).1

/-- The height-`0` run. -/
def run0 : PartialRun hhLive.toBaseRule hhP hhLeader hhWin hhUpd Usun (hhLive.full Usun) 0 :=
  PartialRun.zero _ hhP hhLeader hhWin hhUpd Usun (hhLive.full Usun)

/-- HH8a applied on data: a height-`1` run exists, and HH3 identifies its
configuration `1` with `run2`'s — two leaders after round `5`. -/
example :
    ∃ Rn1 : PartialRun hhLive.toBaseRule hhP hhLeader hhWin hhUpd Usun (hhLive.full Usun) 1,
    Rn1.count 1 = 2 ∧ Rn1.start 1 = 5 ∧ Rn1.anchor 0 = 5 := by
  obtain ⟨Rn1⟩ := (Progress.holds (Fin 4) (Fin 32) Unit hhLive laws32 hhP hhLeader hhWin hhUpd
    hhUpd_bounded 0).1 Usun 1 8 0 run0 hhLive_liveOn
    (show hhLive.Good Usun 1 8 from ⟨rfl, rfl, rfl⟩) (by decide) (by decide)
  refine ⟨Rn1, ?_⟩
  have h := (Agreement.holds (Fin 4) (Fin 32) Unit hhRule32 laws32 hhP hhLeader hhWin _)
    Usun (hhLive.full Usun) Vsun 1 1 Rn1 run2 1 (by decide)
  have h0 := (Agreement.holds (Fin 4) (Fin 32) Unit hhRule32 laws32 hhP hhLeader hhWin _)
    Usun (hhLive.full Usun) Vsun 1 1 Rn1 run2 0 (by decide)
  exact ⟨h.2.1, h.1, (h0.2.2.2 (by decide)).1⟩

-- The bound form too.
example :
    ∃ Rn1 : PartialRun hhLive.toBaseRule hhP hhLeader hhWin hhUpd Usun (hhLive.full Usun) 1,
    Rn1.start 1 ≤ 0 + 4 + 1 + 0 :=
  progress_exists laws32 hhUpd_bounded run0 hhLive_liveOn
    (show hhLive.Good Usun 1 8 from ⟨rfl, rfl, rfl⟩) (by decide) (by decide)

-- horizon values
example : horizon hhP hhLive 0 1 = 8 := by decide
example : horizon hhP hhLive 0 2 = 13 := by decide

/-- `LiveOn` at every count `1`–`4`, gap `0`, on `Usun`. -/
theorem hhLive_liveOn_all : ∀ m (hm : 0 < m) (hmax : m ≤ hhP.maxLeaders),
    hhLive.LiveOn (Sched hhLeader hhWin m hm hmax) 0 := by
  intro m hm hmax
  have hmax' : m ≤ 4 := hmax
  rintro U Rnd N ⟨rfl, rfl, rfl⟩
  have hw : hhLive.waveLength = 3 := rfl
  refine ⟨?_, ?_⟩
  · intro κ h1 h2
    simp only [Sched_slotRound] at h1 h2
    refine ⟨some ⟨(4 * (κ / m) + (κ / m + κ % m) % 4) % 32, Nat.mod_lt _ (by decide)⟩,
      ?_⟩
    interval_cases m
    · obtain ⟨hlo, hhi⟩ : 1 ≤ κ ∧ κ < 6 := by omega
      interval_cases κ <;>
        exact Decided.directCommit (S := Sched hhLeader hhWin 1 (by decide) (by decide))
          (by decide) (by decide)
    · obtain ⟨hlo, hhi⟩ : 2 ≤ κ ∧ κ < 12 := by omega
      interval_cases κ <;>
        exact Decided.directCommit (S := Sched hhLeader hhWin 2 (by decide) (by decide))
          (by decide) (by decide)
    · obtain ⟨hlo, hhi⟩ : 3 ≤ κ ∧ κ < 18 := by omega
      interval_cases κ <;>
        exact Decided.directCommit (S := Sched hhLeader hhWin 3 (by decide) (by decide))
          (by decide) (by decide)
    · obtain ⟨hlo, hhi⟩ : 4 ≤ κ ∧ κ < 24 := by omega
      interval_cases κ <;>
        exact Decided.directCommit (S := Sched hhLeader hhWin 4 (by decide) (by decide))
          (by decide) (by decide)
  · intro r h1 h2
    refine ⟨m * r, ?_, ?_, ⟨(4 * r + r % 4) % 32, Nat.mod_lt _ (by decide)⟩, ?_⟩
    · simp only [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
    · simp only [Sched_slotRound, Nat.mul_div_cancel_left _ hm]; omega
    · obtain ⟨hlo, hhi⟩ : 1 ≤ r ∧ r ≤ 5 := by omega
      interval_cases m <;> interval_cases r <;>
        exact Decided.directCommit
        (S := Sched hhLeader hhWin _ (by decide) (by decide)) (by decide) (by decide)

/-- HH8b applied on data: height `1` under horizon `8`. -/
example :
    Nonempty (PartialRun hhLive.toBaseRule hhP hhLeader hhWin hhUpd Usun (hhLive.full Usun) 1) :=
  everyHeight laws32 hhUpd_bounded hhLive_liveOn_all
    (show hhLive.Good Usun 1 8 from ⟨rfl, rfl, rfl⟩) le_rfl 1 (by decide)

-- Through `holds`.
example :
    Nonempty (PartialRun hhLive.toBaseRule hhP hhLeader hhWin hhUpd Usun (hhLive.full Usun) 1) :=
  ((Progress.holds (Fin 4) (Fin 32) Unit hhLive laws32 hhP hhLeader hhWin hhUpd hhUpd_bounded 0).2
    hhLive_liveOn_all Usun 1 8 ⟨rfl, rfl, rfl⟩ le_rfl 1 (by decide))
example :
    Nonempty (PartialRun hhLive.toBaseRule hhP hhLeader hhWin hhUpd Usun (hhLive.full Usun) 1) :=
  ((Progress.holds (Fin 4) (Fin 32) Unit hhLive laws32 hhP hhLeader hhWin hhUpd hhUpd_bounded 0).1
    Usun 1 8 0 run0 hhLive_liveOn ⟨rfl, rfl, rfl⟩ (by decide) (by decide))

-- Height 2 at interval 4 is out of the horizon: `13 ≤ 8` is false.
example : ¬ (horizon hhP hhLive 0 2 ≤ 8) := by decide

/-! ## Rules that leave the range are not bounded -/

example : ¬ UpdBounded hhP (fun _ _ _ _ => ((0, 0) : ℕ × ℕ) : UpdateRule hhRule32) :=
  fun h => absurd (h 1 0 Usun 0).1 (by decide)
example : ¬ UpdBounded hhP (fun _ _ _ _ => ((5, 0) : ℕ × ℕ) : UpdateRule hhRule32) :=
  fun h => absurd (h 1 0 Usun 0).2 (by decide)


/-! ## Progress from height one, at interval one

`runP1v` is `runP1'` on the full view. At interval `1` its configuration
`1` starts at round `2`, and `2 + 1 + 1 + c + 3 ≤ 8` for `c ≤ 1`: the
theorem extends it at gap `0` and at gap `1` — the latter with the
clause answered at the top of its window — and HH3 identifies the
result with `runP1` at height `2`. -/

theorem hhLive_liveOn1 : hhLive.LiveOn sched1 1 := by
  rintro U Rnd N ⟨rfl, rfl, rfl⟩
  have hw : hhLive.waveLength = 3 := rfl
  refine ⟨(hhLive_liveOn Usun 1 8 ⟨rfl, rfl, rfl⟩).1, ?_⟩
  intro r h1 h2
  have : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl
  · exact ⟨2, by simp, by simp, 10, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
  · exact ⟨3, by simp, by simp, 15, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
  · exact ⟨4, by simp, by simp, 16, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
  · exact ⟨5, by simp, by simp, 21, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩

/-! ## (i) Progress from height `1` at interval `1` on `Usun` -/

abbrev hhUpd1 : UpdateRule hhLive.toBaseRule := Aimd.rule hhRule32 hhP1 hhLeader hhWin

theorem hhUpd1_bounded : UpdBounded hhP1 hhUpd1 :=
  (Aimd.holds (Fin 4) (Fin 32) Unit hhRule32 hhP1 hhLeader hhWin).1

/-- `runP1'` on the full view. -/
def runP1v : PartialRun hhLive.toBaseRule hhP1 hhLeader hhWin hhUpd1 Usun (hhLive.full Usun) 1 where
  start := fun k => if k = 0 then 0 else 2
  count := fun _ => 1
  backoff := fun k => if k = 0 then 0 else 1
  anchor := fun _ => 2
  vdct := fun _ κ => if κ = 1 then some 5 else if κ = 2 then some 10 else none
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun _ => Nat.one_pos
  count_le := fun _ => by decide
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp at h1 h2
    have : κ = 1 ∨ κ = 2 := by omega
    rcases this with rfl | rfl <;>
      exact Decided.directCommit (S := sched1) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨10, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, Nat.div_one] at h
    have hi : hhP1.interval = 1 := rfl
    omega
  start_succ := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  update := by
    intro k hk A hA
    have hk0 : k = 0 := by omega
    subst hk0
    have hA' : A = 10 := by simp at hA; exact hA.symm
    subst hA'
    decide

-- gap 0: 2 + 1 + 1 + 0 + 3 = 7 ≤ 8
example :
    ∃ Rn2 : PartialRun hhLive.toBaseRule hhP1 hhLeader hhWin hhUpd1 Usun (hhLive.full Usun) 2,
    Rn2.start 2 = 4 ∧ Rn2.count 2 = 1 ∧ Rn2.backoff 2 = 2 ∧ Rn2.anchor 1 = 4 := by
  obtain ⟨Rn2⟩ := (Progress.holds (Fin 4) (Fin 32) Unit hhLive laws32 hhP1 hhLeader hhWin hhUpd1
    hhUpd1_bounded 0).1 Usun 1 8 1 runP1v hhLive_liveOn ⟨rfl, rfl, rfl⟩ (by decide) (by decide)
  refine ⟨Rn2, ?_⟩
  have h := (Agreement.holds (Fin 4) (Fin 32) Unit hhRule32 laws32 hhP1 hhLeader hhWin _)
    Usun (hhLive.full Usun) Vsun 2 2 Rn2 runP1 2 (by decide)
  have h1 := (Agreement.holds (Fin 4) (Fin 32) Unit hhRule32 laws32 hhP1 hhLeader hhWin _)
    Usun (hhLive.full Usun) Vsun 2 2 Rn2 runP1 1 (by decide)
  exact ⟨h.1, h.2.1, h.2.2.1, (h1.2.2.2 (by decide)).1⟩

-- gap 1: 2 + 1 + 1 + 1 + 3 = 8 ≤ 8, the horizon exactly
example :
    ∃ Rn2 : PartialRun hhLive.toBaseRule hhP1 hhLeader hhWin hhUpd1 Usun (hhLive.full Usun) 2,
    Rn2.start 2 = 4 ∧ Rn2.count 2 = 1 ∧ Rn2.backoff 2 = 2 ∧ Rn2.anchor 1 = 4 := by
  obtain ⟨Rn2⟩ := (Progress.holds (Fin 4) (Fin 32) Unit hhLive laws32 hhP1 hhLeader hhWin hhUpd1
    hhUpd1_bounded 1).1 Usun 1 8 1 runP1v hhLive_liveOn1 ⟨rfl, rfl, rfl⟩ (by decide) (by decide)
  refine ⟨Rn2, ?_⟩
  have h := (Agreement.holds (Fin 4) (Fin 32) Unit hhRule32 laws32 hhP1 hhLeader hhWin _)
    Usun (hhLive.full Usun) Vsun 2 2 Rn2 runP1 2 (by decide)
  have h1 := (Agreement.holds (Fin 4) (Fin 32) Unit hhRule32 laws32 hhP1 hhLeader hhWin _)
    Usun (hhLive.full Usun) Vsun 2 2 Rn2 runP1 1 (by decide)
  exact ⟨h.1, h.2.1, h.2.2.1, (h1.2.2.2 (by decide)).1⟩

-- Height 3 at interval 1 is out of the horizon: 4 + 1 + 1 + 0 + 3 = 9 > 8.
example : ¬ (runP1.start 2 + hhP1.interval + 1 + 0 + hhLive.waveLength ≤ 8) := by decide

-- EveryHeight at interval 1, gap 0: horizon 2 * 2 + 3 = 7 ≤ 8 gives height 2.
example : horizon hhP1 hhLive 0 2 = 7 := by decide
example :
    Nonempty (PartialRun hhLive.toBaseRule hhP1 hhLeader hhWin hhUpd1 Usun (hhLive.full Usun) 2) :=
  ((Progress.holds (Fin 4) (Fin 32) Unit hhLive laws32 hhP1 hhLeader hhWin hhUpd1
    hhUpd1_bounded 0).2
    hhLive_liveOn_all Usun 1 8 ⟨rfl, rfl, rfl⟩ le_rfl 2 (by decide))
example : ¬ (horizon hhP1 hhLive 0 3 ≤ 8) := by decide

/-! ## Not live one round further

With the horizon at `9`, gap `0` asks round `6` for a committed slot;
its candidate, block `26`, has no certificate in `Usun`, so no
derivation commits it, direct or indirect. -/

def hhLive9 : LiveRule (Fin 4) (Fin 32) Unit :=
  { mysticeti with Good := fun U Rnd N => U = Usun ∧ Rnd = 1 ∧ N = 9 }

/-- Slot 6's only candidate is block 26 … -/
theorem hall6 : ∀ L : Fin 32, hhRule32.IsLeaderBlock sched1 Usun 6 L → L = 26 := by decide
/-- … which has no certificate anywhere (a certificate would sit at round 8). -/
theorem cert26 : certificates Usun 26 6 = ∅ := by decide

/-- No commit at round `6` on `Usun`, by either commit rule. -/
theorem no_commit6 : ∀ L, ¬ hhRule32.Decided sched1 (hhLive9.full Usun) 6 (some L) := by
  intro L hL
  cases hL with
  | directCommit hcand hdir =>
    have := hall6 L hcand; subst this
    exact absurd hdir (by decide)
  | indirectCommit _ _ _ _ hcand hcert =>
    have := hall6 L hcand; subst this
    obtain ⟨C, hC⟩ := certificates_nonempty_of_certifiedIn hcert
    simp only [Sched_slotRound, Nat.div_one, cert26] at hC
    exact absurd hC (Finset.notMem_empty C)

theorem hhLive9_not_liveOn0 : ¬ hhLive9.LiveOn sched1 0 := by
  intro h
  obtain ⟨-, h2⟩ := h Usun 1 9 ⟨rfl, rfl, rfl⟩
  obtain ⟨κ, hlo, hhi, L, hL⟩ := h2 6 (by decide) (by decide)
  simp only [Sched_slotRound, Nat.div_one] at hlo hhi
  have hκ : κ = 6 := by omega
  subst hκ
  exact no_commit6 L hL

-- and the horizon-9 application of Progress at interval 4, gap 1, would need exactly this:
example : (0 : ℕ) + hhP.interval + 1 + 1 + hhLive9.waveLength ≤ 9 := by decide

#print axioms hhLive9_not_liveOn0

/-! ## A skipped slot past the threshold: the anchor skips it

`Usk` is `Usun` with block `10` (round `2`, author `2`) referenced only
by its author's own next block, so three round-`3` blocks blame it and
slot `2` of `Sched 1` is directly skipped; everything else commits. At
gap `0` the clause fails at round `2`; at gap `1` it holds, answered by
slot `3`. From the height-`0` run at interval `1`, the theorem's anchor
is slot `3`, past the skipped slot `2` which lies past the threshold —
`anchor_least` with content, obtained from the theorem. -/

def skBlk : Fin 32 → Block (Fin 4) (Fin 32) Unit := fun i =>
  { round := (i : ℕ) / 4
    creator := ⟨(i : ℕ) % 4, Nat.mod_lt _ (by omega)⟩
    refs := if (i : ℕ) < 4 then ∅ else
      (Finset.univ.filter fun j : Fin 32 =>
        (j : ℕ) / 4 + 1 = (i : ℕ) / 4 ∧ ((j : ℕ) = 10 → (i : ℕ) = 14))
    payload := () }

def Usk : BlockUniverse (Fin 4) (Fin 32) Unit where
  ids := Finset.univ
  block := skBlk
  complete := by decide
  valid := by decide
  no_equivocation := by decide

def hhLiveSk : LiveRule (Fin 4) (Fin 32) Unit :=
  { mysticeti with Good := fun U Rnd N => U = Usk ∧ Rnd = 1 ∧ N = 8 }

-- Slot 2's candidate is block 10, blamed by 12, 13, 15.
theorem hallSk : ∀ L : Fin 32, hhRule32.IsLeaderBlock sched1 Usk 2 L → L = 10 := by decide
example : hhRule32.IsLeaderBlock sched1 Usk 2 10 := by decide
example : ¬ hhRule32.DirectCommitIn (hhLiveSk.full Usk) 10 2 := by decide
example : hhRule32.Decided sched1 (hhLiveSk.full Usk) 2 none :=
  Decided.directSkip (S := sched1) (fun L hL => by have := hallSk L hL; subst this; decide)
-- Slot 3 (block 15) commits.
example : hhRule32.Decided sched1 (hhLiveSk.full Usk) 3 (some 15) :=
  Decided.directCommit (S := sched1) (by decide) (by decide)

theorem hhLiveSk_not_liveOn0 : ¬ hhLiveSk.LiveOn sched1 0 := by
  intro h
  obtain ⟨-, h2⟩ := h Usk 1 8 ⟨rfl, rfl, rfl⟩
  obtain ⟨κ, hlo, hhi, L, hL⟩ := h2 2 (by decide) (by decide)
  simp only [Sched_slotRound, Nat.div_one] at hlo hhi
  have hκ : κ = 2 := by omega
  subst hκ
  have hskip : hhRule32.Decided sched1 (hhLiveSk.full Usk) 2 none :=
    Decided.directSkip (S := sched1) (fun L hL => by have := hallSk L hL; subst this; decide)
  exact Option.some_ne_none L (laws32.agree sched1 _ _ 2 _ _ hL hskip)

/-- Gap `1`: the round-`2` window is answered by slot `3`. -/
theorem hhLiveSk_liveOn1 : hhLiveSk.LiveOn sched1 1 := by
  rintro U Rnd N ⟨rfl, rfl, rfl⟩
  have hw : hhLiveSk.waveLength = 3 := rfl
  refine ⟨?_, ?_⟩
  · intro κ h1 h2
    simp only [Sched_slotRound, Nat.div_one] at h1 h2
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 ∨ κ = 4 ∨ κ = 5 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl
    · exact ⟨some 5, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨none, Decided.directSkip (S := sched1)
        (fun L hL => by have := hallSk L hL; subst this; decide)⟩
    · exact ⟨some 15, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨some 16, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨some 21, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
  · intro r h1 h2
    have : r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl
    · exact ⟨1, by simp, by simp, 5, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨3, by simp, by simp, 15, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨3, by simp, by simp, 15, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩
    · exact ⟨4, by simp, by simp, 16, Decided.directCommit
        (S := sched1) (by decide) (by decide)⟩

abbrev hhUpdSk : UpdateRule hhLiveSk.toBaseRule := Aimd.rule hhRule32 hhP1 hhLeader hhWin

theorem hhUpdSk_bounded : UpdBounded hhP1 hhUpdSk :=
  (Aimd.holds (Fin 4) (Fin 32) Unit hhRule32 hhP1 hhLeader hhWin).1

def run0sk : PartialRun hhLiveSk.toBaseRule hhP1 hhLeader hhWin hhUpdSk Usk (hhLiveSk.full Usk) 0 :=
  PartialRun.zero _ hhP1 hhLeader hhWin hhUpdSk Usk (hhLiveSk.full Usk)

-- The rule at anchor 15, interval 1: nothing scores, unhealthy.
example : observed hhRule32 hhP1 hhLeader hhWin Usk 15 1 (by decide) (by decide) = 0 := by decide
example : Aimd.rule hhRule32 hhP1 hhLeader hhWin 1 0 Usk 15 = (1, 1) := by decide

def vdSk : ℕ → ℕ → Option (Fin 32) :=
  fun _ κ => if κ = 1 then some 5 else if κ = 3 then some 15 else none

/-- Anchor at slot `3`, past the skipped slot `2`: `anchor_least` is
non-vacuous at `κ = 2`. -/
def runSk :
    PartialRun hhLiveSk.toBaseRule hhP1 hhLeader hhWin hhUpdSk Usk (hhLiveSk.full Usk) 1 where
  start := fun k => if k = 0 then 0 else 3
  count := fun _ => 1
  backoff := fun k => if k = 0 then 0 else 1
  anchor := fun _ => 3
  vdct := vdSk
  init := ⟨rfl, rfl, rfl⟩
  count_pos := fun _ => Nat.one_pos
  count_le := fun _ => by decide
  closed := by
    intro k hk κ h1 h2
    have hk0 : k = 0 := by omega
    subst hk0
    simp at h1 h2
    have : κ = 1 ∨ κ = 2 ∨ κ = 3 := by omega
    rcases this with rfl | rfl | rfl
    · exact Decided.directCommit (S := sched1) (by decide) (by decide)
    · exact Decided.directSkip (S := sched1)
        (fun L hL => by have := hallSk L hL; subst this; decide)
    · exact Decided.directCommit (S := sched1) (by decide) (by decide)
  anchor_commits := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    exact ⟨⟨15, rfl⟩, by decide⟩
  anchor_least := by
    intro k hk κ hκ h
    have hk0 : k = 0 := by omega
    subst hk0
    simp only [if_true, Nat.div_one] at h hκ
    have hi : hhP1.interval = 1 := rfl
    have : κ = 2 := by omega
    subst this
    rfl
  start_succ := by
    intro k hk
    have hk0 : k = 0 := by omega
    subst hk0
    rfl
  update := by
    intro k hk A hA
    have hk0 : k = 0 := by omega
    subst hk0
    have hA' : A = 15 := by simp [vdSk] at hA; exact hA.symm
    subst hA'
    decide

-- HH8a at gap 1 (0 + 1 + 1 + 1 + 3 = 6 ≤ 8): the anchor the theorem finds is slot 3,
-- not slot 2, which lies past the threshold and is skipped.
example :
    ∃ Rn1 : PartialRun hhLiveSk.toBaseRule hhP1 hhLeader hhWin hhUpdSk Usk (hhLiveSk.full Usk) 1,
    Rn1.anchor 0 = 3 ∧ Rn1.start 1 = 3 ∧ Rn1.count 1 = 1 ∧ Rn1.backoff 1 = 1 ∧
      Rn1.vdct 0 2 = none ∧ Rn1.start 0 + hhP1.interval < 2 / Rn1.count 0 := by
  obtain ⟨Rn1⟩ := (Progress.holds (Fin 4) (Fin 32) Unit hhLiveSk laws32 hhP1 hhLeader hhWin
    hhUpdSk hhUpdSk_bounded 1).1 Usk 1 8 0 run0sk hhLiveSk_liveOn1 ⟨rfl, rfl, rfl⟩
    (by decide) (by decide)
  refine ⟨Rn1, ?_⟩
  have h := (Agreement.holds (Fin 4) (Fin 32) Unit hhRule32 laws32 hhP1 hhLeader hhWin _)
    Usk (hhLiveSk.full Usk) (hhLiveSk.full Usk) 1 1 Rn1 runSk 1 (by decide)
  have h0 := (Agreement.holds (Fin 4) (Fin 32) Unit hhRule32 laws32 hhP1 hhLeader hhWin _)
    Usk (hhLiveSk.full Usk) (hhLiveSk.full Usk) 1 1 Rn1 runSk 0 (by decide)
  have hv := (h0.2.2.2 (by decide)).2 2
  rw [h0.1, h0.2.1, h.1] at hv
  refine ⟨(h0.2.2.2 (by decide)).1, h.1, h.2.1, h.2.2.1, hv (by decide) (by decide), ?_⟩
  rw [h0.1, h0.2.1]; decide

#print axioms hhLiveSk_not_liveOn0
#print axioms runSk

#print axioms hhLive_liveOn_all
#print axioms Progress.holds

end HammerheadTwo
end LeanDagTest
