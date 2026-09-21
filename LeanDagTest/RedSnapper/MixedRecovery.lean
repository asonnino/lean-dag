import LeanDag.RedSnapper.Five.RecoveryTermination.Statement
import LeanDag.RedSnapper.Five.Agreement.Statement
import LeanDagTest.RedSnapper.FreezeHardening

/-!
# Witness: owned and mixed transactions compete in the recovery

The `5f+1` recovery with a *mixed* candidate — the case the owned-only
reading of `Candidates` could not express. `fourTxs` has one mixed
transaction and gives it no rival, so the scenario needs its own table:
`threeTxs`, three valid transactions on `o0`, of which `tx 0` is mixed.

* **`UMixRec`** — `U6Rec`'s table read over `threeTxs`: the rivals are
  the mixed `tx 0` and the owned `tx 1`. One of the two candidates is
  mixed, so under the owned-only reading the trigger anchor saw a single
  candidate and nothing ever triggered; over `Candidates` as the paper
  now has it, anchor `6` triggers, the five correct validators freeze,
  anchor `17` resolves, and the election is the mixed transaction's:
  `recoveryFinal` finalises it and `recoveryDropLoser` drops the owned
  rival. The finalised mixed transaction is a candidate of a committed
  anchor — RS8's `MixedViaAnchor` on data, through the recovery route.
* **Termination's premises** — on `UMixRec` no certificate exists, so
  `ConflictDecides`' marker input is live: the trigger exists and its
  markers are absent up to it and complete under anchor `17`.
* **`UMixRecFull`** — `U6RecFull`'s table over `threeTxs`: all five
  correct validators stand at the mixed `tx 0`, block `12` is its full
  certificate, and anchor `6`, below it, still triggers. Two routes now
  finalise the same mixed transaction — `mixedFinal` at anchor `17`,
  strictly above the certificate, and `recoveryFinal` at the same
  anchor — the cross-route pair RS8's agreement covers; the reflection
  claim's `W = {tx}` is checked for a mixed certificate; the certificate
  in anchor `17`'s history keeps it from triggering, which a mutant
  reading only owned certificates gets wrong; and `ConflictDecides`' C5
  input is live: the certificate lies under committed anchors.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-- Three valid transactions on `o0`; `0` is mixed, `1` and `2` owned. -/
instance threeTxs : Transactions (Fin 3) (Fin 2) where
  input := fun _ => 0
  Valid := fun _ => True
  Mixed := fun tx => tx = 0

example : Conflict (0 : Fin 3) 1 ∧ Transactions.Mixed (0 : Fin 3) ∧ Owned (1 : Fin 3) := by
  decide

/-- `fourTxs`' transactions `0` and `1` read in `threeTxs`. -/
def recast (t : Fin 4) : Fin 3 := if t = 0 then 0 else if t = 1 then 1 else 2

/-- A `fourTxs` block read over `threeTxs`: the same round, author,
parents, stances and markers. -/
def recastBlock (b : Block (Fin 6) (Fin 24) (Fin 4) (Fin 2)) :
    Block (Fin 6) (Fin 24) (Fin 3) (Fin 2) :=
  { round := b.round, author := b.author, parents := b.parents,
    txs := b.txs.image recast,
    declares := fun o => match b.declares o with
      | some (.ack t) => some (.ack (recast t))
      | some .bot => some .bot
      | none => none,
    freezes := b.freezes }

/-- `lkRec` over `threeTxs`. -/
def lkMixRec : Fin 24 → Block (Fin 6) (Fin 24) (Fin 3) (Fin 2) := fun i =>
  recastBlock (lkRec i)

def UMixRec : Universe (Fin 6) (Fin 24) (Fin 3) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkMixRec
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- The committed anchors of `UMixRec`: `ARec`'s. -/
def AMixRec : Anchors UMixRec where
  seq := [0, 6, 17, 22]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.Pairwise.cons (fun x hx => ?_)
      (List.Pairwise.cons (fun x hx => ?_) (List.pairwise_singleton _ _)))
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)
    · rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)

example : MoveDiscipline UMixRec := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline UMixRec := freezeDiscipline_iff.mpr (by decide)

-- The conflict at the trigger anchor is between a mixed and an owned
-- candidate, and it triggers.
example : IsCandidate UMixRec 6 0 0 ∧ IsCandidate UMixRec 6 0 1 :=
  ⟨(mem_candidates_iff (by decide)).mp (by decide),
    (mem_candidates_iff (by decide)).mp (by decide)⟩
example : ∀ tx ∈ candidates UMixRec 6 0, tx = 0 ∨ tx = 1 := by decide
example : Triggers UMixRec 6 0 := (triggers_iff (by decide)).mpr (by decide)
example : TriggerAt UMixRec AMixRec 0 1 := triggerAt_iff.mpr (by decide)
example : ResolvesFiveAt UMixRec AMixRec 0 1 2 := resolvesFiveAt_iff.mpr (by decide)

-- The election goes to the mixed transaction; the owned rival has no
-- support.
example : EligibleFive UMixRec 6 17 0 0 := (eligibleFive_iff (by decide)).mpr (by decide)
example : ¬ EligibleFive UMixRec 6 17 0 1 := fun h =>
  absurd ((eligibleFive_iff (by decide)).mp h) (by decide)

-- The verdicts: the mixed transaction finalised, the owned one dropped.
example : VerdictFive UMixRec AMixRec (View.full UMixRec) (· ≤ ·) 0 Fate.finalized :=
  .recoveryFinal (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _)
example : VerdictFive UMixRec AMixRec (View.full UMixRec) (· ≤ ·) 1 Fate.dropped :=
  .recoveryDropLoser (tx' := 0) (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _) (by decide)

-- The finalised mixed transaction is a candidate of a committed anchor.
example : ∃ (i : ℕ) (a : Fin 24), AMixRec.seq[i]? = some a ∧ IsCandidate UMixRec a 0 0 :=
  ⟨2, 17, by decide, (mem_candidates_iff (by decide)).mp (by decide)⟩

/-! ### The premises of `ConflictDecides`, on data -/

-- No certificate of either kind exists, so the lemma's third case applies
-- and its C5 input on mixed certificates is idle.
example : ∀ C ∈ UMixRec.ids, ¬ IsFullUnlockCertDec UMixRec C 0 := by decide
example : ∀ tx : Fin 3, ∀ C ∈ UMixRec.ids, ¬ IsFullCertDec UMixRec C tx := by decide

-- The committed anchor `6` sees the conflict.
example : Conflicted UMixRec 6 0 := (conflicted_iff (by decide)).mpr (by decide)

-- The marker input: no quorum at or before the trigger index, and every
-- correct validator frozen under the later anchor `17`.
example : ∀ i' ≤ 1, ∀ a', AMixRec.seq[i']? = some a' → ¬ FreezeQuorumDec UMixRec 6 0 a' := by
  decide
example : ∀ v ∈ (Correct : Finset (Fin 6)), FrozenDec UMixRec 6 v 0 17 := by decide

/-! ### A mixed certificate and the recovery agree -/

/-- `lkRecFull` over `threeTxs`. -/
def lkMixRecFull : Fin 24 → Block (Fin 6) (Fin 24) (Fin 3) (Fin 2) := fun i =>
  recastBlock (lkRecFull i)

def UMixRecFull : Universe (Fin 6) (Fin 24) (Fin 3) (Fin 2) where
  ids := Finset.univ.erase 23
  block := lkMixRecFull
  complete := by decide
  valid := by decide
  no_equivocation := by decide
  self_parent := by decide

/-- The committed anchors of `UMixRecFull`: `ARecFull`'s. -/
def AMixRecFull : Anchors UMixRecFull where
  seq := [0, 6, 17, 22]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.Pairwise.cons (fun x hx => ?_)
      (List.Pairwise.cons (fun x hx => ?_) (List.pairwise_singleton _ _)))
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact (mem_history_iff (by decide)).mp (by decide)
      rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)
    · rw [List.mem_singleton] at hx
      subst hx
      exact (mem_history_iff (by decide)).mp (by decide)

example : MoveDiscipline UMixRecFull := moveDiscipline_iff.mpr (by decide)
example : FreezeDiscipline UMixRecFull := freezeDiscipline_iff.mpr (by decide)

-- The mixed transaction is fully certified at round 2; the trigger, one
-- round below, does not see the certificate; the resolving anchor does.
example : IsFullCert UMixRecFull 12 0 := (isFullCert_iff (by decide)).mpr (by decide)
example : Triggers UMixRecFull 6 0 := (triggers_iff (by decide)).mpr (by decide)
example : ResolvesFiveAt UMixRecFull AMixRecFull 0 1 2 := resolvesFiveAt_iff.mpr (by decide)

-- A mixed certificate in the history blocks the trigger. A mutant whose
-- certificate conjunct reads owned transactions only says anchor 17
-- triggers.
example : ¬ Triggers UMixRecFull 17 0 := fun h =>
  absurd ((triggers_iff (by decide)).mp h) (by decide)
example : (∃ tx ∈ candidates UMixRecFull 17 0, ∃ tx' ∈ candidates UMixRecFull 17 0, tx ≠ tx') ∧
    (¬ ∃ b ∈ historyIn UMixRecFull 17, IsFullUnlockCertDec UMixRecFull b 0) ∧
    ¬ ∃ tx ∈ candidates UMixRecFull 17 0, Owned tx ∧
      ∃ b ∈ historyIn UMixRecFull 17, IsFullCertDec UMixRecFull b tx := by decide

-- The reflection claim for a mixed certificate: `W = {tx 0}`.
example : EligibleFive UMixRecFull 6 17 0 0 := (eligibleFive_iff (by decide)).mpr (by decide)
example : ∀ tx' : Fin 3, EligibleFiveDec UMixRecFull 6 17 0 tx' → tx' = 0 := by decide

-- Two routes, one fate: the anchor route reads the certificate strictly
-- below anchor 17, the recovery route elects the same transaction there.
example : (UMixRecFull.block 12).round < (UMixRecFull.block 17).round := by decide
example : VerdictFive UMixRecFull AMixRecFull (View.full UMixRecFull) (· ≤ ·) 0
    Fate.finalized :=
  .mixedFinal (i := 2) (a := 17) (C := 12) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide)
    ((mem_history_iff (by decide)).mp (by decide))
    ((isFullCert_iff (by decide)).mpr (by decide))
example : VerdictFive UMixRecFull AMixRecFull (View.full UMixRecFull) (· ≤ ·) 0
    Fate.finalized :=
  .recoveryFinal (i := 1) (j := 2) (aₖ := 6) (a := 17)
    (resolvesFiveAt_iff.mpr (by decide)) (by decide) (by decide)
    ((eligibleFive_iff (by decide)).mpr (by decide))
    (fun _ _ => Fin.zero_le _)

-- `ConflictDecides`' C5 input, live: every full certificate of the mixed
-- transaction — block 12 and the later ones above it — lies under a
-- committed anchor.
example : ∀ C ∈ UMixRecFull.ids, IsFullCertDec UMixRecFull C 0 →
    C ∈ historyIn UMixRecFull 17 ∨ C ∈ historyIn UMixRecFull 22 := by decide
example : ¬ ∀ C ∈ UMixRecFull.ids, IsFullCertDec UMixRecFull C 0 →
    C ∈ historyIn UMixRecFull 17 := by decide

end RedSnapper

end LeanDagTest
