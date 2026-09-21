import LeanDag.RedSnapper.Helpers.VotingFive
import LeanDag.RedSnapper.Five.RecoveryTermination.Statement
import LeanDagTest.RedSnapper.LivenessHardening
import LeanDagTest.RedSnapper.Coin
import LeanDagTest.RedSnapper.FreezeHardening

/-!
# Witness hardening: which route reads what

* **The anchor route reads the universe and is class-gated.** Over a
  view holding genesis only, with the certificate block committed:
  `U6Full`'s *owned* `tx 0` has no finalized verdict — `fullFinal` needs
  the certificate in the view, and `mixedFinal` is shut to an owned
  transaction — while `UMixSix`'s *mixed* `tx 2`, under the same view,
  is final by `mixedFinal`, which reads the anchor's history and not
  the view.
* **RS4's anchor claim, owned branch.** `ULive` with its round-3 block
  `10` committed: `finalizeOnCommit` finalises the owned `tx 0` — the
  claim has no class gate.
* **`FullVerdict` needs the certificate round.** On `ULiveT` — `ULive`
  cut after round 2 — every other hypothesis holds under the `5f+1`
  rule and no finalized verdict is derivable.
* **`ConflictDecides`, the unlock case, with no marker anywhere.** On
  `U6Frag` with anchors `[6, 17]` the trigger exists and no validator
  ever freezes: the marker input is false, and is not asked for, since
  block `17` is a full unlock certificate — which decides.
-/

namespace LeanDagTest

namespace RedSnapper

open LeanDag LeanDag.RedSnapper

set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096

/-! ### The anchor route reads the universe and is class-gated -/

/-- The view holding genesis only, over `U6Full`. -/
def VGenFull : View U6Full where
  ids := {0, 1, 2, 3, 4, 5}
  subset_ids := by decide
  complete := by decide

/-- `U6Full`'s certificate block, committed. -/
def AFullCert : Anchors U6Full where
  seq := [12]
  mem := by decide
  chained := by simp

private theorem full_no_cert_in_view : ∀ C ∈ VGenFull.ids, ¬ IsFullCertDec U6Full C 0 := by
  decide

-- Owned: the certificate exists under a committed anchor, and the view
-- that lacks it justifies nothing.
example : IsFullCert U6Full 12 0 := (isFullCert_iff (by decide)).mpr (by decide)
example : ¬ VerdictFive U6Full AFullCert VGenFull (· ≤ ·) 0 Fate.finalized := by
  intro h
  cases h with
  | fullFinal _ hC hcert =>
      exact full_no_cert_in_view _ hC ((isFullCert_iff (VGenFull.subset_ids hC)).mp hcert)
  | mixedFinal hm _ _ _ _ _ => exact absurd hm (by decide)
  | recoveryFinal hres hi hj helig hmin =>
      obtain ⟨-, hij, ⟨aₖ, a, hlk, hla, -⟩, -⟩ := hres
      have h1 := (List.getElem?_eq_some_iff.mp hlk).1
      have h2 := (List.getElem?_eq_some_iff.mp hla).1
      simp [AFullCert] at h1 h2
      omega

/-- The view holding genesis only, over `UMixSix`. -/
def VGenMix : View UMixSix where
  ids := {0, 1, 2, 3, 4, 5}
  subset_ids := by decide
  complete := by decide

-- Mixed: the same view, and the anchor route fires regardless of it.
example : (12 : Fin 13) ∉ VGenMix.ids := by decide
example : VerdictFive UMixSix AMixSixCert VGenMix (· ≤ ·) 2 Fate.finalized :=
  .mixedFinal (i := 0) (a := 12) (C := 12) (by decide) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide)) (by decide) Reaches.refl
    ((isFullCert_iff (by decide)).mpr (by decide))

/-! ### RS4's anchor claim, owned branch -/

/-- `ULive`'s round-3 block of validator `1`, committed. -/
def ALiveCert : Anchors ULive where
  seq := [10]
  mem := by decide
  chained := by simp

example : (ULive.block 10).author ∈ (Correct : Finset (Fin 4)) ∧
    (ULive.block 10).round = 3 ∧ Owned (0 : Fin 4) := by decide
example : TxVerdict ULive ALiveCert (View.full ULive) 0 Fate.finalized :=
  .finalizeOnCommit (i := 0) (a := 10) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))
    (fun h => absurd ((conflicted_iff (by decide)).mp h) (by decide))
    ((hasCert_iff (by decide)).mpr (by decide))

/-! ### `FullVerdict` needs the certificate round -/

/-- An empty anchor sequence over `ULiveT`. -/
def ALiveT : Anchors ULiveT where
  seq := []
  mem := by simp
  chained := List.Pairwise.nil

-- Every other hypothesis of `FullVerdict` holds on the truncated universe ...
example : VotingRuleFive ULiveT := votingRuleFive_of_dec (by decide)
example : SynchronisedOn ULiveT (Correct : Finset (Fin 4)) 1 := by
  unfold SynchronisedOn; decide
example : PopulatedOn ULiveT (Correct : Finset (Fin 4)) 2 := by
  unfold PopulatedOn; decide
example : ¬ PopulatedOn ULiveT (Correct : Finset (Fin 4)) 3 := by
  unfold PopulatedOn; decide

-- ... and no finalized verdict is derivable: no block carries a full
-- certificate yet.
private theorem liveT_no_cert : ∀ C ∈ ULiveT.ids, ¬ IsFullCertDec ULiveT C 0 := by decide

example : ¬ VerdictFive ULiveT ALiveT (View.full ULiveT) (· ≤ ·) 0 Fate.finalized := by
  intro h
  cases h with
  | fullFinal _ hC hcert =>
      have hid := (View.full ULiveT).subset_ids hC
      exact liveT_no_cert _ hid ((isFullCert_iff hid).mp hcert)
  | mixedFinal hm _ _ _ _ _ => exact absurd hm (by decide)
  | recoveryFinal hres hi hj helig hmin => simp [ALiveT] at hi

/-! ### `ConflictDecides`, the unlock case, with no marker anywhere -/

/-- `U6Frag`'s trigger and its round-3 block, committed. -/
def AFragUnlock : Anchors U6Frag where
  seq := [6, 17]
  mem := by decide
  chained := by
    refine List.Pairwise.cons (fun x hx => ?_) (List.pairwise_singleton _ _)
    rw [List.mem_singleton] at hx
    subst hx
    exact (mem_history_iff (by decide)).mp (by decide)

-- The committed anchor 6 sees the conflict and triggers ...
example : Conflicted U6Frag 6 0 := (conflicted_iff (by decide)).mpr (by decide)
example : TriggerAt U6Frag AFragUnlock 0 0 := triggerAt_iff.mpr (by decide)

-- ... no validator ever freezes, so the marker input is false here ...
example : ∀ v : Fin 6, ∀ a ∈ U6Frag.ids, ¬ FrozenDec U6Frag 6 v 0 a := by decide

-- ... and it is not asked for: a full unlock certificate exists, and
-- drops the candidates.
example : IsFullUnlockCert U6Frag 17 0 := (isFullUnlockCert_iff (by decide)).mpr (by decide)
example : VerdictFive U6Frag AFragUnlock (View.full U6Frag) (· ≤ ·) 0 Fate.dropped :=
  .fullUnlockDrop (C := 17) (b := 17) (by decide)
    ((isFullUnlockCert_iff (by decide)).mpr (by decide)) (by decide)
    ((mem_candidates_iff (by decide)).mp (by decide))

/-! ### What the `5f+1` relation does not decide: the loser of a fast commit

Record finding 33, on data. On `U6RecFull` the owned `tx 0` holds a full
certificate at block `12`; commit that block alone. The owned rival
`tx 1` is valid and lies in the anchor's history — it is in the global
order — and `tx 0` is finalized. No route gives `tx 1` a verdict: the
relation has the paper's drops only, and none of them fires. -/

/-- `U6RecFull`'s certificate block, committed alone. -/
def ARecFullCert : Anchors U6RecFull where
  seq := [12]
  mem := by decide
  chained := by simp

example : Owned (1 : Fin 4) ∧ Transactions.Valid (1 : Fin 4) ∧ Conflict (0 : Fin 4) 1 := by
  decide
example : IsCandidate U6RecFull 12 0 1 := (mem_candidates_iff (by decide)).mp (by decide)
example : VerdictFive U6RecFull ARecFullCert (View.full U6RecFull) (· ≤ ·) 0 Fate.finalized :=
  .fullFinal (C := 12) (by decide) (by decide) ((isFullCert_iff (by decide)).mpr (by decide))

private theorem recFull_no_unlock : ∀ C ∈ U6RecFull.ids, ¬ IsFullUnlockCertDec U6RecFull C 0 := by
  decide
private theorem recFull_no_cert_rival : ∀ C ∈ U6RecFull.ids, ¬ IsFullCertDec U6RecFull C 1 := by
  decide
private theorem recFullCert_no_pair {i j : ℕ} {aₖ a : Fin 24} (hij : i < j)
    (hlk : ARecFullCert.seq[i]? = some aₖ) (hla : ARecFullCert.seq[j]? = some a) : False := by
  have h1 := (List.getElem?_eq_some_iff.mp hlk).1
  have h2 := (List.getElem?_eq_some_iff.mp hla).1
  simp [ARecFullCert] at h1 h2
  omega

-- The loser is never dropped ...
example : ¬ VerdictFive U6RecFull ARecFullCert (View.full U6RecFull) (· ≤ ·) 1 Fate.dropped := by
  intro h
  cases h with
  | fullUnlockDrop hC hunlock _ _ =>
      have hid := (View.full U6RecFull).subset_ids hC
      exact recFull_no_unlock _ hid ((isFullUnlockCert_iff hid).mp hunlock)
  | recoveryDropLoser hres hlk hla _ _ _ _ => exact recFullCert_no_pair hres.2.1 hlk hla
  | recoveryDropBot hres hlk hla _ _ => exact recFullCert_no_pair hres.2.1 hlk hla

-- ... and, of course, never finalized.
example : ¬ VerdictFive U6RecFull ARecFullCert (View.full U6RecFull) (· ≤ ·) 1
    Fate.finalized := by
  intro h
  cases h with
  | fullFinal _ hC hcert =>
      have hid := (View.full U6RecFull).subset_ids hC
      exact recFull_no_cert_rival _ hid ((isFullCert_iff hid).mp hcert)
  | mixedFinal hm _ _ _ _ _ => exact absurd hm (by decide)
  | recoveryFinal hres hlk hla _ _ => exact recFullCert_no_pair hres.2.1 hlk hla

end RedSnapper

end LeanDagTest
