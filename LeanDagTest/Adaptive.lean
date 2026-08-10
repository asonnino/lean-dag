import LeanDag.Adaptive.Basic
import LeanDag.Adaptive.Run
import LeanDagTest.Model

/-!
# Adaptive leaders, witnessed: the induced instance and the bounded relation

The `U7` universe of `Model.lean` under reassigned leaders. Three things
are exhibited on data before anything is proved from the definitions:

* `slotsOf` genuinely reassigns: under `aSwap`, slot `1` is led by
  validator `1`, its leader block is `13` rather than `12`, and the
  slot's verdict *changes* — the same DAG, read under a different
  assignment, commits a different block. Adaptivity is not a relabelling.
* `DecidedWithin` derives real verdicts at real bounds: the direct
  commit at slot `1` and the indirect commit at slot `0` (anchor `1`,
  the `Model.lean` configuration) both fit within bound `2`.
* `decidedWithin_congr` transports a bounded verdict across assignments
  that differ only above the bound — the exact situation of an epoch
  judged against a schedule whose later epochs are not yet determined.
-/

namespace LeanDagTest

open LeanDag

/-- One leader per round on the `U7` schedule: slot rounds are `3k`. -/
theorem u7_inj : Function.Injective (Slots.slotRound (Validator := Fin 4)) := by
  intro a b h
  change 3 * (a / 1) = 3 * (b / 1) at h
  omega

/-- The base assignment, as a plain function. -/
def aBase : ℕ → Fin 4 := fun _ => 0

/-- Slot `1`'s leader moves to validator `1`; everything else unchanged. -/
def aSwap : ℕ → Fin 4 := fun k => if k = 1 then 1 else 0

/-- An assignment differing from the base only at slots `≥ 2`. -/
def aHigh : ℕ → Fin 4 := fun k => if 2 ≤ k then 1 else 0

-- The induced instance reassigns the leader and keeps the rounds.
example : (slotsOf u7_inj aSwap).leader 1 = 1 := rfl
example : (slotsOf u7_inj aSwap).slotRound 1 = 3 := rfl

-- Under the base assignment the induced instance *is* the instance.
example : slotsOf u7_inj (Slots.leader (Validator := Fin 4)) =
    (inferInstance : Slots (Fin 4)) := slotsOf_base u7_inj

-- Under `aSwap`, slot 1's candidate is block 13, not block 12.
example : IsLeaderBlock (S := slotsOf u7_inj aSwap) U7 1 13 := by decide
example : ¬ IsLeaderBlock (S := slotsOf u7_inj aSwap) U7 1 12 := by decide

/-- The bounded direct commit at slot `1`, base assignment, bound `2`. -/
theorem u7_decidedWithin_slot1 :
    DecidedWithin (S := slotsOf u7_inj aBase) U7 V7 2 1 (some 12) :=
  DecidedWithin.directCommit (by omega) (by decide) (by decide)

/-- The bounded indirect commit at slot `0`, anchored on slot `1` — the
`Model.lean` configuration, now with both slots inside bound `2`. -/
theorem u7_decidedWithin_slot0 :
    DecidedWithin (S := slotsOf u7_inj aBase) U7 V7 2 0 (some 0) :=
  DecidedWithin.indirectCommit (j := 1) (A := 12) (by omega) (by omega) (by decide)
    u7_decidedWithin_slot1
    (fun _ h1 h2 _ => absurd h2 (by omega))
    (by decide)
    ⟨8, by decide, Reaches.single (by decide)⟩

-- The structural lemmas, exercised.
example : Decided (S := slotsOf u7_inj aBase) U7 V7 1 (some 12) :=
  u7_decidedWithin_slot1.toDecided
example : (1 : ℕ) < 2 := u7_decidedWithin_slot1.lt_bound
example : DecidedWithin (S := slotsOf u7_inj aBase) U7 V7 5 1 (some 12) :=
  u7_decidedWithin_slot1.mono (by omega)

/-- Congruence across the bound: `aHigh` differs from the base only at
slots the bound excludes, so the slot-`0` verdict transports. -/
theorem u7_decidedWithin_slot0_high :
    DecidedWithin (S := slotsOf u7_inj aHigh) U7 V7 2 0 (some 0) :=
  decidedWithin_congr
    (fun m hm => by unfold aBase aHigh; rw [if_neg (by omega)])
    u7_decidedWithin_slot0

/-- **The verdict moves with the assignment.** Under `aSwap` the slot-`1`
candidate is block `13`, and the view commits it directly: the same DAG,
under a reassigned leader, decides a different block for the slot. -/
theorem u7_decidedWithin_slot1_swap :
    DecidedWithin (S := slotsOf u7_inj aSwap) U7 V7 2 1 (some 13) :=
  DecidedWithin.directCommit (S := slotsOf u7_inj aSwap) (by omega) (by decide) (by decide)

#print axioms u7_decidedWithin_slot0
#print axioms u7_decidedWithin_slot1_swap

/-! ## A total adaptive run, and agreement exercised

`demotePolicy` is genuinely adaptive at epoch length `1`: a slot whose
verdict two slots below was a skip is handed to validator `1`. On `U7`
slot `2` is vacuously skipped — its round lies beyond the universe — so
the policy moves slot `4` off the base rotation: `assign 4 = 1`. The
run is total (every slot above the frontier skips vacuously, inside its
window), a second run over the trimmed view `V7small` holds the same
verdicts, and `adaptive_decided_agree` is exercised on the pair. -/

/-- Every `U7` block sits at round `5` or below: slots past the frontier
have no candidates. -/
theorem u7_round_le : ∀ L : Fin 24, (U7.block L).round ≤ 5 := by decide

/-- Demote-on-skip at epoch length `1`: slot `k`'s leader consults the
verdict of slot `k − 2` and nothing else. -/
def demotePolicy : AdaptivePolicy (Fin 4) (Fin 24) Unit where
  W := 1
  W_pos := Nat.one_pos
  inj := u7_inj
  pick := fun _ v k => if k < 2 then 0 else if v (k - 2) = none then 1 else 0
  adapted := by
    intro U v w k hvw
    by_cases h2 : k < 2
    · simp only [if_pos h2]
    · have hj : v (k - 2) = w (k - 2) := hvw (k - 2) (by simp only [epochOf]; omega)
      simp only [if_neg h2, hj]
  base_prefix := by
    intro U v k hk
    have h2 : k < 2 := by simpa [epochOf] using hk
    simp only [if_pos h2]
    rfl

/-- The verdicts of `U7` under the adaptive schedule: the two decided
slots, then vacuous skips above the frontier. -/
def vd7 : ℕ → Option (Fin 24) :=
  fun k => if k = 0 then some 0 else if k = 1 then some 12 else none

/-- The adaptive run over the full view. -/
def run7 : AdaptiveRun demotePolicy U7 V7 where
  assign := fun k => demotePolicy.pick U7 vd7 k
  vdct := vd7
  closed := by
    intro k
    match k with
    | 0 =>
        have hB : demotePolicy.W * (epochOf demotePolicy.W 0 + 2) = 2 := rfl
        rw [hB]
        exact decidedWithin_congr (fun m hm => by interval_cases m <;> rfl)
          u7_decidedWithin_slot0
    | 1 =>
        have hB : demotePolicy.W * (epochOf demotePolicy.W 1 + 2) = 3 := rfl
        rw [hB]
        exact decidedWithin_congr (fun m hm => by interval_cases m <;> rfl)
          (u7_decidedWithin_slot1.mono (by omega))
    | (k + 2) =>
        refine DecidedWithin.directSkip
          (S := slotsOf demotePolicy.inj (fun k => demotePolicy.pick U7 vd7 k))
          ?_ (fun L hL => ?_)
        · have hW : demotePolicy.W = 1 := rfl
          simp only [hW, epochOf, Nat.div_one, Nat.one_mul]
          omega
        · have hr : (U7.block L).round = 3 * ((k + 2) / 1) := hL.2.1
          have h5 := u7_round_le L
          omega
  coherent := fun _ => rfl

/-- The same run over the trimmed view `V7small`. -/
def run7small : AdaptiveRun demotePolicy U7 V7small where
  assign := fun k => demotePolicy.pick U7 vd7 k
  vdct := vd7
  closed := by
    intro k
    match k with
    | 0 =>
        have hB : demotePolicy.W * (epochOf demotePolicy.W 0 + 2) = 2 := rfl
        rw [hB]
        exact decidedWithin_congr (fun m hm => by interval_cases m <;> rfl)
          (DecidedWithin.indirectCommit (S := slotsOf u7_inj aBase)
            (j := 1) (A := 12) (by omega) (by omega) (by decide)
            (DecidedWithin.directCommit (S := slotsOf u7_inj aBase)
              (by omega) (by decide) (by decide))
            (fun _ h1 h2 _ => absurd h2 (by omega))
            (by decide)
            ⟨8, by decide, Reaches.single (by decide)⟩)
    | 1 =>
        have hB : demotePolicy.W * (epochOf demotePolicy.W 1 + 2) = 3 := rfl
        rw [hB]
        exact decidedWithin_congr (fun m hm => by interval_cases m <;> rfl)
          ((DecidedWithin.directCommit (S := slotsOf u7_inj aBase) (B := 2)
            (by omega) (by decide) (by decide)).mono (by omega))
    | (k + 2) =>
        refine DecidedWithin.directSkip
          (S := slotsOf demotePolicy.inj (fun k => demotePolicy.pick U7 vd7 k))
          ?_ (fun L hL => ?_)
        · have hW : demotePolicy.W = 1 := rfl
          simp only [hW, epochOf, Nat.div_one, Nat.one_mul]
          omega
        · have hr : (U7.block L).round = 3 * ((k + 2) / 1) := hL.2.1
          have h5 := u7_round_le L
          omega
  coherent := fun _ => rfl

-- **The policy genuinely adapts**: slot 2's vacuous skip moves slot 4's
-- leader off the base rotation.
example : run7.assign 4 = 1 := rfl
example : run7.assign 3 = 0 := rfl

-- **Safety exercised**: the two views' runs agree, verdicts and schedule.
example : ∀ k, run7.vdct k = run7small.vdct k :=
  fun k => adaptive_decided_agree run7 run7small k
example : ∀ m, run7.assign m = run7small.assign m :=
  (adaptiveRun_agree run7 run7small).2

#print axioms LeanDag.adaptiveRun_agree
#print axioms LeanDag.AdaptivePolicy.const_run_decided
#print axioms run7

end LeanDagTest
