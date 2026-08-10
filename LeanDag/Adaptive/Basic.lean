import LeanDag.Liveness

/-!
# Adaptive leaders: epochs and the bounded decision relation

The groundwork for the adaptive-leaders arc (`adaptive-leaders.md`): a
Hammerhead-style schedule recomputes the leaders ahead from the agreed
prefix, and the question is whether safety and liveness survive.

The base development's decision relation lets verdicts flow *downward* —
a slot is decided indirectly from an anchor arbitrarily far above it. An
adaptive schedule makes leader identity flow *upward* — the leaders of a
high slot depend on verdicts below. Composed without restriction, the
verdict of a slot may depend on the leader of its own anchor, whose
identity depends on that verdict, and nothing rules out two
self-justifying schedules. The stratification that forces the fixpoint
unique needs a decision relation that *carries a bound on its anchors in
the statement*: `Decided` is a `Prop`, so a derivation's anchors cannot
be inspected after the fact.

This file provides that relation and its two structural lemmas:

* `DecidedWithin B` — the four constructors of `Decided`, with every
  slot mentioned strictly below `B`;
* `DecidedWithin.toDecided` — forgetting the bound yields an ordinary
  derivation, so every safety theorem of the base development applies to
  bounded verdicts unchanged (agreement for the new relation *is* M6);
* `decidedWithin_congr` — the relation reads the schedule's `leader`
  only at slots below `B` (only `IsLeaderBlock` consults it; the
  round structure is fixed), so two assignments agreeing below `B`
  derive exactly the same bounded verdicts. This is what lets an
  epoch's verdicts be computed against a schedule only partially
  determined.

It also provides `slotsOf`, the `Slots` instance a leader assignment
induces over a fixed round structure. One leader per round —
`slotRound` injective — is assumed for the whole arc: it makes the
`keyed` clause a lemma, where under multi-leader rounds a reassignment
could collide two slots of one round onto one validator and the policy
would owe the distinctness clause itself.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The epoch of slot `k` at width `W`: epoch `e` is slots
`[W·e, W·(e+1))`. -/
def epochOf (W k : ℕ) : ℕ := k / W

theorem epochOf_lt_iff {W k e : ℕ} (hW : 0 < W) :
    epochOf W k < e ↔ k < W * e := by
  unfold epochOf
  rw [Nat.div_lt_iff_lt_mul hW, Nat.mul_comm]

theorem epochOf_mono (W : ℕ) {j k : ℕ} (h : j ≤ k) :
    epochOf W j ≤ epochOf W k :=
  Nat.div_le_div_right h

section Slots

variable [S : Slots Validator]

/-- The `Slots` instance a leader assignment induces: the base round
structure, the given leaders. `keyed` is where one-leader-per-round
enters: with `slotRound` injective, distinct slots differ in round
whatever the assignment names. -/
@[reducible] def slotsOf (hinj : Function.Injective S.slotRound) (a : ℕ → Validator) :
    Slots Validator where
  slotRound := S.slotRound
  leader := a
  mono := S.mono
  unbounded := S.unbounded
  keyed := fun _ _ h => hinj (congrArg Prod.fst h)

omit [Fintype Validator] [DecidableEq Validator] F in
@[simp] theorem slotsOf_slotRound (hinj : Function.Injective S.slotRound)
    (a : ℕ → Validator) (k : ℕ) : (slotsOf hinj a).slotRound k = S.slotRound k := rfl

omit [Fintype Validator] [DecidableEq Validator] F in
@[simp] theorem slotsOf_leader (hinj : Function.Injective S.slotRound)
    (a : ℕ → Validator) (k : ℕ) : (slotsOf hinj a).leader k = a k := rfl

omit [Fintype Validator] [DecidableEq Validator] F in
/-- The base schedule is its own induced instance — the anchor for
conservativity: a constant policy reassigns nothing. -/
theorem slotsOf_base (hinj : Function.Injective S.slotRound) :
    slotsOf hinj S.leader = S := by
  cases S; rfl

/-- **The bounded decision relation.** `Decided`, with every slot the
derivation mentions — the decided slot, the anchor, the eligible
intermediates — strictly below `B`.

The bound lives in the relation because it cannot live anywhere else: a
`Decided` derivation is a proof of a `Prop` and its anchors cannot be
recovered from it. The adaptive fixpoint is stratified by exactly this
bound — epoch `e`'s verdicts are `DecidedWithin` the start of epoch
`e + 2`, which consults leaders the schedule has already determined. -/
inductive DecidedWithin (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (B : ℕ) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      k < B → IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      DecidedWithin U V B k (some L)
  /-- The direct rule blames every candidate. -/
  | directSkip {k : ℕ} :
      k < B → (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      DecidedWithin U V B k none
  /-- Anchored on the nearest eligible committed slot below the bound. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      DecidedWithin U V B k (some L)
  /-- Anchored likewise, no candidate is in reach. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      DecidedWithin U V B k none

namespace DecidedWithin

variable {V : View Validator BlockId Payload U} {B B' k : ℕ} {v : Option BlockId}

/-- Forgetting the bound: every bounded derivation is a `Decided`
derivation, so the base safety development — M1–M6 in particular —
applies to bounded verdicts without restatement. -/
theorem toDecided (h : DecidedWithin U V B k v) : Decided U V k v := by
  induction h with
  | directCommit _ hL hdc => exact Decided.directCommit hL hdc
  | directSkip _ hall => exact Decided.directSkip hall
  | indirectCommit hkj _ helig _ _ hL hcert ihj ihmid =>
      exact Decided.indirectCommit hkj helig ihj ihmid hL hcert
  | indirectSkip hkj _ helig _ _ hnone ihj ihmid =>
      exact Decided.indirectSkip hkj helig ihj ihmid hnone

/-- The decided slot lies below the bound. -/
theorem lt_bound (h : DecidedWithin U V B k v) : k < B := by
  cases h with
  | directCommit hk _ _ => exact hk
  | directSkip hk _ => exact hk
  | indirectCommit hkj hj _ _ _ _ _ => omega
  | indirectSkip hkj hj _ _ _ _ => omega

/-- The bound relaxes upward. -/
theorem mono (h : DecidedWithin U V B k v) (hBB : B ≤ B') :
    DecidedWithin U V B' k v := by
  induction h with
  | directCommit hk hL hdc => exact directCommit (by omega) hL hdc
  | directSkip hk hall => exact directSkip (by omega) hall
  | indirectCommit hkj hj helig _ _ hL hcert ihj ihmid =>
      exact indirectCommit hkj (by omega) helig ihj (fun i h1 h2 h3 => ihmid i h1 h2 h3)
        hL hcert
  | indirectSkip hkj hj helig _ _ hnone ihj ihmid =>
      exact indirectSkip hkj (by omega) helig ihj (fun i h1 h2 h3 => ihmid i h1 h2 h3)
        hnone

/-- Two bounded verdicts agree — M6, through the embedding. -/
theorem agree {V₁ V₂ : View Validator BlockId Payload U} {B₁ B₂ k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : DecidedWithin U V₁ B₁ k v₁)
    (h₂ : DecidedWithin U V₂ B₂ k v₂) : v₁ = v₂ :=
  decided_agree h₁.toDecided h₂.toDecided

end DecidedWithin

omit [DecidableEq BlockId] in
/-- Only the leader clause of `IsLeaderBlock` consults the assignment,
at the slot itself. -/
theorem isLeaderBlock_slotsOf_congr {hinj : Function.Injective S.slotRound}
    {a₁ a₂ : ℕ → Validator} {k : ℕ} {L : BlockId} (hk : a₁ k = a₂ k)
    (h : IsLeaderBlock (S := slotsOf hinj a₁) U k L) :
    IsLeaderBlock (S := slotsOf hinj a₂) U k L := by
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, h2, by rw [slotsOf_leader, ← hk]; exact h3⟩

/-- **Congruence below the bound.** Only `IsLeaderBlock` consults the
assignment, and only at slots below `B`; the round structure — and with
it eligibility, decision rounds and every counting predicate — is the
base instance's. So two assignments agreeing below `B` derive the same
bounded verdicts, which is what permits judging an epoch against a
schedule only determined so far. -/
theorem decidedWithin_congr {hinj : Function.Injective S.slotRound}
    {a₁ a₂ : ℕ → Validator} {V : View Validator BlockId Payload U} {B k : ℕ}
    {v : Option BlockId} (ha : ∀ m, m < B → a₁ m = a₂ m)
    (h : DecidedWithin (S := slotsOf hinj a₁) U V B k v) :
    DecidedWithin (S := slotsOf hinj a₂) U V B k v := by
  induction h with
  | @directCommit k L hk hL hdc =>
      exact DecidedWithin.directCommit (S := slotsOf hinj a₂) hk
        (isLeaderBlock_slotsOf_congr (ha k hk) hL) hdc
  | @directSkip k hk hall =>
      exact DecidedWithin.directSkip (S := slotsOf hinj a₂) hk
        (fun L hL => hall L (isLeaderBlock_slotsOf_congr (ha k hk).symm hL))
  | @indirectCommit k j A L hkj hj helig _ _ hL hcert ihj ihmid =>
      exact DecidedWithin.indirectCommit (S := slotsOf hinj a₂) hkj hj helig ihj
        (fun i h1 h2 h3 => ihmid i h1 h2 h3)
        (isLeaderBlock_slotsOf_congr (ha k (by omega)) hL) hcert
  | @indirectSkip k j A hkj hj helig _ _ hnone ihj ihmid =>
      exact DecidedWithin.indirectSkip (S := slotsOf hinj a₂) hkj hj helig ihj
        (fun i h1 h2 h3 => ihmid i h1 h2 h3)
        (fun L hL => hnone L
          (isLeaderBlock_slotsOf_congr (ha k (by omega)).symm hL))

end Slots

end LeanDag
