import LeanDag.HammerheadTwo.Model.Live

/-!
# Hammerhead 2.0: the descent laws and runs of heads

What the liveness clause of a base protocol rests on, under multiple
leaders per round (`hammerhead-two.md` §8). The development's own
liveness route — a run of consecutive correct-led slots spanning a wave
(`FairRunOn`) — has no instance under the paper's rotation
`GetLeader(r + l)` at two or more leaders and four validators: three
consecutive rounds name every validator. What does exist is a run of
correct-led *heads*, first slots of consecutive rounds, and a head
committed a wave above a slot decides it with no eligible slot between.

Two facts of the base protocol carry the argument, stated here as a
second law structure, `Descent`, over a live rule: on a good DAG the
slots led by a set of validators missing at most `slack` commit
directly, whatever the schedule (the paper's A4, "an honest leader's
slot is decided directly after GST"); and the indirect rule — the
nearest committed slot a full wave above a slot decides it (A3). The
eligibility gap of every rule of this development is its wave length,
so no separate gap is stated.

`HeadsRun` is the schedule clause: `g` consecutive `T`-led round heads
within `c₀` rounds of any round. Under `Sched m` the head of round `ρ`
is slot `m · ρ`, led by `getLeader ρ` whatever the count, so one clause
serves every configuration; round-robin satisfies it by pigeonhole
(`Heads/Statement.lean`).

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace HammerheadTwo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **The descent laws** of a live rule, with `slack` the number of
validators the good set may miss. -/
structure LiveRule.Descent (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop where
  /-- **A4, direct commits.** On a DAG good from `Rnd` to `N` there is a
  set `T` of validators, all but at most `slack`, such that on any
  schedule a `T`-led slot at a round from `Rnd` whose wave fits under
  `N` is committed on the full view. -/
  goodLeaders : ∀ (U : R.Universe) (Rnd N : ℕ), R.Good U Rnd N →
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      ∀ (S : Slots Validator) (κ : ℕ), Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
        S.leader κ ∈ T → ∃ L, R.Decided S (R.full U) κ (some L)
  /-- **A3, the indirect rule.** If slot `j`, a full wave above slot `i`,
  is committed on `V`, and every slot strictly between them that is a
  full wave above `i` is skipped on `V`, then `i` is decided on `V`. -/
  indirect : ∀ (S : Slots Validator) {U : R.Universe} (V : R.View U) (i j : ℕ) (A : BlockId),
    S.slotRound i + R.waveLength ≤ S.slotRound j → R.Decided S V j (some A) →
    (∀ i', i < i' → i' < j → S.slotRound i + R.waveLength ≤ S.slotRound i' →
      R.Decided S V i' none) →
    ∃ v, R.Decided S V i v

/-- **A run of heads**: from every round `r`, within `c₀` rounds, `g`
consecutive rounds whose heads — first slots, led by `getLeader` of the
round — are led by members of `T`. -/
def HeadsRun (getLeader : ℕ → Validator) (T : Finset Validator) (g c₀ : ℕ) : Prop :=
  ∀ r, ∃ ρ, r ≤ ρ ∧ ρ + g ≤ r + c₀ ∧ ∀ i, i < g → getLeader (ρ + i) ∈ T

end HammerheadTwo

end LeanDag
