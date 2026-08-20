import LeanDag.MahiMahi.Model.Good

/-!
# Mahi-Mahi — the unpredictable-leader clause

The hypothesis under which the rule is live with no network assumption
(`mahi-mahi.md` §5). In words: *in every stretch of `c` consecutive
waves, the schedule names a validator whose block the DAG actually
committed.* It relates the schedule to the DAG — the single change from
the core's `FairScheduleOn`, whose target set is fixed — because under
asynchrony nothing about a validator guarantees that its block commits;
only the DAG's shape does. It says nothing about how the leader is
chosen: a coin revealed after the wave makes it true with probability
one, and any mechanism with the same effect qualifies.

**The horizon.** `U.ids` is a `Finset`, so `good` is empty past some
round and no finite DAG satisfies an unbounded `∀ k`. Both forms
therefore quantify only over windows whose decision rounds lie below a
horizon `N`. The window `c` is a free parameter; its probabilistic
reading is that `c` consecutive misses have probability `(1 − p)^c`,
with `p` the bound the counting lemma gives.

**Two forms.** The single-hit form yields recurring commits. A commit
does not decide every slot below it — a slot is decided through its
lowest eligible slot, and an undecided one there blocks it — so deciding
every slot needs a *run* of consecutive committed slots spanning
eligibility, as the core's `FairRunOn` and `SpansEligible` arrange under
synchrony. The run form is that clause with the target set replaced by
`good`.

**Definitions only**, as in the other model files.
-/

namespace LeanDag

namespace MahiMahi

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **Two universes agree up to round `d`**: the same ids at rounds `≤ d`,
denoting the same blocks. What the measurability result MM2′ consumes —
whatever decides `good` at a wave is fixed by the rounds up to its
decision round, which is the round at which a deployment reveals the
leader. -/
structure AgreeUpto (U₁ U₂ : BlockUniverse Validator BlockId Payload) (d : ℕ) : Prop where
  /-- The ids at rounds `≤ d` coincide. -/
  ids : ∀ i, (i ∈ U₁.ids ∧ (U₁.block i).round ≤ d) ↔ (i ∈ U₂.ids ∧ (U₂.block i).round ≤ d)
  /-- And they denote the same blocks. -/
  block : ∀ i ∈ U₁.ids, (U₁.block i).round ≤ d → U₁.block i = U₂.block i

section Slots

variable [S : Slots Validator]

/-- **The single-hit form.** In every window of `c` slots whose decision
rounds lie below the horizon `N`, the schedule names a committed
candidate at least once. -/
def UnpredictableWithin (U : BlockUniverse Validator BlockId Payload)
    (w c N : ℕ) : Prop :=
  ∀ k,
    -- the window's last decision round lies below the horizon
    decisionRound Validator w (k + c) ≤ N →
    -- some slot of the window is led by a validator whose block commits
    ∃ k', k ≤ k' ∧ k' < k + c ∧ S.leader k' ∈ good U w k'

/-- **The run form.** In every window of `c` slots below the horizon, a
run of `d` consecutive slots whose leaders are all committed candidates.
The bound reads the last slot of the latest possible run, `k + c + d − 1`,
so that small universes are not vacuously covered. -/
def UnpredictableRunWithin (U : BlockUniverse Validator BlockId Payload)
    (w c d N : ℕ) : Prop :=
  ∀ k,
    -- the latest run's last decision round lies below the horizon
    decisionRound Validator w (k + c + d - 1) ≤ N →
    -- some run of d slots starting in the window is led by committed candidates
    ∃ k', k ≤ k' ∧ k' < k + c ∧ ∀ i < d, S.leader (k' + i) ∈ good U w (k' + i)

variable (Validator) in
/-- **A run of `c` slots spans eligibility**: every slot below its start
is eligible for its last slot. The core's `SpansEligible` at wave `w`;
at one leader per round it holds for `c = w`. -/
def SpansEligible (w c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator w i (b + c - 1)

end Slots

end MahiMahi

end LeanDag
