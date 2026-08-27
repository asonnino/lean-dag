import LeanDag.HammerheadTwo.Model.Run

/-!
# Hammerhead 2.0: the liveness interface

The liveness half of the paper's A4 (`hammerhead-two.md` §7): for a fixed
configuration, after the network stabilises, the base protocol decides
every slot and commits new leaders infinitely often. In this development
liveness is structural — a condition on the DAG, no clock — and every
statement carries a horizon, because a universe is finite and decides
nothing above its last rounds.

`LiveRule` extends the base-rule data with one field, `Good`: the rule's
own notion of a DAG that is good from a round `Rnd` to a horizon `N` —
for the rules of this development, synchronised over a reliable quorum
and populated. The mechanism never inspects it; it is the precondition
of `LiveOn`, the clause the liveness results consume, and each
instantiation defines it from its own predicates.

`LiveOn S c` is A4-liveness on one schedule: on a good DAG, every slot
whose wave fits under the horizon is decided on the full view, and from
every round a committed slot lies within `c` rounds. The gap `c` is what
lets the leader-count mechanism find each configuration's anchor before
the horizon; a schedule's own liveness theorem supplies it.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace HammerheadTwo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A base rule with a notion of a good DAG.** `Good U Rnd N`: the DAG
`U` is good from round `Rnd` to horizon `N` — what the base liveness
route asks of it, as the rule defines it. -/
structure LiveRule (Validator : Type) [Fintype Validator] [DecidableEq Validator]
    (BlockId : Type) [DecidableEq BlockId] (Payload : Type)
    extends BaseRule Validator BlockId Payload where
  /-- The DAG is good from round `Rnd` to horizon `N`. -/
  Good : Universe → ℕ → ℕ → Prop

/-- **A4, liveness, on one schedule with commit gap `c`.** -/
def LiveRule.LiveOn (R : LiveRule Validator BlockId Payload) (S : Slots Validator) (c : ℕ) :
    Prop :=
  -- On every DAG good from `Rnd` to `N` …
  ∀ (U : R.Universe) (Rnd N : ℕ), R.Good U Rnd N →
    -- … every slot at a round from `Rnd` whose wave fits under the horizon
    -- is decided on the full view …
    (∀ κ, Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
      ∃ v, R.Decided S (R.full U) κ v) ∧
    -- … and from every round `r` at or after `Rnd`, with `c` rounds and a
    -- wave still under the horizon, some slot at a round in `[r, r + c]`
    -- is committed on the full view.
    (∀ r, Rnd ≤ r → r + c + R.waveLength ≤ N →
      ∃ κ, r ≤ S.slotRound κ ∧ S.slotRound κ ≤ r + c ∧
        ∃ L, R.Decided S (R.full U) κ (some L))

/-- An update rule keeps the count in `[1, maxLeaders]`, whatever it is
given — what extending a run needs of it; HH7a for the AIMD rule. -/
def UpdBounded {R : BaseRule Validator BlockId Payload} (P : Params) (upd : UpdateRule R) :
    Prop :=
  ∀ m b U A, 0 < (upd m b U A).1 ∧ (upd m b U A).1 ≤ P.maxLeaders

/-- The horizon a run of height `K` needs from a synchrony round at
genesis: each configuration's anchor lies within `interval + 1 + c`
rounds of the previous start, and the last range needs one wave to be
decided. -/
def horizon (P : Params) (R : LiveRule Validator BlockId Payload) (c K : ℕ) : ℕ :=
  K * (P.interval + 1 + c) + R.waveLength

end HammerheadTwo

end LeanDag
