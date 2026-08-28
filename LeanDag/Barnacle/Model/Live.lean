import LeanDag.Barnacle.Model.Run

/-!
# Barnacle: the liveness interface

The liveness half of the paper's A4 (`barnacle.md` §7): for a fixed
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
with `c` rounds and a wave under the horizon is decided on the full
view, and from every round a committed slot lies within `c` rounds. The
gap `c` is what lets the leader-count mechanism find each
configuration's anchor before the horizon, and it is also the margin a
slot needs above it to be decided: a slot the direct rule does not
settle is decided by a committed anchor at least a wave above it, whose
own wave must fit under the horizon, so no rule decides every slot up to
`N − waveLength` (`barnacle.md` §11, F9). A schedule's own
liveness theorem supplies `c`.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

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
  ∀ (U : R.Universe) (V : R.View U) (Rnd N : ℕ), R.Good U Rnd N → R.toBaseRule.CoversUpto U V N →
    -- … every slot at a round from `Rnd`, with `c` rounds and a wave still
    -- under the horizon, is decided on any view caught up to `N` …
    (∀ κ, Rnd ≤ S.slotRound κ → S.slotRound κ + c + R.waveLength ≤ N →
      ∃ v, R.Decided S V κ v) ∧
    -- … and from every round `r` at or after `Rnd`, with `c` rounds and a
    -- wave still under the horizon, some slot at a round in `[r, r + c]`
    -- is committed on the full view.
    (∀ r, Rnd ≤ r → r + c + R.waveLength ≤ N →
      ∃ κ, r ≤ S.slotRound κ ∧ S.slotRound κ ≤ r + c ∧
        ∃ L, R.Decided S V κ (some L))

/-- An update rule keeps the count in `[1, maxLeaders]`, whatever it is
given — what extending a run needs of it; BN7a for the AIMD rule. -/
def UpdBounded {R : BaseRule Validator BlockId Payload} (P : Params) (upd : UpdateRule R) :
    Prop :=
  ∀ m b U V A, 0 < (upd m b U V A).1 ∧ (upd m b U V A).1 ≤ P.maxLeaders

/-- **What a good DAG delivers.** On a DAG good from `Rnd` to `N` there
is a set `T` of validators, all but at most `slack`, whose blocks are
*reached* by everything two rounds above them: a `T`-authored block at a
round from `Rnd`, with its own next round under the horizon, lies in the
causal history of every block two rounds up — whoever authored that
block.

This is the base protocol's coverage read as delivery, and it is what
turns a committed anchor into a delivered block. It is the second law a
live rule carries, beside `Descent`: `Descent` says a good leader's slot
commits, this says a good author's block is carried by whatever commits
above it. Both are facts of the base protocol, and neither mentions the
mechanism. -/
structure LiveRule.Delivers (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop where
  /-- A good author's block is in the history of every block two rounds
  above it. -/
  reaches : ∀ (U : R.Universe) (Rnd N : ℕ), R.Good U Rnd N →
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      ∀ b ∈ R.ids U, (R.block U b).creator ∈ T → Rnd ≤ (R.block U b).round →
        (R.block U b).round + 1 ≤ N →
        ∀ c ∈ R.ids U, (R.block U b).round + 2 ≤ (R.block U c).round →
          b ∈ historyFrom (R.block U) c

/-- The horizon a run of height `K` needs from a synchrony round at
genesis: each configuration's anchor lies within `interval + 1 + c`
rounds of the previous start, and the last range needs the gap and one
wave above it to be decided. -/
def horizon (P : Params) (R : LiveRule Validator BlockId Payload) (c K : ℕ) : ℕ :=
  K * (P.interval + 1 + c) + c + R.waveLength

end Barnacle

end LeanDag
