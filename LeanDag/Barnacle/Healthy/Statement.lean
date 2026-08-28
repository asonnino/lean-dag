import LeanDag.Barnacle.Model.Window
import Mathlib.Order.Interval.Finset.Nat

/-!
# BN12 — a healthy window is read as healthy

Safety and liveness are unconditional in the leader count: BN3 holds for
every update rule and BN8 at whatever count the run reaches. That is the
right design, and it leaves one thing unsaid. Nothing so far stops the
measurement reading a window in which *every* scoring slot committed as
unhealthy, so nothing stops the AIMD rule driving the count to one and
holding it there for ever. The mechanism would be safe, live, and inert.

This file closes that. `WindowHealthy` says what a healthy window is —
every slot of every scoring round directly committed on the anchor's
history — and BN12 says the count then reaches `expected`, so the
threshold test passes and the rule increases.

**Which rounds can score.** A direct commit at round `r` rests on
evidence at round `r + waveLength − 1`, so the anchor at round `ra` can
carry it only when `r + waveLength − 1 ≤ ra`, that is `d ≥ waveLength −
1` for `r = ra − d`. The round at `d = waveLength − 1` has the anchor
itself as its only certifier in the window and never scores, so the
scoring rounds are `waveLength ≤ d ≤ interval` — `interval − waveLength
+ 1` of them, which is `expected` divided by the count. `expected` is
therefore exactly the count of a window in which every scoring slot
commits, and BN12 is that reading, proved.

**What this does not claim.** That a *good DAG* makes the window
healthy. That needs the anchor's history to carry the good validators'
blocks below it, which is a property of the base protocol and not of the
mechanism; it is the natural next result, and slots led by validators
outside the good set will not commit in any case, so the bound there is
partial rather than `expected`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Healthy

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **A healthy window**: every slot of every scoring round of the window
is directly committed on the anchor's causal history. -/
def WindowHealthy (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U)
    (m : ℕ) (hm : 0 < m) (hmax : m ≤ P.maxLeaders) : Prop :=
  ∀ d, R.waveLength ≤ d → d ≤ P.interval → ∀ l, l < m →
    R.SlotDirect (Sched getLeader hk m hm hmax) U (R.historyView U A hA)
      (m * ((R.block U A).round - d) + l)

/-- **BN12a, a healthy window reaches the expected count.** -/
def Counted (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) : Prop :=
  ∀ (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U) (m : ℕ) (hm : 0 < m)
    (hmax : m ≤ P.maxLeaders),
    R.waveLength ≤ P.interval → P.interval ≤ (R.block U A).round →
    WindowHealthy R P getLeader hk U A hA m hm hmax →
    expected R P m ≤ observed R P getLeader hk U A m hm hmax

/-- **BN12b, and the rule then increases.** At a threshold of at most one
— the paper's `num / den ≤ 1`, which every deployment satisfies — a
healthy window raises the count by one, capped at `maxLeaders`, and
resets the back-off. So the loop cannot read a window in which every
scoring slot committed as a reason to back off. -/
def Raises (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) : Prop :=
  ∀ (U : R.Universe) (A : BlockId) (hA : A ∈ R.ids U) (m : ℕ) (hm : 0 < m)
    (hmax : m ≤ P.maxLeaders) (backoff : ℕ) (V : R.View U),
    P.num ≤ P.den → R.waveLength ≤ P.interval → P.interval ≤ (R.block U A).round →
    WindowHealthy R P getLeader hk U A hA m hm hmax →
    Aimd.rule R P getLeader hk m backoff U V A = (min (m + 1) P.maxLeaders, 0)

/-- The count of a healthy window, and the step it produces. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders),
    Counted R P getLeader hk ∧ Raises R P getLeader hk

end Healthy

end Barnacle

end LeanDag
