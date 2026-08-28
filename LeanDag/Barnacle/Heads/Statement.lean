import LeanDag.Barnacle.Model.Heads

/-!
# BN9 — the heads descent

The base protocol's liveness clause, `LiveOn`, discharged for the
paper's own schedule at every leader count (`barnacle.md` §8):
from the descent laws of a rule and a run of correct-led heads, a
schedule is live with the run's gap; and round-robin has such runs by
pigeonhole whenever the committee bound `waveLength · slack + 1 ≤ n`
holds — which for Mysticeti is `3f + 1 ≤ n`, its own.

* **BN9a, the stretch descent** — a stretch of consecutive decided slots
  with a committed top decides everything a wave below the top.
* **BN9b, heads decide** — `waveLength` consecutive good-led heads decide
  every slot up to a wave below the first and commit it.
* **BN9c, live from heads** — a run of heads with gap `c₀` makes every
  count's schedule live with gap `c₀`.
* **BN9d, round-robin has runs of heads** — the pigeonhole.
* **BN9e, round-robin is live** — at every count, with gap
  `n + waveLength − 1`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Heads

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **BN9a, the stretch descent**: from `indirect` alone. -/
def StretchDescent (R : LiveRule Validator BlockId Payload) (slack : ℕ) : Prop :=
  R.Descent slack →
  -- Any schedule, any view;
  ∀ (S : Slots Validator) (U : R.Universe) (V : R.View U) (b top : ℕ),
    -- a stretch of slots `[b, top]` whose top lies a full wave above every
    -- slot below `b` …
    (∀ i, i < b → S.slotRound i + R.waveLength ≤ S.slotRound top) →
    -- … every slot of which is decided …
    (∀ j, b ≤ j → j ≤ top → ∃ v, R.Decided S V j v) →
    -- … and whose top is committed …
    (∃ B, R.Decided S V top (some B)) →
    -- … decides every slot below `b`.
    ∀ i, i < b → ∃ v, R.Decided S V i v

/-- **BN9b, heads decide**: under `Sched m`, `waveLength` consecutive
good-led heads from round `ρ` decide every slot at a round in
`[ρ − waveLength, ρ)` and commit the head of `ρ`. -/
def HeadsDecide (R : LiveRule Validator BlockId Payload) (slack : ℕ)
    (getLeader : ℕ → Validator) {w : ℕ} (hk : Keyed getLeader w) : Prop :=
  R.Descent slack → 0 < R.waveLength →
  ∀ (U : R.Universe) (Rnd N : ℕ) (T : Finset Validator),
    -- Given what `goodLeaders` gives for `T` on `U` from `Rnd` to `N`,
    (∀ (S : Slots Validator) (κ : ℕ), Rnd ≤ S.slotRound κ → S.slotRound κ + R.waveLength ≤ N →
      S.leader κ ∈ T → ∃ L, R.Decided S (R.full U) κ (some L)) →
    -- for every count `m` and every round `ρ` from `Rnd` whose `waveLength`
    -- heads have their waves under `N` …
    ∀ (m : ℕ) (hm : 0 < m) (hmax : m ≤ w) (ρ : ℕ), Rnd ≤ ρ →
      ρ + R.waveLength + R.waveLength ≤ N + 1 →
      -- … if the heads of rounds `ρ, …, ρ + waveLength − 1` are `T`-led …
      (∀ i, i < R.waveLength → getLeader (ρ + i) ∈ T) →
      -- … then every slot at a round below `ρ` and at most a wave below it
      -- is decided on the full view …
      (∀ κ, (Sched getLeader hk m hm hmax).slotRound κ < ρ →
        ρ ≤ (Sched getLeader hk m hm hmax).slotRound κ + R.waveLength →
        ∃ v, R.Decided (Sched getLeader hk m hm hmax) (R.full U) κ v) ∧
      -- … and the head of `ρ`, slot `m · ρ`, is committed.
      ∃ L, R.Decided (Sched getLeader hk m hm hmax) (R.full U) (m * ρ) (some L)

/-- **BN9c, live from heads**: a run of good-led heads with gap `c₀`, for
the good set of every good DAG, makes every count's schedule live with
gap `c₀`. -/
def LiveOnOfHeads (R : LiveRule Validator BlockId Payload) (slack : ℕ)
    (getLeader : ℕ → Validator) {w : ℕ} (hk : Keyed getLeader w) (c₀ : ℕ) : Prop :=
  R.Descent slack → 0 < R.waveLength →
  -- If every set missing at most `slack` validators has a run of heads …
  (∀ T : Finset Validator, Fintype.card Validator ≤ T.card + slack →
    HeadsRun getLeader T R.waveLength c₀) →
  -- … then every count's schedule is live with gap `c₀`.
  ∀ (m : ℕ) (hm : 0 < m) (hmax : m ≤ w), R.LiveOn (Sched getLeader hk m hm hmax) c₀

/-- **BN9d, round-robin has runs of heads**: on `n` validators, for every
set missing at most `slack`, when `g · slack + 1 ≤ n` — within
`n + g − 1` rounds. -/
def RoundRobinHeads : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (T : Finset (Fin n)) (slack g : ℕ),
    n ≤ T.card + slack → g * slack + 1 ≤ n →
    HeadsRun (roundRobin n hn) T g (n + g - 1)

/-- **BN9e, round-robin is live**: a live rule with descent laws at
`slack`, on `n ≥ waveLength · slack + 1` validators, is live under
round-robin at every count, with gap `n + waveLength − 1`. -/
def LiveOnRoundRobin : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (BlockId Payload : Type) [DecidableEq BlockId]
    (R : LiveRule (Fin n) BlockId Payload) (slack : ℕ), R.Descent slack →
    0 < R.waveLength → R.waveLength * slack + 1 ≤ n →
    ∀ (w : ℕ) (hk : Keyed (roundRobin n hn) w) (m : ℕ) (hm : 0 < m) (hmax : m ≤ w),
      R.LiveOn (Sched (roundRobin n hn) hk m hm hmax) (n + R.waveLength - 1)

/-- The heads descent, for every live rule with descent laws, every keyed
leader function, and round-robin on every committee. -/
def Statement : Prop :=
  (∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : LiveRule Validator BlockId Payload) (slack : ℕ)
    (getLeader : ℕ → Validator) (w : ℕ) (hk : Keyed getLeader w) (c₀ : ℕ),
    StretchDescent R slack ∧ HeadsDecide R slack getLeader hk ∧
      LiveOnOfHeads R slack getLeader hk c₀) ∧
  RoundRobinHeads ∧ LiveOnRoundRobin

end Heads

end Barnacle

end LeanDag
