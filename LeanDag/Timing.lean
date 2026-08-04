import LeanDag.Liveness

/-!
# Timing — `Synchronised` earned from GST and backoff

`liveness.md` §8 Q1. The layer beneath `Delivery`.

Everything above this file takes `SynchronisedOn U T R` as an **assumption**,
and Q1 records the worry: a correct validator waits on a timeout and builds on
whatever arrived, unable to tell correct peers from Byzantine ones. Nothing so
far shows a timeout actually achieves coverage, so every theorem after L3 could
in principle rest on something false.

This file discharges that, from the standard partial-synchrony assumption:

```
GST + Δ delivery  ──▶  SynchronisedOn U T R  ──L4/L6──▶  commits
   (this file)              (assumed before)
```

**The argument, in one line.** A validator waits a full timeout before
building. Once the timeout exceeds `drift + delay`, everything a `T`-peer
built one round below has arrived, so it is referenced. The backoff drives the
timeout past that threshold because it never stops growing, and after GST the
threshold is finite.

**Byzantine behaviour does not appear.** An earlier sketch of this argument
split on whether Byzantine validators participate. That case analysis is not
needed and would not have worked — a Byzantine *leader* can publish and reveal
selectively, leaving its slot undecided no matter how long anyone waits. The
argument here quantifies only over `T`, and the adversary is simply absent
from it.

**The obligation this creates on an implementation.** `waits` says a validator
builds a *full timeout* after entering the round — **not** as soon as it holds
`2f+1` blocks. That distinction is load bearing: an adversary answering
instantly can fill an early quorum with Byzantine blocks and crowd out the
correct ones, including the leader's. Building on the first `2f+1` would make
the backoff accomplish nothing.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {D R N : ℕ}

/-- When each validator built each of its blocks, and what the network
guarantees about delivery.

`gst`, `delay` and `timeout` are fields rather than parameters because they
belong to the execution, not to the statement. -/
structure Timing (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) where
  /-- `v`'s round-`n` block. -/
  blk : Validator → ℕ → BlockId
  /-- The time at which `v` built it. -/
  built : Validator → ℕ → ℕ
  /-- The timeout in force at round `n`, common to `T`. -/
  timeout : ℕ → ℕ
  /-- Global stabilisation time. -/
  gst : ℕ
  /-- The post-GST delivery bound — Δ. -/
  delay : ℕ
  /-- The universe stops at the horizon. Without this the structure would be
  **unsatisfiable**, exactly as the first `Live` was: `blk` at every round
  would force infinitely many distinct blocks into the `Finset` `U.ids`
  (`liveness.md` §4.4). -/
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  blk_mem : ∀ v ∈ T, ∀ n ≤ N, blk v n ∈ U.ids
  blk_creator : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).creator = v
  blk_round : ∀ v ∈ T, ∀ n ≤ N, (U.block (blk v n)).round = n
  /-- **The waiting rule** (protocol). `v` builds round `n+1` a full timeout
  after entering round `n` — not as soon as it holds a quorum. -/
  waits : ∀ v ∈ T, ∀ n < N, built v n + timeout n ≤ built v (n + 1)
  /-- Timeouts are positive, so time advances with rounds. -/
  timeout_pos : ∀ n, 1 ≤ timeout n
  /-- **Delivery** (network). After GST, a `T`-block built at time `t` is in
  every `T`-validator's hands by `t + delay`; and a validator references
  everything it holds. This is GST, and it is where the chain bottoms out. -/
  covers : ∀ v ∈ T, ∀ w ∈ T, ∀ n < N, gst ≤ built w n →
    built w n + delay ≤ built v (n + 1) →
    blk w n ∈ (U.block (blk v (n + 1))).refs

namespace Timing

variable (tm : Timing U T N)

/-- `T`-validators are never more than `D` apart in real time at the same
round.

**The one thing this file assumes rather than derives.** It is bounded, not
growing: given `covers` and a rule that a validator builds once the timeout
has elapsed *and* the round below has arrived, drift is non-increasing while
`delay ≤ timeout`. Deriving that needs an upper bound on `built` — a
`prompt` field — and a max over `T`. Recorded in `liveness.md` §8 Q1 as the
remaining step. -/
def Drift (D : ℕ) : Prop :=
  ∀ v ∈ T, ∀ w ∈ T, ∀ n ≤ N, tm.built w n ≤ tm.built v n + D

variable {tm}

omit [DecidableEq BlockId] in
/-- Rounds advance real time, so any round past `gst` was built past `gst`.
This is what stops `gst` needing its own assumption. -/
theorem le_built {v : Validator} (hv : v ∈ T) : ∀ n ≤ N, n ≤ tm.built v n := by
  intro n
  induction n with
  | zero => intro _; omega
  | succ n ih =>
      intro hn
      have hw := tm.waits v hv n (by omega)
      have := tm.timeout_pos n
      have := ih (by omega)
      omega

omit [DecidableEq BlockId] in
/-- **Q1, discharged.** Once the timeout exceeds `drift + delay` and the
rounds are past GST, coverage among `T` holds — `SynchronisedOn` becomes a
theorem.

The chain is four inequalities:
`built w n ≤ built v n + D` (drift), `D + delay ≤ timeout n` (backoff),
`built v n + timeout n ≤ built v (n+1)` (waiting), hence
`built w n + delay ≤ built v (n+1)`, which is exactly what `covers` wants.

Non-equivocation does the remaining work: `SynchronisedOn` quantifies over
*every* `T`-authored block, and T1 identifies each with the `blk` this
structure names. That is why `T ⊆ Correct` is needed here — a Byzantine
author could have several blocks in a round and `blk` would name only one. -/
theorem synchronisedOn_of_timing (hT : T ⊆ (Correct : Finset Validator))
    (hD : tm.Drift D) (hgst : tm.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + tm.delay ≤ tm.timeout n) :
    SynchronisedOn U T R := by
  intro n hn b hb hbr hbc a ha har hac
  -- the horizon bounds the round, so `blk` is defined where it is used
  have hN : n + 1 ≤ N := hbr ▸ tm.rounds_le b hb
  -- name the two blocks through `blk`, using non-equivocation
  have hbv : b = tm.blk ((U.block b).creator) (n + 1) :=
    U.eq_of_creator_eq hb (tm.blk_mem _ hbc _ hN) (hT hbc) rfl
      (tm.blk_creator _ hbc _ hN) (by rw [hbr, tm.blk_round _ hbc _ hN])
  have haw : a = tm.blk ((U.block a).creator) n :=
    U.eq_of_creator_eq ha (tm.blk_mem _ hac _ (by omega)) (hT hac) rfl
      (tm.blk_creator _ hac _ (by omega)) (by rw [har, tm.blk_round _ hac _ (by omega)])
  rw [hbv, haw]
  refine tm.covers _ hbc _ hac n (by omega) ?_ ?_
  · exact le_trans (le_trans hgst hn) (le_built hac n (by omega))
  · have hdrift := hD _ hbc _ hac n (by omega)
    have hwait := tm.waits _ hbc n (by omega)
    have hto := hbackoff n hn
    omega

end Timing

/-! ## Backoff convergence

The remaining question is why the timeout ever exceeds `D + delay`. It does
because the backoff never stops growing, and that is the *only* property of
the backoff schedule the argument uses — not its shape, not its rate, and not
the signal that drives it.

Which is worth stating plainly: §4.3 describes a backoff driven by observing
that commits have stalled, i.e. by liveness failure. Nothing here depends on
that mechanism being the one in force. Any schedule that grows without bound
works, so an implementation is free to choose how it grows. What it is **not**
free to do is cap the timeout — a capped backoff satisfies neither hypothesis
below, and the system it describes can be permanently stuck.
-/

/-- A backoff that grows without bound eventually clears any fixed
threshold. -/
theorem exists_backoff_ge {timeout : ℕ → ℕ} (hmono : Monotone timeout)
    (hub : ∀ m, ∃ n, m ≤ timeout n) (m : ℕ) :
    ∃ R, ∀ n, R ≤ n → m ≤ timeout n := by
  obtain ⟨R, hR⟩ := hub m
  exact ⟨R, fun n hn => le_trans hR (hmono hn)⟩

omit [DecidableEq BlockId] in
/-- **The headline.** Under GST with a bounded drift and an unbounded
backoff, `SynchronisedOn` holds from *some* round — no longer assumed.

Everything above this file consumes `SynchronisedOn` and is unchanged: L4 and
L6 still take it as a hypothesis, and this supplies it, exactly as
`synchronised_of_delivery` supplies it from `Delivery`. -/
theorem exists_synchronisedOn_of_backoff (tm : Timing U T N)
    (hT : T ⊆ (Correct : Finset Validator)) (hD : tm.Drift D)
    (hmono : Monotone tm.timeout) (hub : ∀ m, ∃ n, m ≤ tm.timeout n) :
    ∃ R, SynchronisedOn U T R := by
  obtain ⟨R₀, hR₀⟩ := exists_backoff_ge hmono hub (D + tm.delay)
  refine ⟨max R₀ tm.gst, Timing.synchronisedOn_of_timing hT hD (le_max_right _ _) ?_⟩
  exact fun n hn => hR₀ n (le_trans (le_max_left _ _) hn)

end LeanDag
