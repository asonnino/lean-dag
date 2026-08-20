import LeanDag.WaveRobin
import LeanDag.Network.Quorum

/-!
# The wave-aligned rotation — the witnesses

`WaveRobin.lean` proves fairness at every `n`; this file pins the wave shape
down where `decide` can see it, on the standard four-validator committee, and
assembles the payoff: L10 with **every schedule hypothesis discharged by a
theorem**, at every committee size. Compare `Pipelined.lean`, whose
`pipe_fairRun` proves the same pair of hypotheses for per-slot rotation but
only over `Fin 4` — the wave-aligned schedule is what frees the composition
of the committee.

`waveRobin` is a `def`, not an instance, so nothing here collides with the
schedules of the other witness files; every use names it explicitly.
-/

namespace LeanDagTest

open LeanDag

-- Axiom audit for the wave-aligned schedule results.
#print axioms LeanDag.waveRobin_fairRun
#print axioms LeanDag.waveRobin_spansEligible
#print axioms LeanDag.waveRobin_fairSchedule

/-! ## The wave shape

Pipelined rounds, and the leader holds for three consecutive slots: slots
`0`–`2` are validator `0`'s wave, `3`–`5` validator `1`'s, and slot `12`
wraps the four-validator rotation back to `0`. -/

example : (waveRobin 4 (by omega)).slotRound 0 = 0 := by decide
example : (waveRobin 4 (by omega)).slotRound 7 = 7 := by decide

example : (waveRobin 4 (by omega)).leader 0 = 0 := by decide
example : (waveRobin 4 (by omega)).leader 2 = 0 := by decide
example : (waveRobin 4 (by omega)).leader 3 = 1 := by decide
example : (waveRobin 4 (by omega)).leader 5 = 1 := by decide
example : (waveRobin 4 (by omega)).leader 11 = 3 := by decide
example : (waveRobin 4 (by omega)).leader 12 = 0 := by decide

section

/-- The standard witness fault configuration: validator `0` Byzantine,
`f = 1` — the instance `Model.lean` and `Growth.lean` also use, local to
this section so it leaks nowhere. -/
local instance waveFaults : Faults (Fin 4) where
  f := 1
  byzantine := {0}
  card_validators := by decide
  card_byzantine := by decide

example : (Correct : Finset (Fin 4)) = {1, 2, 3} := by decide

/-! Validator `1`'s wave — slots `3`, `4`, `5` — is a correct 3-run, which is
the run the fairness proof locates (its witness for `k = 0` is slot
`3 * (1 + 4·0) = 3`). -/

example : (waveRobin 4 (by omega)).leader 3 ∈ (Correct : Finset (Fin 4)) := by decide
example : (waveRobin 4 (by omega)).leader 4 ∈ (Correct : Finset (Fin 4)) := by decide
example : (waveRobin 4 (by omega)).leader 5 ∈ (Correct : Finset (Fin 4)) := by decide

/-- The general theorem, landing on the concrete committee. -/
example : FairRunOn (S := waveRobin 4 (by omega)) (Correct : Finset (Fin 4)) 3 :=
  waveRobin_fairRun 4 (by omega)

end

/-! ## The grounded composition -/

/-- **L10 with no schedule hypothesis left** — at every committee size and
every fault configuration. Both of L10's schedule premises are discharged by
the wave-aligned theorems; what remains are hypotheses about the DAG and the
network — population, synchrony, and the horizon — which is the intended
division of labour. Contrast the corresponding example in `Pipelined.lean`,
which is pinned to `Fin 4` and *assumes* its committee correct. -/
example {BlockId : Type} [DecidableEq BlockId] {Payload : Type}
    (n : ℕ) (hn : 0 < n) [F : Faults (Fin n)] (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ (waveRobin n hn).slotRound b ∧
      ∀ (U : BlockUniverse (Fin n) BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → Populated U r) → Synchronised U R →
        (waveRobin n hn).slotRound (b + 3 - 1) + 2 ≤ N →
        ∀ i, i < b → ∃ v, Decided (S := waveRobin n hn) U (View.full U) i v :=
  all_decided_below_of_fairRun_correct (S := waveRobin n hn) (by omega)
    (waveRobin_spansEligible n hn) (waveRobin_fairRun n hn) R k

end LeanDagTest
