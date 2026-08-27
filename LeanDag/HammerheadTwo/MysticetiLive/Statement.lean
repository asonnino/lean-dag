import LeanDag.HammerheadTwo.Model.Heads
import LeanDag.HammerheadTwo.Mysticeti.Statement
import LeanDag.Liveness

/-!
# Hammerhead 2.0 over Mysticeti — liveness

Mysticeti as a live rule, its descent laws, and the paper's A4 for
Mysticeti under its own schedule: round-robin is live at every leader
count (`hammerhead-two.md` §8, F3). `Good` is the base development's
own liveness interface — a reliable quorum over which the DAG is
synchronised from `Rnd` and populated to `N` (report §5) — and the
descent laws are `decided_of_leader_mem` (L4) and the two indirect
constructors of `Decided`. The slack is `f`, and the committee bound
the pigeonhole needs, `3f + 1 ≤ n`, is `Faults.card_validators`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace HammerheadTwo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **Mysticeti as a live rule.** A DAG is good from `Rnd` to `N` when
some quorum of correct validators is synchronised from `Rnd` and
populates every round from `Rnd` to `N`. -/
def mysticetiLive [Faults Validator] : LiveRule Validator BlockId Payload :=
  { mysticeti with
    Good := fun U Rnd N => ∃ T ⊆ (Correct : Finset Validator),
      quorumCard Validator ≤ T.card ∧ SynchronisedOn U T Rnd ∧
      ∀ r, Rnd ≤ r → r ≤ N → PopulatedOn U T r }

namespace MysticetiLive

/-- **Mysticeti has the descent laws at slack `f`.** -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults Validator] [DecidableEq BlockId],
    (mysticetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent F.f

/-- **Mysticeti under round-robin is live at every count** — the paper's
A4 for its own schedule, with gap `n + 2`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults (Fin n)] (BlockId Payload : Type) [DecidableEq BlockId]
    (w : ℕ) (hk : Keyed (roundRobin n hn) w) (m : ℕ) (hm : 0 < m) (hmax : m ≤ w),
    (mysticetiLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload)).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + 2)

/-- The descent laws, and liveness under round-robin at every count. -/
def Statement : Prop := Descent ∧ RoundRobinLive

end MysticetiLive

end HammerheadTwo

end LeanDag
