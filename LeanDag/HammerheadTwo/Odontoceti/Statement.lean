import LeanDag.HammerheadTwo.Model.Heads
import LeanDag.HammerheadTwo.Helpers.Mysticeti
import LeanDag.Odontoceti.Liveness

/-!
# Hammerhead 2.0 over Odontoceti — statement

The two-round rule at `n ≥ 5f + 1` (report §10; the paper's Blue
Bottle) as a base rule with its laws, as a live rule with its descent
laws at slack `f`, and the paper's A4 for it under round-robin: live at
every leader count with gap `n + 1`. The universe and views are the
Byzantine ones, so the history view is `historyViewOf`; the ids carry a
linear order, which the two-round indirect rule uses to commit the
least candidate that passes its test, and which supplies the
interface's decidable equality — no separate instance is assumed, so
that the two do not diverge.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace HammerheadTwo

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- **Odontoceti as a base rule** — the data. Wave length two; the direct
commit predicate counts supporters at the next round. -/
def odontoceti [Faults5 Validator] : BaseRule Validator BlockId Payload where
  Universe := BlockUniverse Validator BlockId Payload
  View := fun U => LeanDag.View Validator BlockId Payload U
  block := fun U => U.block
  ids := fun U => U.ids
  viewIds := fun V => V.ids
  full := fun U => LeanDag.View.full U
  historyView := fun U A hA => historyViewOf U A hA
  waveLength := 2
  DirectCommitIn := fun V L r => Odontoceti.DirectCommitIn _ V L r
  decDirect := fun _ _ _ => inferInstance
  Decided := fun S {U} V k v => @Odontoceti.Decided _ _ _ _ _ _ _ S U V k v

/-- **Odontoceti as a live rule**: a DAG is good when a correct quorum is
synchronised from `Rnd` and populates the rounds to `N`. -/
def odontocetiLive [Faults5 Validator] : LiveRule Validator BlockId Payload :=
  { odontoceti with
    Good := fun U Rnd N => ∃ T ⊆ (Correct : Finset Validator),
      quorumCard Validator ≤ T.card ∧ SynchronisedOn U T Rnd ∧
      ∀ r, Rnd ≤ r → r ≤ N → PopulatedOn U T r }

namespace Odontoceti

/-- **Odontoceti satisfies the laws**: O5 is the agreement law. -/
def Laws : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId],
    BaseRule.Laws (odontoceti (Validator := Validator) (BlockId := BlockId) (Payload := Payload))

/-- **Odontoceti has the descent laws at slack `f`**: O7 is the direct
commit of a good leader's slot; the indirect rule commits the least
candidate with a thick link, or skips. -/
def Descent : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [F : Faults5 Validator] [LinearOrder BlockId],
    (odontocetiLive (Validator := Validator) (BlockId := BlockId) (Payload := Payload)).Descent F.f

/-- **Odontoceti under round-robin is live at every count**, with gap
`n + 1`. -/
def RoundRobinLive : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) [Faults5 (Fin n)] (BlockId Payload : Type) [LinearOrder BlockId]
    (w : ℕ) (hk : Keyed (roundRobin n hn) w) (m : ℕ) (hm : 0 < m) (hmax : m ≤ w),
    (odontocetiLive (Validator := Fin n) (BlockId := BlockId) (Payload := Payload)).LiveOn
      (Sched (roundRobin n hn) hk m hm hmax) (n + 1)

/-- The laws, the descent laws, and liveness under round-robin. -/
def Statement : Prop := Laws ∧ Descent ∧ RoundRobinLive

end Odontoceti

end HammerheadTwo

end LeanDag
