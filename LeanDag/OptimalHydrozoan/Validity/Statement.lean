import LeanDag.OptimalHydrozoan.Delivery.Statement
import LeanDag.OptimalHydrozoan.EventualDecision.Statement
import LeanDag.Hydrozoan.Validity.Statement
/-!
# Optimal-Hydrozoan: validity — statement

Hydrozoan's `Validity` read over `DecidedOpt`. `ListsHistory` and
`ListsWithin` speak of the block record alone and are reused as they
are; the two claims are re-stated over an `OptUniverse` and this arc's
`DecidesBelow`.

The Optimal validity clause constrains which parents a block may take,
but never stands between a `T`-block and the `T`-blocks of the round
below: `SynchronisedOn` is a hypothesis here as in Hydrozoan, so the
references the route needs are given, and the committing slot is
reached through the unchanged slow path.
-/

namespace LeanDag

namespace OptimalHydrozoan

open LeanDag.Hydrozoan

namespace Validity

open LeanDag.Hydrozoan.Delivery (delivered authorRound)
open LeanDag.Hydrozoan.Validity (ListsHistory ListsWithin)
open LeanDag.OptimalHydrozoan.PrefixAgreement (DecidesBelow)

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [O : OptimalFaults Replica] [S : Slots Replica]

/-- **A `T`-led slot delivers every earlier `T`-block's key.** With the
committing slot `k` explicit: direct liveness commits `k`'s leader block,
synchrony puts `x` in its history, and the filter loses no key. -/
def RunDelivers (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (R k : ℕ) (x : BlockId),
    T ⊆ (LeanDag.Hydrozoan.Correct : Finset Replica) →  -- a set of correct replicas ...
    q Replica ≤ T.card →                 -- ... of at least a DAG quorum,
    SynchronisedOn U.toBlockRecord T R →  -- internally synchronised from R,
    S.leader k ∈ T →                     -- a T-led slot ...
    x ∈ U.ids →                          -- and a block ...
    (U.block x).creator ∈ T →            -- ... of T ...
    R ≤ (U.block x).round →              -- ... at or after R ...
    (U.block x).round < S.slotRound k →  -- ... and below the slot,
    (∀ r, (U.block x).round < r →        -- T filling every round from
      r ≤ S.slotRound k + 2 →            -- above the block to the slot's
      PopulatedOn U.toBlockRecord T r) →  -- decision round:
    ∀ (κ : Type) [DecidableEq κ] (key : BlockId → κ)  -- then for any key,
      (lin : BlockId → List BlockId),    -- any listing ...
      ListsHistory U.toBlockRecord lin →  -- ... of causal histories,
    ∀ (V : LeanDag.Hydrozoan.View U.toBlockRecord)  -- and any view
      (g : ℕ → Option BlockId) (n : ℕ),
      k < n → DecidesBelow U V g n →     -- decided past the slot:
      ∃ c ∈ delivered key lin g n, key c = key x  -- the key is delivered.

/-- **Validity, as the paper states it**: under the key
`(author, round)`, by a listing that stays inside the universe, the block
itself is delivered — its author is correct, so no other block of the
universe shares its key. -/
def DeliversBlock (U : OptUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (R k : ℕ) (x : BlockId),
    T ⊆ (LeanDag.Hydrozoan.Correct : Finset Replica) →  -- a set of correct replicas ...
    q Replica ≤ T.card →                 -- ... of at least a DAG quorum,
    SynchronisedOn U.toBlockRecord T R →  -- internally synchronised from R,
    S.leader k ∈ T →                     -- a T-led slot ...
    x ∈ U.ids →                          -- and a block ...
    (U.block x).creator ∈ T →            -- ... of T ...
    R ≤ (U.block x).round →              -- ... at or after R ...
    (U.block x).round < S.slotRound k →  -- ... and below the slot,
    (∀ r, (U.block x).round < r →        -- T filling every round from
      r ≤ S.slotRound k + 2 →            -- above the block to the slot's
      PopulatedOn U.toBlockRecord T r) →  -- decision round:
    ∀ (lin : BlockId → List BlockId),    -- then for any listing ...
      ListsHistory U.toBlockRecord lin →  -- ... of causal histories ...
      ListsWithin U.toBlockRecord lin →  -- ... and of nothing foreign,
    ∀ (V : LeanDag.Hydrozoan.View U.toBlockRecord)  -- and any view
      (g : ℕ → Option BlockId) (n : ℕ),
      k < n → DecidesBelow U V g n →     -- decided past the slot:
      x ∈ delivered (authorRound U.block) lin g n  -- the block is delivered.

/-- Validity over every fault configuration, schedule, and universe the
Optimal model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [OptimalFaults Replica] [Slots Replica]
    (U : OptUniverse Replica BlockId),
    RunDelivers U ∧ DeliversBlock U

end Validity

end OptimalHydrozoan

end LeanDag
