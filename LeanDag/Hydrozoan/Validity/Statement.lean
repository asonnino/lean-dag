import LeanDag.Hydrozoan.Delivery.Statement
import LeanDag.Hydrozoan.EventualDecision.Statement
/-!
# Validity — statement

The fourth property of Byzantine atomic broadcast, required only after
GST, as in Bullshark: from the round `R` of the liveness hypotheses on,
every block of a correct replica is eventually delivered by every
correct replica.

As everywhere in the liveness arc, "the correct replicas" are a set `T`
of them, of at least quorum size, that is synchronised and fills the
rounds: the claims are about blocks authored in `T`, and a correct
replica outside `T` — one that fell behind — is promised nothing. The
paper's reading is `T = Correct`.

The route is the paper's (`thm:validity`). From `R` on, every `T`-block
references every `T`-block of the round below (`SynchronisedOn`), so
while `T` fills the rounds (`PopulatedOn`) a `T`-block lies in the
causal history of every later `T`-block; a later `T`-led slot commits
its leader block (`DirectLiveness`); and what a committed leader's
history holds is delivered (`Delivery.Faithful`). No self-parent edge is
needed, unlike FinWhale's route.

`Delivery` holds for every per-leader listing `lin`; validity cannot,
and asks the one thing the paper's `LinearizeSubDags` gives:
`ListsHistory`, that a leader's listing holds its causal history.

Two claims, with the committing slot `k` explicit as in
`EventualDecision.RunDecidesBelow`: for every key, the block's key is
delivered; and under the paper's key, by a listing that stays inside
the universe, the block itself is. Both speak of any view and any
verdict assignment decided past `k` — no coverage is asked of the view,
the commit being derived on the full view and carried over by slot
agreement. That such an assignment exists is `EventualDecision`'s
claim; `validityProgress` in `Proof.lean` composes the two.
-/

namespace LeanDag

namespace Hydrozoan

namespace Validity

open LeanDag.Hydrozoan.PrefixAgreement (DecidesBelow)
open LeanDag.Hydrozoan.Delivery (delivered authorRound)

variable {Replica BlockId : Type*} [Fintype Replica] [DecidableEq Replica]
  [DecidableEq BlockId] [LinearOrder BlockId] [F : LeanDag.Hydrozoan.Faults Replica]
  [S : Slots Replica]

/-- **The listing holds the causal history**: whatever a leader block
reaches is in its list. The order within the list stays free. -/
def ListsHistory (U : BlockUniverse Replica BlockId) (lin : BlockId → List BlockId) : Prop :=
  ∀ L ∈ U.ids, ∀ x, Reaches U L x → x ∈ lin L

/-- **The listing stays inside the universe.** -/
def ListsWithin (U : BlockUniverse Replica BlockId) (lin : BlockId → List BlockId) : Prop :=
  ∀ L ∈ U.ids, ∀ x ∈ lin L, x ∈ U.ids

/-- **A `T`-led slot delivers every earlier `T`-block's key.** With the
committing slot `k` explicit: direct liveness commits `k`'s leader block,
synchrony puts `x` in its history, and the filter loses no key. -/
def RunDelivers (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (R k : ℕ) (x : BlockId),
    T ⊆ (Correct : Finset Replica) →     -- a set of correct replicas ...
    q Replica ≤ T.card →                 -- ... of at least a DAG quorum,
    SynchronisedOn U T R →               -- internally synchronised from R,
    S.leader k ∈ T →                     -- a T-led slot ...
    x ∈ U.ids →                          -- and a block ...
    (U.block x).creator ∈ T →            -- ... of T ...
    R ≤ (U.block x).round →              -- ... at or after R ...
    (U.block x).round < S.slotRound k →  -- ... and below the slot,
    (∀ r, (U.block x).round < r →        -- T filling every round from
      r ≤ S.slotRound k + 2 →            -- above the block to the slot's
      PopulatedOn U T r) →               -- decision round:
    ∀ (κ : Type) [DecidableEq κ] (key : BlockId → κ)  -- then for any key,
      (lin : BlockId → List BlockId),    -- any listing ...
      ListsHistory U lin →               -- ... of causal histories,
    ∀ (V : View U) (g : ℕ → Option BlockId) (n : ℕ),  -- and any view
      k < n → DecidesBelow U V g n →     -- decided past the slot:
      ∃ c ∈ delivered key lin g n, key c = key x  -- the key is delivered.

/-- **Validity, as the paper states it**: under the key
`(author, round)`, by a listing that stays inside the universe, the block
itself is delivered — its author is correct, so no other block of the
universe shares its key. -/
def DeliversBlock (U : BlockUniverse Replica BlockId) : Prop :=
  ∀ (T : Finset Replica) (R k : ℕ) (x : BlockId),
    T ⊆ (Correct : Finset Replica) →     -- a set of correct replicas ...
    q Replica ≤ T.card →                 -- ... of at least a DAG quorum,
    SynchronisedOn U T R →               -- internally synchronised from R,
    S.leader k ∈ T →                     -- a T-led slot ...
    x ∈ U.ids →                          -- and a block ...
    (U.block x).creator ∈ T →            -- ... of T ...
    R ≤ (U.block x).round →              -- ... at or after R ...
    (U.block x).round < S.slotRound k →  -- ... and below the slot,
    (∀ r, (U.block x).round < r →        -- T filling every round from
      r ≤ S.slotRound k + 2 →            -- above the block to the slot's
      PopulatedOn U T r) →               -- decision round:
    ∀ (lin : BlockId → List BlockId),    -- then for any listing ...
      ListsHistory U lin →               -- ... of causal histories ...
      ListsWithin U lin →                -- ... and of nothing foreign,
    ∀ (V : View U) (g : ℕ → Option BlockId) (n : ℕ),  -- and any view
      k < n → DecidesBelow U V g n →     -- decided past the slot:
      x ∈ delivered (authorRound U.block) lin g n  -- the block is delivered.

/-- Validity over every fault configuration, schedule, tie-break order,
and block universe the model admits. -/
def Statement : Prop :=
  ∀ (Replica BlockId : Type) [Fintype Replica] [DecidableEq Replica]
    [DecidableEq BlockId] [LinearOrder BlockId] [LeanDag.Hydrozoan.Faults Replica]
    [Slots Replica] (U : BlockUniverse Replica BlockId),
    RunDelivers U ∧ DeliversBlock U

end Validity

end Hydrozoan

end LeanDag
