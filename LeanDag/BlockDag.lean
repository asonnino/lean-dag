import LeanDag.Block

/-!
# The block universe

`spec.md` §3.3 and the non-equivocation lemma T1.

A `BlockUniverse` is every block that exists — authored by anyone, correct
or Byzantine. Non-equivocation is stated **here**, at the universe level,
rather than on any individual DAG. Per-DAG would be too weak: two DAGs could
each satisfy "at most one block per correct validator per round" while
holding *different* such blocks, which is exactly a correct validator
equivocating, with both DAGs looking well-formed. T5 would silently break.

Note the `valid` field reads `ValidWrt block (block i)`, mentioning only its
sibling field `block`. That is the whole reason `ValidWrt` (§3.2) takes a
lookup function rather than a universe: a structure field cannot mention the
structure being defined.
-/

namespace LeanDag

/-- Every block that exists, together with the well-formedness conditions
the protocol guarantees. -/
structure BlockUniverse (Validator BlockId Payload : Type*)
    [Fintype Validator] [DecidableEq Validator] [Faults Validator] where
  /-- Which blocks exist. -/
  ids : Finset BlockId
  /-- What each id denotes. Total, with junk outside `ids`; every statement
  below quantifies over `i ∈ ids`, so the junk is never observed. -/
  block : BlockId → Block Validator BlockId Payload
  /-- Every referenced block is itself present. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  /-- Every block present is valid. -/
  valid : ∀ i ∈ ids, ValidWrt block (block i)
  /-- Correct validators do not equivocate: at most one block per correct
  author per round. Byzantine validators are unconstrained. -/
  no_equivocation : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator ∈ (Correct : Finset Validator) →
    (block i).creator = (block j).creator →
    (block i).round = (block j).round → i = j

/-- A **view**: one validator's local DAG. A subset of the universe that is
itself closed under references.

Views share `U.block`, so they disagree about *which* blocks they hold, never
about what an id denotes, and they inherit validity and non-equivocation from
`U` for free. Different correct validators may hold different views — that
asymmetry is the entire point of the cross-view results. -/
structure View (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator]
    (U : BlockUniverse Validator BlockId Payload) where
  /-- The ids this validator holds. -/
  ids : Finset BlockId
  /-- A view holds only blocks that exist. -/
  subset_ids : ids ⊆ U.ids
  /-- A view is closed downward: it holds everything its blocks reference. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable (U : BlockUniverse Validator BlockId Payload)

namespace BlockUniverse

variable {U}

/-- **T1.** A correct validator authors at most one block per round, so two
ids in the universe with the same correct author and the same round are the
*same id*.

Phrased around the author `v` rather than around `(U.block i).creator`,
because that is how every use site arrives: a quorum intersection yields a
correct validator, and T1 turns two blocks known to be authored by it into a
single concrete id. -/
theorem eq_of_creator_eq {v : Validator} {i j : BlockId}
    (hi : i ∈ U.ids) (hj : j ∈ U.ids) (hv : v ∈ (Correct : Finset Validator))
    (hic : (U.block i).creator = v) (hjc : (U.block j).creator = v)
    (hround : (U.block i).round = (U.block j).round) :
    i = j :=
  U.no_equivocation i hi j hj (hic ▸ hv) (hic.trans hjc.symm) hround

/-- Completeness, as a subset statement. -/
theorem refs_subset {i : BlockId} (hi : i ∈ U.ids) : (U.block i).refs ⊆ U.ids :=
  fun _ hj => U.complete i hi _ hj

/-- A reference sits in the round immediately below its referrer. -/
theorem round_of_mem_refs {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ (U.block i).refs) :
    (U.block j).round + 1 = (U.block i).round :=
  (U.valid i hi).predecessor j hj

/-- References of a non-genesis block carry a quorum of distinct authors.
This is the hypothesis T0' consumes. -/
theorem creators_quorum {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    2 * F.f + 1 ≤ (creatorsOf U.block (U.block i).refs).card :=
  (U.valid i hi).quorum hround

/-- A non-genesis block references at least one block. -/
theorem refs_nonempty {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    (U.block i).refs.Nonempty :=
  (U.valid i hi).refs_nonempty hround

end BlockUniverse

end LeanDag
