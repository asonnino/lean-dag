import LeanDag.BlackMarlin.Model.Ledger

/-!
# Black Marlin — the delivered sequence

Algorithm 1, L26–L31 (`black-marlin.md` §12). Having fixed the segment
boundaries, `commit` flushes each segment through `τ`, "any deterministic
topological sorting", and emits a block only if no block of the same
author and round was emitted before. This file models both, so that what
a validator outputs is a **list** rather than a set.

**`τ` is a structure, not a choice.** The paper fixes no particular sort;
what it uses of one is that it is a function — hence shared — and that it
respects causality. `TopoSort` asks exactly that, so every result below
holds for whichever sort a deployment picks.

**The anchor needs no separate emission.** L26 flushes `τ(past(B) \ 𝒟)`
and L30 then emits `B`. Since every block of `history U B` is reachable
from `B`, a topological sort of `history U B \ 𝒟` places `B` last of its
own accord, and the segment below is that one list.

**The filter is stateful.** L27 tests the delivered set as it stands,
which changes within a segment as well as between them, so
`filterFirstFrom` threads it and returns both the emitted list and the
set it leaves behind.

**Trusted core of the arc: definitions only.** No theorem lives in this
file.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- **`τ`**: a deterministic topological sort of a set of blocks. A
function of the set alone, so two validators sorting the same set produce
the same list; and causally ordered, so a block never precedes what it
reaches. -/
structure TopoSort (U : BlockUniverse Validator BlockId Payload) where
  /-- The sorted list. -/
  sort : Finset BlockId → List BlockId
  /-- It holds exactly the set. -/
  mem : ∀ s b, b ∈ sort s ↔ b ∈ s
  /-- Without repetition. -/
  nodup : ∀ s, (sort s).Nodup
  /-- And in causal order: what a block reaches comes no later than it. -/
  topo : ∀ s a b, a ∈ s → b ∈ s → Reaches U b a →
    (sort s).idxOf a ≤ (sort s).idxOf b

/-- What a record has delivered below a round: the causal history of
every anchor it flushed there — the paper's `𝒟` at that point. -/
def deliveredBelow (U : BlockUniverse Validator BlockId Payload) (f : Flush U) (ρ : ℕ) :
    Finset BlockId :=
  (Finset.range ρ).biUnion (fun σ =>
    match f.block σ with
    | none => ∅
    | some L => history U L)

/-- The segment a record flushes at a round: what the anchor's cone adds,
sorted. Empty where the record flushes nothing. -/
def segment (U : BlockUniverse Validator BlockId Payload) (f : Flush U)
    (τ : TopoSort U) (ρ : ℕ) : List BlockId :=
  match f.block ρ with
  | none => []
  | some L => τ.sort (history U L \ deliveredBelow U f ρ)

/-- The blocks a record flushes through round `n`, in order. -/
def ledgerSeq (U : BlockUniverse Validator BlockId Payload) (f : Flush U)
    (τ : TopoSort U) (n : ℕ) : List BlockId :=
  (List.range n).flatMap (segment U f τ)

/-- What L27 tests a block by: its author and its round. -/
def key (U : BlockUniverse Validator BlockId Payload) (b : BlockId) : Validator × ℕ :=
  ((U.block b).creator, (U.block b).round)

/-- **The filter of L27**, threading the delivered set: the emitted list,
and the keys it leaves behind. -/
def filterFirstFrom (U : BlockUniverse Validator BlockId Payload) :
    List BlockId → Finset (Validator × ℕ) → List BlockId × Finset (Validator × ℕ)
  | [], seen => ([], seen)
  | (b :: bs), seen =>
      if key U b ∈ seen then filterFirstFrom U bs seen
      else
        (b :: (filterFirstFrom U bs (insert (key U b) seen)).1,
          (filterFirstFrom U bs (insert (key U b) seen)).2)

/-- **What a validator outputs**: the flushed sequence with L27 applied.
Definition 1 speaks about this list. -/
def deliverSeq (U : BlockUniverse Validator BlockId Payload) (f : Flush U)
    (τ : TopoSort U) (n : ℕ) : List BlockId :=
  (filterFirstFrom U (ledgerSeq U f τ n) ∅).1

end BlackMarlin

end LeanDag
