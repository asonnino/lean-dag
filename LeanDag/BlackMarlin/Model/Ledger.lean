import LeanDag.BlackMarlin.Model.Decision

/-!
# Black Marlin — the flush record

`commit(B)` does not deliver `past(B)` in one piece. It descends through
the undelivered anchors of `strong(B)`, flushing one segment per anchor
round from the lowest up (Algorithm 1, L18–L32), so what a validator
outputs is segmented by anchor round whether or not it applied the rule
at that round itself (`black-marlin.md` §11).

That segmentation is what the delivered **order** is, and it is also what
makes two validators' orders agree: a validator that committed at rounds
`3` and `5` and one that committed only at `7` flush the same segments,
because the second one's descent visits `5`, `4` and `3` on the way down.
A validator's record is modelled here rather than the recursion that
builds it, in the same way the core models `Decided` rather than the
implementation that decides.

**The descent steps by one round, and that is what pins it.** The
candidates at round `ρ` below a round-`(ρ+1)` block are that block's
references, and `ValidWrt.distinct_creators` allows at most one block per
author — so a consecutive step has at most one candidate and needs no
tie-break at all. The paper's L21–L24 supplies a tie-break for the case
where the descent skips an anchor round; its text does not parse (it uses
`maxAnchor(A)` as a set on L21 and as an element on L22, binds `A` as an
element of `A` on L24, and is undefined when the candidate set holds no
anchor), so nothing here transcribes it. `step` and `dense` are what the
descent guarantees when it does not skip, and `black-marlin.md` §11
records what is left over.

**Trusted core of the arc: definitions only.** No theorem lives in this
file.
-/

namespace LeanDag

namespace BlackMarlin

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [Rot : Rotation Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- The anchors of round `ρ` in `A`'s causal history — the candidates the
descent chooses among when it arrives at that round. -/
def coneAnchors (U : BlockUniverse Validator BlockId Payload)
    (A : BlockId) (ρ : ℕ) : Finset BlockId :=
  (blocksAt U ρ).filter (fun X => (U.block X).creator = Rot.anchor ρ ∧ X ∈ history U A)

/-- **A flush record**: the anchor block a validator flushed at each
round, and what the descent guarantees of it.

`step` is the descent's own shape — the anchor flushed at `ρ` is a
reference of the anchor flushed at `ρ + 1` — and `dense` says the descent
does not pass over a round whose anchor that reference set contains.
Neither says anything about a round the descent skips, which is the case
the paper's tie-break is for. -/
structure Flush (U : BlockUniverse Validator BlockId Payload) where
  /-- The anchor flushed at each round, where the descent flushed one. -/
  block : ℕ → Option BlockId
  /-- What is flushed at a round is that round's anchor. -/
  isAnchor : ∀ ρ L, block ρ = some L → IsAnchor U ρ L
  /-- **The descent steps by one round.** -/
  step : ∀ ρ L M, block ρ = some L → block (ρ + 1) = some M → L ∈ (U.block M).refs
  /-- **And does not pass over an anchor it references.** -/
  dense : ∀ ρ M, block (ρ + 1) = some M → (coneAnchors U M ρ).Nonempty →
    (block ρ).isSome

/-- The blocks a record has output through round `n`: everything in the
causal history of an anchor it flushed below `n`. Ordering *within* a
segment is the deterministic sort `τ`, which the rule does not constrain
and this arc does not model, so the ledger is a set and the record's
rounds are its positions. -/
def ledgerSet (U : BlockUniverse Validator BlockId Payload) (f : Flush U) (n : ℕ) :
    Set BlockId :=
  {b | ∃ ρ, ρ < n ∧ ∃ L, f.block ρ = some L ∧ Reaches U L b}

/-- `b` enters the ledger at round `ρ`: the first flushed anchor whose
causal history holds it. This is a block's position in the delivered
sequence, at the granularity of segments. -/
def OutputAt (U : BlockUniverse Validator BlockId Payload) (f : Flush U)
    (b : BlockId) (ρ : ℕ) : Prop :=
  (∃ L, f.block ρ = some L ∧ Reaches U L b) ∧
    ∀ σ, σ < ρ → ∀ L, f.block σ = some L → ¬ Reaches U L b

end BlackMarlin

end LeanDag
