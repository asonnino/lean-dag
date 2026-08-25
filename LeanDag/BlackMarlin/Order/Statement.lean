import LeanDag.BlackMarlin.Model.Order
import LeanDag.BlackMarlin.Model.Descent
import LeanDag.BlackMarlin.Liveness.Statement

/-!
# Black Marlin — the delivered sequence, stated

Definition 1 speaks about `ab-deliver` events: a **list**, not a set.
`Ledger` and `Agreement` gave the set; this phase gives the list, by
modelling the sort `τ` of L26 and the filter of L27
(`black-marlin.md` §12). Nine claims:

* **BMO1, `AnchorLast`** — the anchor is last in its own segment, so the
  single sorted list of `history U L \ 𝒟` is what L26 and L30 emit
  together;
* **BMO2, `SeqAgree`** — records that agree below a round flush the same
  list;
* **BMO3, `SeqPrefix`** — and the list only extends;
* **BMO4, `Integrity`** — Definition 1's Integrity: no author-and-round
  is output twice, and everything output is a block of the universe;
* **BMO5, `KeyDelivered`** — every author-and-round flushed is output, by
  that block or by one of the same author and round;
* **BMO6, `CorrectDelivered`** — and for a *correct* author, by the block
  itself: it has no twin for the filter to prefer;
* **BMO7, `TotalOrder`** — Definition 1's Total order: two records that
  agree cannot output a pair in opposite orders;
* **BMO8, `DescentOrder`** — two descents that reach a common block
  output the same list below it, with no further hypothesis. BME5 and
  BMO2 composed;
* **BMO9, `Validity`** — Definition 1's Validity for reliable authors: a
  reliable validator's block is output by any record that flushes an
  anchor two rounds above it.

**Where the twin case still sits.** BMO6 delivers the block itself only
for a correct author. For an equivocator, BMO5 says *some* block of that
author and round is output, and which one depends on the segmentation —
so two validators whose records differ at a round can output different
twins. BMO8 rules that out wherever their descents meet; what is not
established is that they always do. §12 records what that would need.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace BlackMarlin

namespace Order

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] [Rot : Rotation Validator]
  {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}

/-- **BMO1, the anchor is last in its segment.** -/
def AnchorLast (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f : Flush U) (τ : TopoSort U) (ρ : ℕ) (L b : BlockId),
    f.block ρ = some L → b ∈ segment U f τ ρ →
    (segment U f τ ρ).idxOf b ≤ (segment U f τ ρ).idxOf L

/-- **BMO2, records that agree flush the same list.** -/
def SeqAgree (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (τ : TopoSort U) (n : ℕ),
    (∀ σ, σ < n → f₁.block σ = f₂.block σ) →
    deliverSeq U f₁ τ n = deliverSeq U f₂ τ n

/-- **BMO3, and the list only extends.** Nothing output is retracted, and
nothing already output is reordered. -/
def SeqPrefix (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f : Flush U) (τ : TopoSort U) (n m : ℕ), n ≤ m →
    deliverSeq U f τ n <+: deliverSeq U f τ m

/-- **BMO4, Definition 1's Integrity.** No author-and-round is output
twice, and everything output is a block of the universe — which for a
correct author is a block it produced, since blocks carry their
creator. -/
def Integrity (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f : Flush U) (τ : TopoSort U) (n : ℕ),
    (deliverSeq U f τ n).Pairwise (fun a b => key U a ≠ key U b) ∧
      ∀ b ∈ deliverSeq U f τ n, b ∈ U.ids

/-- **BMO5, every author-and-round flushed is output.** -/
def KeyDelivered (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f : Flush U) (τ : TopoSort U) (n : ℕ) (b : BlockId),
    b ∈ ledgerSeq U f τ n → ∃ c ∈ deliverSeq U f τ n, key U c = key U b

/-- **BMO6, and for a correct author, by the block itself.** -/
def CorrectDelivered (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f : Flush U) (τ : TopoSort U) (n : ℕ) (b : BlockId),
    b ∈ ledgerSeq U f τ n → (U.block b).creator ∈ (Correct : Finset Validator) →
    b ∈ deliverSeq U f τ n

/-- **BMO7, Definition 1's Total order.** -/
def TotalOrder (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (τ : TopoSort U) (n : ℕ) (a b : BlockId),
    (∀ σ, σ < n → f₁.block σ = f₂.block σ) →
    (deliverSeq U f₁ τ n).idxOf a < (deliverSeq U f₁ τ n).idxOf b →
    ¬ ((deliverSeq U f₂ τ n).idxOf b < (deliverSeq U f₂ τ n).idxOf a)

/-- **BMO8, two descents that meet output the same list.** The
composition of BME5 with BMO2: below a block both descents reached,
their records coincide, so their lists do. -/
def DescentOrder (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f₁ f₂ : Flush U) (τ : TopoSort U) (B₁ B₂ M : BlockId) (σ n : ℕ),
    B₁ ∈ U.ids → B₂ ∈ U.ids →
    f₁.block = flushRecord U B₁ → f₂.block = flushRecord U B₂ →
    flushRecord U B₁ σ = some M → flushRecord U B₂ σ = some M →
    n ≤ σ + 1 →
    deliverSeq U f₁ τ n = deliverSeq U f₂ τ n

/-- **BMO9, Definition 1's Validity for reliable authors.** A block a
reliable validator produced at round `ρ`, once coverage has taken hold,
is output by any record that flushes an anchor at round `ρ + 2`. -/
def Validity (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (f : Flush U) (τ : TopoSort U) (T : Finset Validator) (R ρ n : ℕ) (b L : BlockId),
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    SynchronisedOn U T R → R ≤ ρ → PopulatedOn U T (ρ + 1) →
    b ∈ U.ids → (U.block b).round = ρ → (U.block b).creator ∈ T →
    f.block (ρ + 2) = some L → ρ + 2 < n →
    b ∈ deliverSeq U f τ n

/-- The delivered sequence of the Black Marlin commit rule, over every
fault configuration, rotation, block universe and topological sort the
model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Rotation Validator]
    (U : BlockUniverse Validator BlockId Payload),
    AnchorLast U ∧ SeqAgree U ∧ SeqPrefix U ∧ Integrity U ∧ KeyDelivered U ∧
      CorrectDelivered U ∧ TotalOrder U ∧ DescentOrder U ∧ Validity U

end Order

end BlackMarlin

end LeanDag
