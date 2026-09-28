import LeanDag.Steelhead.Model.Pair
import LeanDag.Common.Ledger
/-!
# The `5f + 1` pair's atomic broadcast — statement

The paper's Definition 1 at BlueBottle's two variants: SH17 at the pair's
composite, whose laws hold (SH-BB16b), so no law is asked. Five claims:

* **SH-BB17a, agreement** — a block one view delivers over a settled
  prefix, every view delivers over any settled prefix at least as long;
* **SH-BB17b, integrity** — a delivered block is a block of the record,
  and it enters the ledger at one slot;
* **SH-BB17c, validity** — after GST a reliable block is delivered with
  the first committed leader two rounds up or more;
* **SH-BB17d, validity under asynchrony** — a block every reliable
  validator has referenced by round `ρ` is delivered with the first
  committed leader above `ρ`, whoever led it;
* **SH-BB17e, total order** — two blocks enter the ledger at the same
  slots in every view that settled them.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Broadcast

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH-BB17a, agreement.** -/
def Agreement (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (n m : ℕ) (g₁ g₂ : ℕ → Option BlockId)
    (b : BlockId),
    -- V₁ settled every slot below n, V₂ every slot below m ≥ n
    (∀ k, k < n → (blueBottlePairAnchored Validator BlockId Payload).Decided U V₁ k (g₁ k)) →
    (∀ k, k < m → (blueBottlePairAnchored Validator BlockId Payload).Decided U V₂ k (g₂ k)) →
    n ≤ m →
    -- a block V₁ delivers, V₂ delivers
    b ∈ ledgerSet U g₁ n → b ∈ ledgerSet U g₂ m

/-- **SH-BB17b, integrity.** -/
def Integrity (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (n : ℕ) (g : ℕ → Option BlockId) (b : BlockId)
    (k₁ k₂ : ℕ),
    (∀ k, k < n → (blueBottlePairAnchored Validator BlockId Payload).Decided U V k (g k)) →
    -- a delivered block is a block of the record, so one its author proposed ...
    (b ∈ ledgerSet U g n → b ∈ U.ids) ∧
      -- ... and it enters the ledger at one slot
      (OutputAt U g b k₁ → OutputAt U g b k₂ → k₁ = k₂)

/-- **SH-BB17c, validity.** -/
def Validity (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (n k r : ℕ)
    (g : ℕ → Option BlockId) (b L : BlockId),
    -- V settled every slot below n, and committed L at slot k below n
    (∀ k, k < n → (blueBottlePairAnchored Validator BlockId Payload).Decided U V k (g k)) →
    k < n → g k = some L →
    -- b is a reliable block at round r, and T is synchronised from r and populates r + 1
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    SynchronisedOn U T r → PopulatedOn U T (r + 1) →
    b ∈ U.ids → (U.block b).round = r → (U.block b).creator ∈ T →
    -- slot k lies two rounds up or more
    r + 2 ≤ S.slotRound k →
    -- then V delivers b
    b ∈ ledgerSet U g n

/-- **SH-BB17d, validity under asynchrony.** -/
def ValidityOfEventualReference (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (n k ρ : ℕ)
    (g : ℕ → Option BlockId) (b L : BlockId),
    -- V settled every slot below n, and committed L at slot k below n
    (∀ k, k < n → (blueBottlePairAnchored Validator BlockId Payload).Decided U V k (g k)) →
    k < n → g k = some L →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- every reliable block at round ρ references b, the reference rule's eventual coverage ...
    (∀ q ∈ U.ids, (U.block q).round = ρ → (U.block q).creator ∈ T → Reaches U q b) →
    -- ... the reliable validators populate that round, and the committed slot lies above it
    PopulatedOn U T ρ → ρ + 1 ≤ S.slotRound k →
    -- then V delivers b, whoever led the slot
    b ∈ ledgerSet U g n

/-- **SH-BB17e, total order.** -/
def TotalOrder (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (n : ℕ) (g₁ g₂ : ℕ → Option BlockId)
    (b b' : BlockId) (k k' : ℕ),
    -- both views settled every slot below n
    (∀ i, i < n → (blueBottlePairAnchored Validator BlockId Payload).Decided U V₁ i (g₁ i)) →
    (∀ i, i < n → (blueBottlePairAnchored Validator BlockId Payload).Decided U V₂ i (g₂ i)) →
    -- V₁ outputs b at slot k and b' at the later slot k', below n
    OutputAt U g₁ b k → OutputAt U g₁ b' k' → k < k' → k' < n →
    -- then V₂ outputs them at the same slots, so in the same order
    OutputAt U g₂ b k ∧ OutputAt U g₂ b' k'

/-- The `5f + 1` pair's atomic broadcast, over every fault configuration, schedule and block
universe the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload),
    Agreement U ∧ Integrity U ∧ Validity U ∧ ValidityOfEventualReference U ∧ TotalOrder U

end Broadcast

end BlueBottlePair

end Steelhead

end LeanDag
