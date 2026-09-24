import LeanDag.Steelhead.Model.Pair
import LeanDag.Common.Ledger
/-!
# The `5f + 1` pair's ledger — statement

The paper's Corollary 2 at BlueBottle's two variants: SH13 at the pair's
composite, whose laws hold (SH-BB16b), so no law is asked. Two claims:

* **SH-BB13a to SH-BB13d, the output of a settled prefix** — two views
  that settled the same prefix read off the same committed leaders and
  the same ledger, the ledger only grows, and a block enters at one slot
  both name;
* **SH-BB13e, integrity** — a committed block is the candidate of one
  slot.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

namespace Ledger

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH-BB13a to SH-BB13d, the output of a settled prefix.** -/
def Output (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (n : ℕ) (g₁ g₂ : ℕ → Option BlockId),
    -- each view settled every slot below n, g its verdicts there
    (∀ k, k < n → (blueBottlePairAnchored Validator BlockId Payload).Decided U V₁ k (g₁ k)) →
    (∀ k, k < n → (blueBottlePairAnchored Validator BlockId Payload).Decided U V₂ k (g₂ k)) →
    -- the committed-leader sequence and the ledger are the same ...
    commitSeq g₁ n = commitSeq g₂ n ∧
      ledgerSet U g₁ n = ledgerSet U g₂ n ∧
      -- ... the ledger only grows as further slots settle ...
      (∀ m, n ≤ m → ledgerSet U g₁ n ⊆ ledgerSet U g₁ m) ∧
      -- ... and a block enters at one slot, which both views name
      (∀ (b : BlockId) (k : ℕ), k < n → OutputAt U g₁ b k → OutputAt U g₂ b k) ∧
      ∀ (b : BlockId) (k₁ k₂ : ℕ), OutputAt U g₁ b k₁ → OutputAt U g₁ b k₂ → k₁ = k₂

/-- **SH-BB13e, integrity.** -/
def Integrity (U : BlockUniverse Validator BlockId Payload) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k₁ k₂ : ℕ) (L : BlockId),
    (blueBottlePairAnchored Validator BlockId Payload).Decided U V₁ k₁ (some L) →
    (blueBottlePairAnchored Validator BlockId Payload).Decided U V₂ k₂ (some L) → k₁ = k₂

/-- The `5f + 1` pair's ledger, over every fault configuration, schedule and block universe the
model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults5 Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload),
    Output U ∧ Integrity U

end Ledger

end BlueBottlePair

end Steelhead

end LeanDag
