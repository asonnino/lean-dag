import LeanDag.Steelhead.Model.Clauses
import LeanDag.Common.Ledger
/-!
# The ledger at any lawful rule — statement

What the output layer owes once the verdicts are agreed
(`steelhead.md` §3): the paper's Corollary 2, order and integrity, at any
rule of the interface. Five claims, all read off a validator's verdict
assignment `g` over a settled prefix of slots:

* **SH13a, the committed-leader sequence is agreed** — two validators
  that settled the same prefix read off the same list, in slot order,
  which is round order since `slotRound` is monotone;
* **SH13b, the ledger is agreed** — and so is the set of blocks it
  delivers, the causal histories of those leaders;
* **SH13c, the ledger is monotone** — nothing already output is dropped
  as further slots settle;
* **SH13d, a block enters at one slot, agreed** — the slot a block
  enters at is the same in both views, and no block enters at two slots;
* **SH13e, a committed block belongs to one slot** — the integrity half:
  without it one block could be delivered by two slots.

SH13a to SH13d assume the rule's laws and a settled prefix; SH13e assumes
neither, since a commit names its slot whatever the rule. The two pairs'
instances are in `MahiMahiPair/Ledger/` and `BlueBottlePair/Ledger/`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Ledger

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH13a to SH13d, the output of a settled prefix.** -/
def Output (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (n : ℕ) (g₁ g₂ : ℕ → Option BlockId),
    R.Laws →
    -- each view settled every slot below n, g its verdicts there
    (∀ k, k < n → R.Decided U V₁ k (g₁ k)) →
    (∀ k, k < n → R.Decided U V₂ k (g₂ k)) →
    -- the committed-leader sequence and the ledger are the same ...
    commitSeq g₁ n = commitSeq g₂ n ∧
      ledgerSet U g₁ n = ledgerSet U g₂ n ∧
      -- ... the ledger only grows as further slots settle ...
      (∀ m, n ≤ m → ledgerSet U g₁ n ⊆ ledgerSet U g₁ m) ∧
      -- ... and a block enters at one slot, which both views name
      (∀ (b : BlockId) (k : ℕ), k < n → OutputAt U g₁ b k → OutputAt U g₂ b k) ∧
      ∀ (b : BlockId) (k₁ k₂ : ℕ), OutputAt U g₁ b k₁ → OutputAt U g₁ b k₂ → k₁ = k₂

/-- **SH13e, integrity**: a committed block is the candidate of one slot, whichever views and
routes committed it. -/
def Integrity (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (k₁ k₂ : ℕ) (L : BlockId),
    R.Decided U V₁ k₁ (some L) → R.Decided U V₂ k₂ (some L) → k₁ = k₂

/-- The ledger at any rule, over every fault configuration, schedule, block universe and anchored
rule the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct),
    Output U R ∧ Integrity U R

end Ledger

end Steelhead

end LeanDag
