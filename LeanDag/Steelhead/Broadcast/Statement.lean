import LeanDag.Steelhead.Model.Clauses
import LeanDag.Common.Ledger
/-!
# Atomic broadcast at any lawful rule — statement

The paper's Definition 1, clause by clause, read off a validator's
verdict assignment over a settled prefix (`steelhead.md` §3), at any
rule of the interface. Five claims:

* **SH17a, agreement** — a block one view delivers over a settled prefix,
  every view delivers over any settled prefix at least as long. That
  every view eventually settles such a prefix is the liveness half;
* **SH17b, integrity** — a block enters the ledger at one slot, and a
  delivered block is a block of the record, which carries its author;
* **SH17c, validity** — after GST a reliable block lies in the cone of
  every reliable block two rounds up, so it is delivered with the first
  committed leader above, once the prefix below is settled;
* **SH17d, validity under asynchrony** — a block every reliable validator
  has referenced by round `ρ` lies in the cone of every block above `ρ`,
  its author reliable or not, so the first committed slot above `ρ`
  delivers it, whichever leader it has;
* **SH17e, total order** — the slots at which two blocks enter the ledger
  are the same in every view that settled them, so their order is.

SH17a and SH17e assume the rule's laws; SH17b, SH17c and SH17d read no
law, since a committed leader's cone is what they read. The two pairs'
instances are in `MahiMahiPair/Broadcast/` and `BlueBottlePair/Broadcast/`.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Steelhead

namespace Broadcast

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
  [S : Slots Validator]

/-- **SH17a, agreement.** -/
def Agreement (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (n m : ℕ) (g₁ g₂ : ℕ → Option BlockId)
    (b : BlockId),
    R.Laws →
    -- V₁ settled every slot below n, V₂ every slot below m ≥ n
    (∀ k, k < n → R.Decided U V₁ k (g₁ k)) → (∀ k, k < m → R.Decided U V₂ k (g₂ k)) → n ≤ m →
    -- a block V₁ delivers, V₂ delivers
    b ∈ ledgerSet U g₁ n → b ∈ ledgerSet U g₂ m

/-- **SH17b, integrity.** -/
def Integrity (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (V : View Validator BlockId Payload U) (n : ℕ) (g : ℕ → Option BlockId) (b : BlockId)
    (k₁ k₂ : ℕ),
    (∀ k, k < n → R.Decided U V k (g k)) →
    -- a delivered block is a block of the record, so one its author proposed ...
    (b ∈ ledgerSet U g n → b ∈ U.ids) ∧
      -- ... and it enters the ledger at one slot
      (OutputAt U g b k₁ → OutputAt U g b k₂ → k₁ = k₂)

/-- **SH17c, validity.** -/
def Validity (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (n k r : ℕ)
    (g : ℕ → Option BlockId) (b L : BlockId),
    -- V settled every slot below n, and committed L at slot k below n
    (∀ k, k < n → R.Decided U V k (g k)) → k < n → g k = some L →
    -- b is a reliable block at round r, and T is synchronised from r and populates r + 1
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    SynchronisedOn U T r → PopulatedOn U T (r + 1) →
    b ∈ U.ids → (U.block b).round = r → (U.block b).creator ∈ T →
    -- slot k lies two rounds up or more
    r + 2 ≤ S.slotRound k →
    -- then V delivers b
    b ∈ ledgerSet U g n

/-- **SH17d, validity under asynchrony.** -/
def ValidityOfEventualReference (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (T : Finset Validator) (V : View Validator BlockId Payload U) (n k ρ : ℕ)
    (g : ℕ → Option BlockId) (b L : BlockId),
    -- V settled every slot below n, and committed L at slot k below n
    (∀ k, k < n → R.Decided U V k (g k)) → k < n → g k = some L →
    T ⊆ (Correct : Finset Validator) → quorumCard Validator ≤ T.card →
    -- every reliable block at round ρ references b, the reference rule's eventual coverage ...
    (∀ q ∈ U.ids, (U.block q).round = ρ → (U.block q).creator ∈ T → Reaches U q b) →
    -- ... the reliable validators populate that round, and the committed slot lies above it
    PopulatedOn U T ρ → ρ + 1 ≤ S.slotRound k →
    -- then V delivers b, whoever led the slot
    b ∈ ledgerSet U g n

/-- **SH17e, total order.** -/
def TotalOrder (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct) : Prop :=
  ∀ (V₁ V₂ : View Validator BlockId Payload U) (n : ℕ) (g₁ g₂ : ℕ → Option BlockId)
    (b b' : BlockId) (k k' : ℕ),
    R.Laws →
    -- both views settled every slot below n
    (∀ i, i < n → R.Decided U V₁ i (g₁ i)) → (∀ i, i < n → R.Decided U V₂ i (g₂ i)) →
    -- V₁ outputs b at slot k and b' at the later slot k', below n
    OutputAt U g₁ b k → OutputAt U g₁ b' k' → k < k' → k' < n →
    -- then V₂ outputs them at the same slots, so in the same order
    OutputAt U g₂ b k ∧ OutputAt U g₂ b' k'

/-- Atomic broadcast at any rule, over every fault configuration, schedule, block universe and
anchored rule the model admits. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [Faults Validator] [LinearOrder BlockId] [Slots Validator]
    (U : BlockUniverse Validator BlockId Payload)
    (R : AnchoredRule Validator BlockId Payload ValidWrt Correct),
    Agreement U R ∧ Integrity U R ∧ Validity U R ∧ ValidityOfEventualReference U R ∧
      TotalOrder U R

end Broadcast

end Steelhead

end LeanDag
