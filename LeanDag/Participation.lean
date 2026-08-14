import LeanDag.Block

/-!
# Participation predicates

`PopulatedFrom` and `SynchronisedFrom`, stated over the raw block assignment
and id population — the fault-agnostic data every universe type carries.
Neither predicate mentions validity, quorums, or a fault model, so pinning
them to a universe type would only thread an unused instance through their
statements; stated over the data, the Byzantine `BlockUniverse` and the
crash `Nemo.Universe` instantiate one definition instead of restating it.
-/

namespace LeanDag

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}
variable {blk : BlockId → Block Validator BlockId Payload} {ids : Finset BlockId}

/-- Every validator in `T` authors a block at round `r` among `ids`. -/
def PopulatedFrom (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ ids, (blk b).creator = v ∧ (blk b).round = r

/-- Decidable on concrete data: a bounded quantifier over two `Finset`s, so a
model can settle it by `decide`. -/
instance decidablePopulatedFrom [DecidableEq Validator]
    (T : Finset Validator) (r : ℕ) : Decidable (PopulatedFrom blk ids T r) :=
  inferInstanceAs (Decidable (∀ v ∈ T, ∃ b ∈ ids,
    (blk b).creator = v ∧ (blk b).round = r))

/-- Population is antitone: a smaller set is easier to populate. -/
theorem PopulatedFrom.mono {T T' : Finset Validator} {r : ℕ} (hsub : T ⊆ T')
    (h : PopulatedFrom blk ids T' r) : PopulatedFrom blk ids T r :=
  fun v hv => h v (hsub hv)

/-- From round `R` on, every `T`-authored block references every `T`-authored
block of the round below. Both quantifiers restricted to `T`, deliberately. -/
def SynchronisedFrom (blk : BlockId → Block Validator BlockId Payload)
    (ids : Finset BlockId) (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ ids, (blk b).round = n + 1 → (blk b).creator ∈ T →
    ∀ a ∈ ids, (blk a).round = n → (blk a).creator ∈ T → a ∈ (blk b).refs

/-- Coverage is antitone too: mutual coverage among a larger set implies it
among any subset. -/
theorem SynchronisedFrom.mono {T T' : Finset Validator} {R : ℕ} (hsub : T ⊆ T')
    (h : SynchronisedFrom blk ids T' R) : SynchronisedFrom blk ids T R :=
  fun n hn b hb hbr hbc a ha har hac => h n hn b hb hbr (hsub hbc) a ha har (hsub hac)

end LeanDag
