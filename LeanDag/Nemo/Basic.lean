import LeanDag.Block

/-!
# Nemo-Nemo: the crash-fault DAG foundation

"Finding Nemo-Nemo: CFT DAG-based Consensus in the WAN."

Nemo-Nemo is crash-fault-tolerant: `n ≥ 2f+1` validators, all honest — they may
halt, but never equivocate. Its quorum is a bare **majority** `n/2+1`, which is
mathematically outside the core Byzantine model (`Faults` forces `n − f`, a
`~2n/3` supermajority). So this arc builds a self-contained crash foundation
consuming only the fault-agnostic parts of the core (`Block`, `creatorsOf`).

The crash setting is *leaner* than the Byzantine one: there is no `byzantine`
set, every validator is correct, so non-equivocation is universal and the single
quorum fact is that **two majorities intersect** — no correct-member filtering.

This file provides the majority quorum, its intersection lemma, crash block
validity, the crash universe, and the block-level lemmas the commit rule needs.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} {Payload : Type*}

/-- The majority quorum: strictly more than half the validators, `n/2 + 1`. -/
def majority (Validator : Type*) [Fintype Validator] : ℕ :=
  Fintype.card Validator / 2 + 1

/-- **The one quorum fact.** Two majorities always intersect —
`(n/2+1) + (n/2+1) > n` — and, all validators being honest, the shared member is
consistent. This is the crash analogue of the core's `exists_correct_mem_inter`,
with the correctness filtering gone. -/
theorem exists_mem_inter {Q₁ Q₂ : Finset Validator}
    (h₁ : majority Validator ≤ Q₁.card) (h₂ : majority Validator ≤ Q₂.card) :
    (Q₁ ∩ Q₂).Nonempty := by
  rw [← Finset.card_pos]
  have hunion : (Q₁ ∪ Q₂).card ≤ Fintype.card Validator := by
    rw [← Finset.card_univ]; exact Finset.card_le_univ _
  have hadd := Finset.card_union_add_card_inter Q₁ Q₂
  unfold majority at h₁ h₂
  omega

/-- Crash block validity: like the core `ValidWrt`, but the parents quorum is the
majority `n/2+1` rather than `n − f`, and the core's `self_parent` and
`distinct_creators` fields are gone. The implementation's block verifier imposes
neither: there is no self-parent check, and duplicate-author includes are
deduplicated by the stake aggregator, not rejected. Under crash the second is
also derivable — universal non-equivocation makes duplicate creators among refs
impossible (`Universe.eq_of_mem_refs_of_creator_eq`). -/
structure ValidWrt (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- Every reference sits in the immediately preceding round. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- Non-genesis blocks reference a **majority** of distinct validators. -/
  quorum : 0 < b.round → majority Validator ≤ (creators blk b).card

instance [DecidableEq BlockId] (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Decidable (ValidWrt blk b) :=
  decidable_of_iff
    ((∀ i ∈ b.refs, (blk i).round + 1 = b.round) ∧
      (0 < b.round → majority Validator ≤ (creators blk b).card))
    ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.predecessor, h.quorum⟩⟩

namespace ValidWrt

variable {blk : BlockId → Block Validator BlockId Payload}
  {b : Block Validator BlockId Payload}

/-- A non-genesis block has at least one reference (the majority quorum is
positive). -/
theorem refs_nonempty (h : ValidWrt blk b) (h0 : 0 < b.round) : b.refs.Nonempty := by
  have hq : majority Validator ≤ (creatorsOf blk b.refs).card := h.quorum h0
  have hpos : 0 < (creatorsOf blk b.refs).card := by unfold majority at hq; omega
  exact nonempty_of_creatorsOf_card_pos hpos

end ValidWrt

/-- The crash block universe: majority-parent validity and **universal**
non-equivocation — every validator is honest, so there is no Byzantine exemption.
No `Faults` instance is needed. -/
structure Universe (Validator BlockId Payload : Type*)
    [Fintype Validator] [DecidableEq Validator] where
  /-- Which blocks exist. -/
  ids : Finset BlockId
  /-- What each id denotes. -/
  block : BlockId → Block Validator BlockId Payload
  /-- Every referenced block is present. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  /-- Every block present is valid (majority parents). -/
  valid : ∀ i ∈ ids, ValidWrt block (block i)
  /-- **No validator equivocates** — one block per author per round, for everyone. -/
  no_equivocation : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator = (block j).creator → (block i).round = (block j).round → i = j

/-- A view: one validator's local, reference-closed sub-DAG. -/
structure View (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] (U : Universe Validator BlockId Payload) where
  /-- The ids this validator holds. -/
  ids : Finset BlockId
  /-- A view holds only blocks that exist. -/
  subset_ids : ids ⊆ U.ids
  /-- A view is closed under references. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (U.block i).refs, j ∈ ids

namespace Universe

variable {U : Universe Validator BlockId Payload}

/-- Two ids with the same author and round are the same id — universal, no
correctness hypothesis (the crash simplification of the core's T1). -/
theorem eq_of_creator_eq {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ U.ids)
    (hc : (U.block i).creator = (U.block j).creator)
    (hround : (U.block i).round = (U.block j).round) : i = j :=
  U.no_equivocation i hi j hj hc hround

/-- Completeness, as a subset statement. -/
theorem refs_subset {i : BlockId} (hi : i ∈ U.ids) : (U.block i).refs ⊆ U.ids :=
  fun _ hj => U.complete i hi _ hj

/-- A reference sits in the round immediately below its referrer. -/
theorem round_of_mem_refs {i j : BlockId} (hi : i ∈ U.ids) (hj : j ∈ (U.block i).refs) :
    (U.block j).round + 1 = (U.block i).round :=
  (U.valid i hi).predecessor j hj

/-- References of a non-genesis block carry a majority of distinct authors. -/
theorem creators_quorum {i : BlockId} (hi : i ∈ U.ids) (hround : 0 < (U.block i).round) :
    majority Validator ≤ (creatorsOf U.block (U.block i).refs).card :=
  (U.valid i hi).quorum hround

/-- Distinct creators among references are automatic under crash: two refs of
the same block sharing a creator sit at the same round (`predecessor`), so
universal `no_equivocation` identifies them. This is why the crash `ValidWrt`
has no `distinct_creators` field. -/
theorem eq_of_mem_refs_of_creator_eq {i j k : BlockId} (hi : i ∈ U.ids)
    (hj : j ∈ (U.block i).refs) (hk : k ∈ (U.block i).refs)
    (hc : (U.block j).creator = (U.block k).creator) : j = k := by
  have h1 := U.round_of_mem_refs hi hj
  have h2 := U.round_of_mem_refs hi hk
  exact U.eq_of_creator_eq (U.refs_subset hi hj) (U.refs_subset hi hk) hc (by omega)

/-- **Two majority-backed sets of round-`n` blocks share a block.** The crash
analogue of the core's `exists_common_mem_of_quorums`: majority intersection
(all honest) plus universal non-equivocation. -/
theorem exists_common_mem_of_quorums {s t : Finset BlockId} {n : ℕ}
    (hs : ∀ q ∈ s, q ∈ U.ids ∧ (U.block q).round = n)
    (ht : ∀ q ∈ t, q ∈ U.ids ∧ (U.block q).round = n)
    (hsq : majority Validator ≤ (creatorsOf U.block s).card)
    (htq : majority Validator ≤ (creatorsOf U.block t).card) :
    ∃ q, q ∈ s ∧ q ∈ t := by
  obtain ⟨v, hv⟩ := exists_mem_inter hsq htq
  rw [Finset.mem_inter, mem_creatorsOf, mem_creatorsOf] at hv
  obtain ⟨⟨q₁, hq₁, hq₁c⟩, q₂, hq₂, hq₂c⟩ := hv
  obtain ⟨hq₁i, hq₁r⟩ := hs q₁ hq₁
  obtain ⟨hq₂i, hq₂r⟩ := ht q₂ hq₂
  have : q₁ = q₂ :=
    U.eq_of_creator_eq hq₁i hq₂i (hq₁c.trans hq₂c.symm) (by omega)
  exact ⟨q₁, hq₁, this ▸ hq₂⟩

end Universe

end Nemo

end LeanDag
