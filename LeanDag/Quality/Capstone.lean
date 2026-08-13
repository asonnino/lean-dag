import LeanDag.Quality.Inclusion
import LeanDag.Quantitative

/-!
# Chain quality: the capstone, and the quantitative bounds

`chain-quality.md` §4, CQP3 — **CQ7**. Two packagings of the arc's
results, in the house style of `dos_resistance`: quote enforceable or
standard conditions only, and say everything in one place.

* `chain_quality` — the combined statement: under a fair schedule over
  reliable validators, (a) *unconditionally*, every commit's flush
  covers all but at most `f` correct validators at every round below
  it — at least half — and (b) post-`R`, every correct block is in the
  flush of a committed slot the schedule fixes in advance.
* `committed_of_correct_block_within` / `…_by_round` — the quantitative
  forms: under a windowed-fair schedule the committing slot lies within
  `w` slots of the first slot above the block's round, and under
  bounded spacing its round is within `s·w` rounds — *"a correct block
  is committed within a schedule-window of its creation, once the DAG
  is synchronous."*

The block-fraction purity statement (CQ4) was assessed and **dropped**,
per the gate recorded in the design document: under `DoSValid` alone the
per-author block count in a cone carries the exponential pedigree
constant, and under the budget the cone-level Byzantine count is the
author's whole store bound — linear in the round, not in the layer —
so neither route yields a ratio worth quoting. The author-coverage
metric of CQ1–CQ3 is the honest one.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable [S : Slots Validator]
variable {T : Finset Validator} {w s R m : ℕ}

/-- The least slot at or above a round is monotone in the round. -/
theorem slotAt_le_slotAt {a b : ℕ} (h : a ≤ b) :
    slotAt Validator a ≤ slotAt Validator b :=
  Nat.find_min' _ (le_trans h (le_slotRound_slotAt (Validator := Validator) b))

/-- **CQ7, windowed.** Under a windowed-fair schedule, the committing
slot for round-`m` blocks lies within `w` slots of the first slot above
round `m`. -/
theorem committed_of_correct_block_within
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairWithin T w) (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', slotAt Validator (m + 1) ≤ k' ∧
      k' < slotAt Validator (m + 1) + w ∧
      m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k' := by
  obtain ⟨k', hk₁, hk₂, hlead⟩ := fair (slotAt Validator (m + 1))
  have hm : m < S.slotRound k' := by
    have h1 := le_slotRound_slotAt (Validator := Validator) (m + 1)
    have h2 := S.mono hk₁
    omega
  have hRk' : R ≤ S.slotRound k' := by omega
  refine ⟨k', hk₁, hk₂, hm, hRk', ?_⟩
  intro U N hpop hs hN
  obtain ⟨L, hLb, hdec⟩ :=
    decided_of_leader_of_populated hT hcard (hs.mono hT) hRk'
      (fun r _ hr => PopulatedOn.mono hT (hpop r hr)) (by omega) hlead
  refine ⟨L, hdec, ?_⟩
  intro b hb hbc hbr
  have hLc : (U.block L).creator ∈ (Correct : Finset Validator) := by
    rw [hLb.2.2]
    exact hT hlead
  have hmem : b ∈ history U L :=
    mem_history_of_decided_commit hs hdec hLc hb hbc (by omega)
      (by rw [hLb.2.1]; omega)
  exact ⟨hmem, fun g n hg hn =>
    mem_ledgerSet_of_mem_history hg hn (isLeaderBlock_of_decided hdec).1 hmem⟩

/-- **CQ7, by round.** With bounded slot spacing, the committing slot's
round is within `s·w` rounds of the first slot above `m`: a correct
block is committed within a schedule-window of rounds of its creation,
once the DAG is synchronous. -/
theorem committed_of_correct_block_by_round
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairWithin T w) (hs : BoundedSpacing (Validator := Validator) s)
    (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧
      S.slotRound k' ≤ S.slotRound (slotAt Validator (m + 1)) + s * w ∧
      R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k' := by
  obtain ⟨k', hk₁, hk₂, hm, hRk', hrest⟩ :=
    committed_of_correct_block_within (BlockId := BlockId) (Payload := Payload)
      hT hcard fair R m hRm
  refine ⟨k', hm, ?_, hRk', hrest⟩
  have := slotRound_le_of_boundedSpacing hs (slotAt Validator (m + 1))
    (k' - slotAt Validator (m + 1))
  have hle : k' = slotAt Validator (m + 1) + (k' - slotAt Validator (m + 1)) := by
    omega
  have hd : k' - slotAt Validator (m + 1) ≤ w := by omega
  rw [← hle] at this
  calc S.slotRound k'
      ≤ S.slotRound (slotAt Validator (m + 1)) +
        s * (k' - slotAt Validator (m + 1)) := this
    _ ≤ S.slotRound (slotAt Validator (m + 1)) + s * w :=
        Nat.add_le_add_left (Nat.mul_le_mul_left s hd) _

/-- **CQ7 (the capstone).** Chain quality in one statement, enforceable
or standard conditions only. Unconditionally: every commit's flush
covers at least half of the correct validators at every round below
it. Post-`R`, under a fair schedule: every correct block is in the
flush of a committed slot fixed in advance by the schedule. -/
theorem chain_quality (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R m : ℕ) (hRm : R ≤ m) :
    (∀ (U : BlockUniverse Validator BlockId Payload)
        (V : View Validator BlockId Payload U) (k : ℕ) (L : BlockId)
        (δ : ℕ), Decided U V k (some L) → δ < (U.block L).round →
        (Correct : Finset Validator).card ≤ 2 * (coveredAt U L δ).card) ∧
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k' :=
  ⟨fun _ _ _ _ _ hdec hδ =>
    card_correct_le_two_mul_coveredAt_of_decided hdec hδ,
   committed_of_correct_block hT hcard fair R m hRm⟩

end LeanDag
