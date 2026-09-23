import LeanDag.Steelhead.BlueBottlePair.Period.Statement
import LeanDag.Steelhead.Helpers.Period
import LeanDag.Steelhead.Helpers.BlueBottlePair.Liveness
/-!
# Helpers — the `5f + 1` pair's period sequence

Generated lemma infrastructure for `BlueBottlePair/Period/Statement.lean`;
not part of the audit surface. Both rules' commits reach their candidates
through blocks the view holds, Odontoceti's through a support block one
round up and Async BlueBottle's through a vote two rounds up, whose cone
holds the candidate; a link reaches a supporter or a voter in the
anchor's cone, the threshold `n − 3f` being positive at `n ≥ 5f + 1`; a
direct skip rests on blames one or two rounds up. The composite inherits
both. Theorems 3 and 4 at the pair are then the generic helpers.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-! ## The rules' verdicts in their views -/

/-- **Odontoceti's verdicts are witnessed in their views**: a direct commit holds a support block
one round up, which references the candidate; a direct skip holds a blame there; a link counts
`n − 3f` supporters in the anchor's cone, one of which references the candidate. -/
theorem viewLaws_odontoceti :
    ViewLaws (Odontoceti.odontocetiAnchored Validator BlockId Payload) where
  commit_mem := fun {_ V L _ _} hc => by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hc)
    obtain ⟨q, hq, hqV, -⟩ := mem_heldAuthors.mp hv
    exact V.complete q hqV L (mem_votesFor.mp hq).2.2
  link_reaches := fun hl => by
    have hpos : 0 < Fintype.card Validator - 3 * F.f := by
      have := F.card_validators5
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le hpos hl)
    obtain ⟨q, -, -, hLq, hqA, -⟩ := mem_coneSupporters.mp hv
    exact Reaches.trans (reaches_of_mem_historyUptoFrom hqA) (Reaches.single hLq)
  skip_round := fun hs => by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hs)
    obtain ⟨q, hq, hqV, -⟩ := mem_heldAuthors.mp hv
    have hqr := (mem_blocksAt.mp (Finset.mem_filter.mp hq).1).2
    exact ⟨q, hqV, by omega⟩

/-- **Async BlueBottle's commits are witnessed in their views**: a direct commit holds a vote two
rounds up, whose cone holds the candidate; a link counts `n − 3f` voters in the anchor's cone. -/
theorem commitLaws_asyncBlueBottle :
    CommitLaws (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) where
  commit_mem := fun {_ V _ _ _} hc => by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hc)
    obtain ⟨q, hq, hqV, -⟩ := mem_heldAuthors.mp hv
    obtain ⟨-, -, hvote⟩ := AsyncBlueBottle.mem_voters.mp hq
    exact mem_of_reaches_of_closed V.complete hqV
      (reaches_of_mem_historyUptoFrom (Finset.mem_filter.mp hvote.1).2.2)
  link_reaches := fun hl => by
    have hpos : 0 < Fintype.card Validator - 3 * F.f := by
      have := F.card_validators5
      omega
    obtain ⟨v, hv⟩ := Finset.card_pos.mp (lt_of_lt_of_le hpos hl)
    obtain ⟨q, -, -, hvote, hqA, -⟩ := AsyncBlueBottle.mem_coneSupporters.mp hv
    exact Reaches.trans (reaches_of_mem_historyUptoFrom hqA)
      (reaches_of_mem_historyUptoFrom (Finset.mem_filter.mp hvote.1).2.2)

/-- **Async BlueBottle's verdicts are witnessed in their views**: its commits are, and a direct
skip holds a blame two rounds up. -/
theorem viewLaws_asyncBlueBottle :
    ViewLaws (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) where
  toCommitLaws := commitLaws_asyncBlueBottle
  skip_round := fun hs => by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hs)
    obtain ⟨q, hq, hqV, -⟩ := mem_heldAuthors.mp hv
    exact ⟨q, hqV, by have := (AsyncBlueBottle.blamerBlocks_spec hq).2; omega⟩

/-- **The pair's verdicts are witnessed in their views**, each kind's rule's being. -/
theorem viewLaws_pair : ViewLaws (blueBottlePairAnchored Validator BlockId Payload) :=
  viewLaws_compose (rules := blueBottlePair Validator BlockId Payload) fun κ => by
    unfold blueBottlePair
    split
    · exact viewLaws_odontoceti
    · exact viewLaws_asyncBlueBottle

/-- **Odontoceti breaks ties by the least candidate**, so every nonempty rung has a choice. -/
theorem leastLinked_odontoceti :
    LeastLinked (Odontoceti.odontocetiAnchored Validator BlockId Payload) :=
  fun hi h => Odontoceti.exists_least hi h

/-! ## SH-BB10, SH-BB10a, SH-BB10d, SH-BB14b -/

/-- **SH-BB10.** Each rule's own laws and the lemmas above. -/
theorem periodHypotheses : Period.PeriodHypotheses Validator BlockId Payload :=
  ⟨AsyncBlueBottle.asyncBlueBottleLaws, commitLaws_asyncBlueBottle, leastLinked_asyncBlueBottle,
    goodCommits_asyncBlueBottle, rfl, Odontoceti.odontocetiLaws, leastLinked_odontoceti,
    by change 1 ≤ 2; omega, blueBottlePairLaws, viewLaws_pair⟩

variable [S : Slots Validator] {U : BlockUniverse Validator BlockId Payload} {I K : ℕ} [NeZero K]
  {coin : ℕ → Validator} {upd : UpdateRule BlockId} {k₀ : ℕ}

/-- **SH-BB10d.** SH10d at Async BlueBottle, the clause ABB9c's. -/
theorem periodAt_of_clause {V : View Validator BlockId Payload U} {c N : ℕ} (hI : 0 < I)
    (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K) (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K)
    (hrun : ∀ j k, 1 ≤ k → k ≤ K →
      AsyncBlueBottle.UnpredictableRunWithin (S := controlSlots coin I K j k) U c 3 N)
    (hV : V.CoversUpto N) (j : ℕ) (hN : (j + 1) * I + (c + 3) * K + 2 ≤ N) :
    ∃ st, PeriodAt I K (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) coin
      upd k₀ U V (blueBottlePairAnchored Validator BlockId Payload) (j + 1) st :=
  Steelhead.periodAt_of_clause (wa := 3) leastLinked_asyncBlueBottle goodCommits_asyncBlueBottle
    le_rfl viewLaws_pair hI h₀ hK hupd hrun hV j (by omega)

/-- **SH-BB14b.** SH14b at `bbPair`, the good set Async BlueBottle's. -/
theorem all_decided {V : View Validator BlockId Payload U} {per : ℕ → ℕ}
    (hid : ∀ t, S.slotRound t = t) (hkind : ∀ t, S.kind t = adaptiveKind I per t) (hI : 0 < I)
    (hlead : ∀ r, S.kind r = 1 → S.leader r = coin r)
    (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K) (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K)
    {c N : ℕ} (hcK : (c + 3) * K ≤ I)
    (hrun : ∀ j k, 1 ≤ k → k ≤ K →
      AsyncBlueBottle.UnpredictableRunWithin (S := controlSlots coin I K j k) U c 3 N)
    (hV : V.CoversUpto N)
    (hper : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I K (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) coin upd k₀
          U V (blueBottlePairAnchored Validator BlockId Payload) j st ∧ per j = st.period)
    (s : ℕ) (h₁ : 1 ≤ s) (hN : (intervalOf I s + 3) * I + c + 3 + 2 ≤ N) :
    ∃ v, (blueBottlePairAnchored Validator BlockId Payload).Decided U V s v :=
  Steelhead.all_decided (p := bbPair Validator BlockId Payload) (wa := 3)
    (good := fun U r => AsyncBlueBottle.goodAt U r) Odontoceti.odontocetiLaws
    AsyncBlueBottle.asyncBlueBottleLaws leastLinked_odontoceti leastLinked_asyncBlueBottle
    commitLaws_asyncBlueBottle goodCommits_asyncBlueBottle (by change 1 ≤ 2; omega) rfl hid hkind
    hI hlead h₀ hK hupd hcK hrun hV hper s h₁ (by omega)

end BlueBottlePair

end Steelhead

end LeanDag
