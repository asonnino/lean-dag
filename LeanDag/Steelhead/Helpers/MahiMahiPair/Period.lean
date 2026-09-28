import LeanDag.Steelhead.MahiMahiPair.Period.Statement
import LeanDag.Steelhead.Helpers.Period
import LeanDag.Steelhead.Helpers.MahiMahiPair.Liveness
/-!
# Helpers — the `3f + 1` pair's period sequence

Generated lemma infrastructure for `MahiMahiPair/Period/Statement.lean`;
not part of the audit surface. Mahi-Mahi's commits are witnessed in their
views at every wave, a certificate reaching the candidate it certifies,
and its skips at waves of two rounds or more, the blame's vote round
lying at or above the slot's; the composite `steelheadAnchored w` inherits
both. SH-MM14a to SH-MM14c are the generic ones at `mmPair ws wa`, the
agreed output read at `steelheadAnchored (wavelength ws wa)`, which is
`steelheadAt (mmPair ws wa)`.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable {U : BlockUniverse Validator BlockId Payload}

/-! ## Mahi-Mahi's verdicts in their views -/

/-- A certificate reaches the candidate it certifies: it references a vote, whose cone holds the
candidate. -/
theorem reaches_of_certificate_mem {w : ℕ} {L C : BlockId} {r : ℕ}
    (hC : C ∈ MahiMahi.certificates U w L r) : Reaches U C L := by
  obtain ⟨hCU, -, hcar⟩ := mem_certificatesAt.mp hC
  obtain ⟨v, hv⟩ := Finset.card_pos.mp
    (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hcar)
  obtain ⟨b, hb, -⟩ := mem_creatorsOf.mp hv
  obtain ⟨hbref, hvote⟩ := mem_carriedVotes.mp hb
  exact Reaches.of_mem_refs hbref
    ((mem_history_iff (U.complete C hCU b hbref)).mp (Finset.mem_filter.mp hvote.1).2.2)

/-- **Mahi-Mahi's commits are witnessed in their views**, at every wave: a direct commit holds a
certificate, which reaches the candidate, and a link reaches a certificate. -/
theorem commitLaws_mahiMahi (w : ℕ) :
    CommitLaws (MahiMahi.mahiMahiAnchored Validator BlockId Payload w) where
  commit_mem := fun {_ V _ _ _} hc => by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hc)
    obtain ⟨C, hC, hCV, -⟩ := mem_heldAuthors.mp hv
    exact mem_of_reaches_of_closed V.complete hCV (reaches_of_certificate_mem hC)
  link_reaches := fun hl => by
    obtain ⟨C, hC, hre⟩ := hl
    exact hre.trans (reaches_of_certificate_mem hC)

/-- **Mahi-Mahi's verdicts are witnessed in their views** at a wave of two rounds or more: its
commits are (`commitLaws_mahiMahi`), and a direct skip holds a blame at the vote round
`r + w − 2`, at or above the slot's round. -/
theorem viewLaws_mahiMahi {w : ℕ} (hw : 2 ≤ w) :
    ViewLaws (MahiMahi.mahiMahiAnchored Validator BlockId Payload w) where
  toCommitLaws := commitLaws_mahiMahi w
  skip_round := fun hs => by
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hs)
    obtain ⟨q, hq, hqV, -⟩ := mem_heldAuthors.mp hv
    have hqr := (mem_blocksAt.mp (Finset.mem_filter.mp hq).1).2
    refine ⟨q, hqV, ?_⟩
    unfold MahiMahi.votingRound at hqr
    omega

/-- **The pair's verdicts are witnessed in their views** at waves of two rounds or more, each
kind's rule's being. -/
theorem viewLaws_steelhead {w : ℕ → ℕ} (hw : ∀ κ, 2 ≤ w κ) :
    ViewLaws (steelheadAnchored Validator BlockId Payload w) :=
  viewLaws_compose (rules := mahiMahiPair Validator BlockId Payload w) fun κ =>
    viewLaws_mahiMahi (hw κ)

section Slots

variable [S : Slots Validator]

/-- **No verdict of an anchor's history has its vote round above the anchor's**: a direct commit
holds a certificate of the history at the slot's decision round, a direct skip a blame at its vote
round, and an indirect verdict rests on an anchor at or above the slot's floor, whose own vote
round is bounded in turn. -/
theorem voteRound_le_of_decided_historyView {w : ℕ → ℕ} (hw : ∀ r, 2 ≤ w r) {A : BlockId}
    (hA : A ∈ U.ids) {s : ℕ} {v : Option BlockId}
    (h : Decided w U (U.historyView A hA) s v) :
    S.slotRound s + w (S.kind s) - 2 ≤ (U.block A).round := by
  induction h with
  | @directCommit k L _ hc =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hc)
    obtain ⟨C, hC, hCV, -⟩ := mem_heldAuthors.mp hv
    have hCr := (mem_certificatesAt.mp hC).2.1
    have hCA := round_le_of_mem_history hA hCV
    have := hw (S.kind k)
    unfold MahiMahi.decisionRoundAt at hCr
    omega
  | @directSkip k hs =>
    obtain ⟨v, hv⟩ := Finset.card_pos.mp
      (lt_of_lt_of_le (MysticetiProperties.quorumCard_pos (Validator := Validator)) hs)
    obtain ⟨q, hq, hqV, -⟩ := mem_heldAuthors.mp hv
    have hqr := (mem_blocksAt.mp (Finset.mem_filter.mp hq).1).2
    have hqA := round_le_of_mem_history hA hqV
    have := hw (S.kind k)
    unfold MahiMahi.votingRound at hqr
    omega
  | @indirectCommit k j _ _ _ _ he _ _ _ _ _ _ _ ihj _ =>
    rw [AnchoredRule.eligible_iff] at he
    simp only [steelheadAnchored_waveAt] at he
    have := hw (S.kind k)
    have := hw (S.kind j)
    omega
  | @indirectSkip k j _ _ he _ _ _ ihj _ =>
    rw [AnchoredRule.eligible_iff] at he
    simp only [steelheadAnchored_waveAt] at he
    have := hw (S.kind k)
    have := hw (S.kind j)
    omega

/-! ## SH-MM14 — the generic claims at the pair -/

variable {I K : ℕ} [NeZero K] {coin : ℕ → Validator} {ws wa : ℕ} {upd : UpdateRule BlockId}
  {k₀ : ℕ} {V : View Validator BlockId Payload U} {per : ℕ → ℕ}

/-- **SH-MM14a.** SH14a at `mmPair ws wa`, the good set Mahi-Mahi's. -/
theorem output_liveness (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hkind : ∀ t, S.kind t = adaptiveKind I per t) (hI : 0 < I)
    {b : ℕ}
    (hper : ∀ j, j ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I K (MahiMahi.mahiMahiAnchored _ _ _ wa) coin upd k₀ U V
          (steelheadAnchored _ _ _ (wavelength ws wa)) j st ∧ per j = st.period)
    (hlead : ∀ r, S.kind r = 1 → S.leader r = coin r)
    {s j₁ i₁ : ℕ} {A : BlockId} (h₁ : 1 ≤ s) (hs : intervalOf I s + 1 < j₁)
    (hA : IntervalAnchor I K (MahiMahi.mahiMahiAnchored _ _ _ wa) coin U V j₁ (per j₁) i₁ A)
    (hb : (j₁ + 1) * I < b) (hgood : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∃ v, Decided (wavelength ws wa) U V s v := by
  rw [← steelheadAt_mmPair] at hper
  obtain ⟨v, hv⟩ := Steelhead.output_liveness (p := mmPair Validator BlockId Payload ws wa)
    (good := fun U r => MahiMahi.goodAt U wa r) (MahiMahi.mahiMahiLaws hws)
    (MahiMahi.mahiMahiLaws (by omega)) (leastLinked_mahiMahi ws) (leastLinked_mahiMahi wa)
    (commitLaws_mahiMahi wa) (goodCommits_mahiMahi wa) (by change ws - 1 ≤ wa - 1; omega)
    (by change wa - 1 + 1 = wa; omega) hid hkind hI hper hlead h₁ hs hA hb hgood
    (hV.mono (by unfold MahiMahi.decisionRoundAt; omega))
  exact ⟨v, decided_mmPair_iff.mp hv⟩

/-- **SH-MM14c.** SH14c at `mmPair ws wa`. -/
theorem output_liveness_of_runs (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hkind : ∀ t, S.kind t = adaptiveKind I per t) (hI : 0 < I)
    (hlead : ∀ r, S.kind r = 1 → S.leader r = coin r) {b : ℕ}
    (hper : ∀ j', j' ≤ intervalOf I (b + wa - 1) → ∃ st,
      PeriodAt I K (MahiMahi.mahiMahiAnchored _ _ _ wa) coin upd k₀ U V
          (steelheadAnchored _ _ _ (wavelength ws wa)) j' st ∧ per j' = st.period)
    {s j : ℕ} (h₁ : 1 ≤ s) (hs : intervalOf I s + 1 < j) (hk : 1 ≤ per j) (hkI : per j ≤ I)
    (hgood : coin (firstControlRound I j (per j)) ∈
      MahiMahi.goodAt U wa (firstControlRound I j (per j)))
    (hb : (j + 1) * I < b) (hgoodb : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∃ v, Decided (wavelength ws wa) U V s v := by
  rw [← steelheadAt_mmPair] at hper
  obtain ⟨v, hv⟩ := Steelhead.output_liveness_of_runs
    (p := mmPair Validator BlockId Payload ws wa) (good := fun U r => MahiMahi.goodAt U wa r)
    (MahiMahi.mahiMahiLaws hws) (MahiMahi.mahiMahiLaws (by omega)) (leastLinked_mahiMahi ws)
    (leastLinked_mahiMahi wa) (commitLaws_mahiMahi wa) (goodCommits_mahiMahi wa)
    (by change ws - 1 ≤ wa - 1; omega) (by change wa - 1 + 1 = wa; omega) hid hkind hI hlead
    hper h₁ hs hk hkI hgood hb hgoodb (hV.mono (by unfold MahiMahi.decisionRoundAt; omega))
  exact ⟨v, decided_mmPair_iff.mp hv⟩

/-- **SH-MM14b.** SH14b at `mmPair ws wa`, the clause MM3c's at every control schedule. -/
theorem all_decided (hws : 2 ≤ ws) (hle : ws ≤ wa) (hwa : 3 ≤ wa) (hid : ∀ t, S.slotRound t = t)
    (hkind : ∀ t, S.kind t = adaptiveKind I per t) (hI : 0 < I)
    (hlead : ∀ r, S.kind r = 1 → S.leader r = coin r)
    (h₀ : 1 ≤ k₀) (hK : k₀ ≤ K) (hupd : ∀ A k, 1 ≤ k → k ≤ K → 1 ≤ upd A k ∧ upd A k ≤ K)
    {c N : ℕ} (hcK : (c + wa) * K ≤ I)
    (hrun : ∀ j k, 1 ≤ k → k ≤ K →
      MahiMahi.UnpredictableRunWithin (S := controlSlots coin I K j k) U wa c wa N)
    (hV : V.CoversUpto N)
    (hper : ∀ j, j ≤ intervalOf I N → ∃ st,
      PeriodAt I K (MahiMahi.mahiMahiAnchored _ _ _ wa) coin upd k₀ U V
          (steelheadAnchored _ _ _ (wavelength ws wa)) j st ∧ per j = st.period)
    (s : ℕ) (h₁ : 1 ≤ s)
    (hN : MahiMahi.decisionRoundAt wa ((intervalOf I s + 3) * I + c + wa) ≤ N) :
    ∃ v, Decided (wavelength ws wa) U V s v := by
  rw [← steelheadAt_mmPair] at hper
  obtain ⟨v, hv⟩ := Steelhead.all_decided (p := mmPair Validator BlockId Payload ws wa)
    (good := fun U r => MahiMahi.goodAt U wa r) (MahiMahi.mahiMahiLaws hws)
    (MahiMahi.mahiMahiLaws (by omega)) (leastLinked_mahiMahi ws) (leastLinked_mahiMahi wa)
    (commitLaws_mahiMahi wa) (goodCommits_mahiMahi wa) (by change ws - 1 ≤ wa - 1; omega)
    (by change wa - 1 + 1 = wa; omega) hid hkind hI hlead h₀ hK hupd hcK hrun hV hper s h₁
    (by unfold MahiMahi.decisionRoundAt at hN; omega)
  exact ⟨v, decided_mmPair_iff.mp hv⟩

end Slots

end MahiMahiPair

end Steelhead

end LeanDag
