import LeanDag.Steelhead.BlueBottlePair.Liveness.Statement
import LeanDag.Steelhead.Helpers.BlueBottlePair
import LeanDag.Steelhead.Helpers.MahiMahiPair.Liveness
import LeanDag.Steelhead.Helpers.Reactive
import LeanDag.Odontoceti.Liveness
import LeanDag.AsyncBlueBottle.Helpers.Synchrony
/-!
# Helpers — the `5f + 1` pair's liveness

Generated lemma infrastructure for `BlueBottlePair/Liveness/Statement.lean`;
not part of the audit surface. Each clause is proved once per half and
carried to the composite by SH6a, SH6c and `leastLinked_compose`: at
Odontoceti the commit is O7's quorum of supporters one round up and the
skip a quorum of slot blamers there; at Async BlueBottle the commit is
ABB10a's cone votes two rounds up and the skip a quorum of blames there.
Theorem 2 at the pair is then the generic helpers at the composite with
the waves two and three. Both arcs are consumed read-only.
-/

namespace LeanDag

namespace Steelhead

namespace BlueBottlePair

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  [F : Faults5 Validator] {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

section Slots

variable [S : Slots Validator]

/-! ## The clauses, half by half -/

/-- **Clause A4 at Odontoceti** (O7): every reliable block one round up references the reliable
leader's block, and a quorum of them is the direct commit. -/
theorem commitsUnderSync_odontoceti (U : BlockUniverse Validator BlockId Payload) :
    CommitsUnderSync (Odontoceti.odontocetiAnchored Validator BlockId Payload) U := by
  intro T V R₀ N k hT hcard hs hpop hR hN hV hlead
  have hdr : S.slotRound k + 1 ≤ N := hN
  obtain ⟨L, hL, hdc⟩ := Odontoceti.directCommit_of_leader_mem hcard hs hR
    (hpop _ hR (by omega)) (hpop _ (by omega) hdr) hlead
  exact ⟨L, hL, Odontoceti.directCommitIn_of_coversUpto hdc (hV.mono hdr)⟩

/-- **Clause A4 at Async BlueBottle** (ABB10a): the reliable leader is good, its block directly
committed by the cone votes two rounds up. -/
theorem commitsUnderSync_asyncBlueBottle (U : BlockUniverse Validator BlockId Payload) :
    CommitsUnderSync (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) U := by
  intro T V R₀ N k hT hcard hs hpop hR hN hV hlead
  have hdr : S.slotRound k + 2 ≤ N := hN
  have hg := AsyncBlueBottle.good_of_synchronisedOn hT hcard hs hR (hpop _ hR (by omega))
    (hpop _ (by omega) (by omega)) (hpop _ (by change R₀ ≤ S.slotRound k + 2; omega) hN) hlead
  obtain ⟨L, hLU, hLr, hLc, hdc⟩ := AsyncBlueBottle.mem_goodAt.mp hg
  exact ⟨L, ⟨hLU, hLr, hLc⟩, AsyncBlueBottle.directCommitIn_of_coversUpto hdc (hV.mono hdr)⟩

/-- **A silent leader is skipped at Odontoceti**: every block one round up blames a slot whose
leader has no block, so a quorum there is the direct skip. -/
theorem skipsSilent_odontoceti (U : BlockUniverse Validator BlockId Payload) :
    SkipsSilent (Odontoceti.odontocetiAnchored Validator BlockId Payload) U := by
  intro T V k hcard hcrash hpop hV
  change HoldsAtLeast U V (quorumCard Validator) (slotBlamers U k)
  unfold HoldsAtLeast
  refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
  obtain ⟨q, hq, hqc, hqr⟩ := hpop (S.slotRound k + 1) (by omega) le_rfl v hv
  refine mem_heldAuthors.mpr ⟨q, ?_, hV q hq (le_of_eq hqr), hqc⟩
  rw [slotBlamers, Finset.mem_filter]
  exact ⟨mem_blocksAt.mpr ⟨hq, hqr⟩, fun j _ hj => hcrash j hj.1 hj.2.1 hj.2.2⟩

/-- **A silent leader is skipped at Async BlueBottle**: every block two rounds up blames a slot
whose leader has no block, no candidate lying in its cone. -/
theorem skipsSilent_asyncBlueBottle (U : BlockUniverse Validator BlockId Payload) :
    SkipsSilent (AsyncBlueBottle.asyncBlueBottleAnchored Validator BlockId Payload) U := by
  intro T V k hcard hcrash hpop hV
  change HoldsAtLeast U V (quorumCard Validator)
    (AsyncBlueBottle.blamerBlocks U (S.leader k) (S.slotRound k))
  unfold HoldsAtLeast
  refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
  obtain ⟨q, hq, hqc, hqr⟩ := hpop (S.slotRound k + 2) (by omega) le_rfl v hv
  refine mem_heldAuthors.mpr ⟨q, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hq, hqr⟩, ?_⟩,
    hV q hq (le_of_eq hqr), hqc⟩
  unfold MahiMahi.Blames
  refine Finset.eq_empty_of_forall_notMem fun L hL => ?_
  obtain ⟨hLids, hLr, hLc, -⟩ := MahiMahi.mem_candidatesAt.mp hL
  exact hcrash L hLids hLr hLc

/-! ## SH-BB6a, SH-BB6c — the clauses at the composite -/

/-- **SH-BB6a.** SH6a at the family, Odontoceti's clause at kind `0` and Async BlueBottle's
elsewhere. -/
theorem commitsUnderSync_pair (U : BlockUniverse Validator BlockId Payload) :
    CommitsUnderSync (blueBottlePairAnchored Validator BlockId Payload) U :=
  commitsUnderSync_compose (rules := blueBottlePair Validator BlockId Payload) fun κ => by
    unfold blueBottlePair
    split
    · exact commitsUnderSync_odontoceti U
    · exact commitsUnderSync_asyncBlueBottle U

/-- **SH-BB6c.** SH6c at the family. -/
theorem skipsSilent_pair (U : BlockUniverse Validator BlockId Payload) :
    SkipsSilent (blueBottlePairAnchored Validator BlockId Payload) U :=
  skipsSilent_compose (rules := blueBottlePair Validator BlockId Payload) fun κ => by
    unfold blueBottlePair
    split
    · exact skipsSilent_odontoceti U
    · exact skipsSilent_asyncBlueBottle U

omit S in
/-- **The pair's tie-break has a choice**: both halves break ties by the least candidate. -/
theorem leastLinked_pair : LeastLinked (blueBottlePairAnchored Validator BlockId Payload) :=
  leastLinked_compose (rules := blueBottlePair Validator BlockId Payload) (fun κ => by
      unfold blueBottlePair
      split
      · exact fun hi h => Odontoceti.exists_least hi h
      · exact fun hi h => AsyncBlueBottle.exists_least hi h)
    pair_rungs pair_tie

/-- The pair's decision round is one round up at the synchronous kind. -/
theorem pair_decisionRound_zero {k : ℕ} (hk : S.kind k = 0) :
    (blueBottlePairAnchored Validator BlockId Payload).decisionRound k = S.slotRound k + 1 := by
  unfold AnchoredRule.decisionRound
  rw [hk, pairAnchored_waveAt_zero]

/-- And two rounds up at every other kind. -/
theorem pair_decisionRound_of_ne {k : ℕ} (hk : S.kind k ≠ 0) :
    (blueBottlePairAnchored Validator BlockId Payload).decisionRound k = S.slotRound k + 2 := by
  unfold AnchoredRule.decisionRound
  rw [pairAnchored_waveAt_of_ne hk]

/-! ## SH-BB6d, SH-BB6k -/

/-- **SH-BB6d.** Synchrony carries the candidate into every reliable cone two rounds up; the
reliable blocks there vote for it, the leader's only block at its round; a quorum of them is Async
BlueBottle's direct commit, and a view holding the decision round holds them. -/
theorem commitsOfDisseminationAsync {U : BlockUniverse Validator BlockId Payload}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {k : ℕ} {L q : BlockId}
    (hk : S.kind k ≠ 0) (hcard : quorumCard Validator ≤ T.card) (hL : IsLeaderBlock U k L)
    (huniq : ∀ L' ∈ U.ids, (U.block L').round = S.slotRound k →
      (U.block L').creator = S.leader k → L' = L)
    (hq : q ∈ U.ids) (hqr : (U.block q).round = S.slotRound k + 1) (hqT : (U.block q).creator ∈ T)
    (hqL : L ∈ (U.block q).refs) (hs : SynchronisedOn U T (S.slotRound k + 1))
    (hpop : ∀ r, S.slotRound k + 1 ≤ r →
      r ≤ (blueBottlePairAnchored Validator BlockId Payload).decisionRound k → PopulatedOn U T r)
    (hV : V.CoversUpto ((blueBottlePairAnchored Validator BlockId Payload).decisionRound k)) :
    (blueBottlePairAnchored Validator BlockId Payload).Decided U V k (some L) := by
  rw [pair_decisionRound_of_ne hk] at hpop hV
  have hreach := MahiMahiPair.reaches_of_synchronised_of_ref hcard hs hpop hq hqr hqT hqL
  have huniq' : ∀ L' ∈ U.ids, (U.block L').round = (U.block L).round →
      (U.block L').creator = (U.block L).creator → L' = L :=
    fun L' h1 h2 h3 => huniq L' h1 (h2.trans hL.2.1) (h3.trans hL.2.2)
  have hdc : AsyncBlueBottle.DirectCommit U L (S.slotRound k) := by
    unfold AsyncBlueBottle.DirectCommit
    refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
    obtain ⟨c, hc, hcc, hcr⟩ := hpop (S.slotRound k + 2) (by omega) le_rfl v hv
    rw [AsyncBlueBottle.mem_supporters]
    exact ⟨c, hc, hcr, MahiMahiPair.votes_of_reaches_of_unique hc hL.1 huniq'
      (hreach c hc (by omega) (by omega) (hcc ▸ hv)), hcc⟩
  refine AnchoredRule.Decided.directCommit hL ?_
  change (blueBottlePair Validator BlockId Payload (S.kind k)).Commit U V L (S.slotRound k)
    (S.kind k)
  simp only [blueBottlePair, if_neg hk]
  exact AsyncBlueBottle.directCommitIn_of_coversUpto hdc hV

/-- **SH-BB6k.** At a round that carries the leader wait the reliable blocks one round up
reference the reliable leader's block (`ReactiveS.votes`): a quorum of them is Odontoceti's direct
commit, and every block two rounds up reaches the leader's block through them, which is Async
BlueBottle's. -/
theorem reactiveCommits {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {waits : ℕ → Prop} {T : Finset Validator} {V : View Validator BlockId Payload U} {N R k : ℕ}
    (rs : ReactiveS U T N w waits) (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hgst : rs.gst ≤ R)
    (hto : ∀ n, R ≤ n → 2 * rs.delay + rs.proc ≤ rs.timeout n) (hR : R ≤ S.slotRound k)
    (hwait : waits (S.slotRound k))
    (hN : (blueBottlePairAnchored Validator BlockId Payload).decisionRound k ≤ N)
    (hV : V.CoversUpto ((blueBottlePairAnchored Validator BlockId Payload).decisionRound k))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧
      (blueBottlePairAnchored Validator BlockId Payload).Decided U V k (some L) := by
  have hN1 : S.slotRound k + 1 ≤ N := by
    by_cases hk : S.kind k = 0
    · rw [pair_decisionRound_zero hk] at hN; exact hN
    · rw [pair_decisionRound_of_ne hk] at hN; omega
  obtain ⟨L, hLmem, hLc, hLr⟩ :=
    rs.toPaceCore.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  have hvotes := rs.votes hcard hgst hto hR hwait hN1 hlead hL
  have hpop1 := rs.toPaceCore.populatedOn hcard (S.slotRound k + 1) hN1
  refine ⟨L, hL, AnchoredRule.Decided.directCommit hL ?_⟩
  change (blueBottlePair Validator BlockId Payload (S.kind k)).Commit U V L (S.slotRound k)
    (S.kind k)
  by_cases hk : S.kind k = 0
  · simp only [blueBottlePair, if_pos hk]
    rw [pair_decisionRound_zero hk] at hV
    exact Odontoceti.directCommitIn_of_coversUpto
      (Odontoceti.directCommit_of_votesAt hcard hpop1 hvotes) hV
  · simp only [blueBottlePair, if_neg hk]
    rw [pair_decisionRound_of_ne hk] at hN hV
    have hLcT : (U.block L).creator ∈ T := hL.2.2 ▸ hlead
    have hreach := MahiMahi.reaches_of_votes hT hcard hpop1 hL.1 hL.2.1 hLcT
      fun q hq hqr hqc => hvotes _ hqc q hq rfl hqr
    have hdc := AsyncBlueBottle.directCommit_of_reach hcard
      (rs.toPaceCore.populatedOn hcard (S.slotRound k + 2) hN) hL.1 (hT hLcT)
      fun q hq hqr => hreach q hq (by omega)
    exact AsyncBlueBottle.directCommitIn_of_coversUpto hdc hV

/-! ## SH-BB6 — Theorem 2 at the pair -/

/-- **SH-BB6.** The generic descent (SH6m) and round counts (SH6j, SH6p) at the pair's
composite, its clauses being SH-BB6a, SH-BB6c and `leastLinked_pair`, its laws SH-BB16a, and its
waves two at the synchronous kind and three elsewhere. -/
theorem pairDecides (U : BlockUniverse Validator BlockId Payload) :
    Liveness.PairDecides (S := S) U := by
  refine ⟨fun V h x hid hhop hcom =>
      floorChainDecidesFromCommit leastLinked_pair hid h x hhop hcom, ?_, ?_⟩
  · intro T V R N n hn lead k hid hkind hT hcard hs hpop hV hcrash hbij hsched hlt hR hstart hN
    exact floorChainDecidesWithinRounds hn blueBottlePairLaws leastLinked_pair
      (commitsUnderSync_pair U) (skipsSilent_pair U) (fun t => by rw [hkind t]; rfl) hid hT hcard
      hs hpop hV hcrash hbij hsched hlt hR hstart hN
  · intro T V R N p n W hn lead k hp hid hkind hsched hT hcard hs hpop hV hcrash hbij hlt hwait
      hasync hR hstart hN
    exact floorChainDecidesWithinRoundsAtPeriod hn hp blueBottlePairLaws leastLinked_pair
      (commitsUnderSync_pair U) (skipsSilent_pair U) rfl
      (by rw [pairAnchored_waveAt_of_ne (by omega : (1 : ℕ) ≠ 0)]) hid hkind hsched hT hcard hs
      hpop hV hcrash hbij hlt hwait hasync hR hstart hN

end Slots

end BlueBottlePair

end Steelhead

end LeanDag
