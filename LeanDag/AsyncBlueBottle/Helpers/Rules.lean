import LeanDag.AsyncBlueBottle.Model.Rules
import LeanDag.MahiMahi.Helpers.Rules
/-!
# Helpers — the rule layer

Generated lemma infrastructure for `Model/Rules.lean`; not part of the
audit surface. Membership unfoldings, the two facts canonical support
supplies through Mahi-Mahi's `Votes`, and the arithmetic core every
safety result rests on — Odontoceti's O1, O1′, O2, O3 and O4′ with the
decision round at `r + 2` and the cone vote in place of the reference:
commit excludes skip, two commits name one block, a skipped slot fails
the weak test everywhere, a commit passes it from every block three
rounds up, and a commit is the only candidate that passes it.
-/

namespace LeanDag

namespace AsyncBlueBottle

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {L A : BlockId} {r : ℕ}

/-! ## Unfoldings -/

theorem mem_voters {q : BlockId} :
    q ∈ voters U L r ↔ q ∈ U.ids ∧ (U.block q).round = r + 2 ∧ MahiMahi.Votes U q L := by
  simp only [voters, decisionRoundAt, Finset.mem_filter, mem_blocksAt, and_assoc]

theorem mem_supporters {v : Validator} :
    v ∈ supporters U L r ↔ ∃ q ∈ U.ids, (U.block q).round = r + 2 ∧ MahiMahi.Votes U q L ∧
      (U.block q).creator = v := by
  simp only [supporters, mem_creatorsOf, mem_voters]
  tauto

theorem mem_blamerBlocks {q : BlockId} {a : Validator} :
    q ∈ blamerBlocks U a r ↔ q ∈ U.ids ∧ (U.block q).round = r + 2 ∧ MahiMahi.Blames U q a r := by
  simp only [blamerBlocks, decisionRoundAt, Finset.mem_filter, mem_blocksAt, and_assoc]

theorem mem_blamers {a v : Validator} :
    v ∈ blamers U a r ↔ ∃ q ∈ U.ids, (U.block q).round = r + 2 ∧ MahiMahi.Blames U q a r ∧
      (U.block q).creator = v := by
  simp only [blamers, mem_creatorsOf, mem_blamerBlocks]
  tauto

theorem mem_coneSupporters {v : Validator} :
    v ∈ coneSupporters U A L r ↔ ∃ q ∈ U.ids, (U.block q).round = r + 2 ∧ MahiMahi.Votes U q L ∧
      q ∈ history U A ∧ (U.block q).creator = v := by
  simp only [coneSupporters, mem_creatorsOf, Finset.mem_filter, mem_voters]
  tauto

/-- In-cone supporters are supporters. -/
theorem coneSupporters_subset_supporters : coneSupporters U A L r ⊆ supporters U L r :=
  Finset.image_subset_image (Finset.filter_subset _ _)

/-- Cones nest, so in-cone support does. -/
theorem coneSupporters_subset_of_reaches {B : BlockId} (hB : B ∈ U.ids) (h : Reaches U B A) :
    coneSupporters U A L r ⊆ coneSupporters U B L r := by
  refine Finset.image_subset_image fun q hq => ?_
  rw [Finset.mem_filter] at hq ⊢
  exact ⟨hq.1, history_subset_of_reaches hB h hq.2⟩

/-- A voter's block is in the universe at the decision round. -/
theorem voters_spec {q : BlockId} (hq : q ∈ voters U L r) :
    q ∈ U.ids ∧ (U.block q).round = r + 2 :=
  ⟨(mem_voters.mp hq).1, (mem_voters.mp hq).2.1⟩

theorem blamerBlocks_spec {q : BlockId} {a : Validator} (hq : q ∈ blamerBlocks U a r) :
    q ∈ U.ids ∧ (U.block q).round = r + 2 :=
  ⟨(mem_blamerBlocks.mp hq).1, (mem_blamerBlocks.mp hq).2.1⟩

/-! ## What canonical support supplies

A correct validator has one decision-round block, and that block votes
for at most one candidate of a slot and does not blame a slot it votes
in; so two sets of supporters, or supporters and blamers, meet only in
the Byzantine set. -/

/-- A validator both voting for `L` and blaming its slot at the decision
round has two blocks there. -/
theorem not_mem_correct_of_supports_of_blames {v : Validator} (hLr : (U.block L).round = r)
    (hs : v ∈ supporters U L r) (hb : v ∈ blamers U (U.block L).creator r) :
    v ∉ (Correct : Finset Validator) := by
  intro hv
  obtain ⟨q₁, hq₁, hr₁, hv₁, hc₁⟩ := mem_supporters.mp hs
  obtain ⟨q₂, hq₂, hr₂, hb₂, hc₂⟩ := mem_blamers.mp hb
  have := U.eq_of_creator_eq hq₁ hq₂ hv hc₁ hc₂ (by rw [hr₁, hr₂])
  subst this
  subst hLr
  exact MahiMahi.not_blames_of_votes hv₁ hb₂

/-- A validator voting for two distinct same-author blocks at one round
has two decision-round blocks. -/
theorem not_mem_correct_of_supports_two {L₁ L₂ : BlockId} {v : Validator} (hd : L₁ ≠ L₂)
    (hcr : (U.block L₁).creator = (U.block L₂).creator)
    (hrr : (U.block L₁).round = (U.block L₂).round)
    (h₁ : v ∈ supporters U L₁ r) (h₂ : v ∈ supporters U L₂ r) :
    v ∉ (Correct : Finset Validator) := by
  intro hv
  obtain ⟨q₁, hq₁, hr₁, hv₁, hc₁⟩ := mem_supporters.mp h₁
  obtain ⟨q₂, hq₂, hr₂, hv₂, hc₂⟩ := mem_supporters.mp h₂
  have := U.eq_of_creator_eq hq₁ hq₂ hv hc₁ hc₂ (by rw [hr₁, hr₂])
  subst this
  exact hd (MahiMahi.eq_of_votes hv₁ hv₂ hcr hrr)

/-- **Supporters and blamers together number at most `n + f`.** -/
theorem card_supporters_add_card_blamers_le (hLr : (U.block L).round = r) :
    (supporters U L r).card + (blamers U (U.block L).creator r).card ≤
      Fintype.card Validator + F.f :=
  card_add_card_le_of_inter_subset F.card_byzantine fun v hv => by
    have := not_mem_correct_of_supports_of_blames hLr (Finset.mem_inter.mp hv).1
      (Finset.mem_inter.mp hv).2
    simpa [mem_correct] using this

/-- **The supporters of two distinct same-author blocks together number
at most `n + f`.** -/
theorem card_supporters_add_card_supporters_le {L₁ L₂ : BlockId} (hd : L₁ ≠ L₂)
    (hcr : (U.block L₁).creator = (U.block L₂).creator)
    (hrr : (U.block L₁).round = (U.block L₂).round) :
    (supporters U L₁ r).card + (supporters U L₂ r).card ≤ Fintype.card Validator + F.f :=
  card_add_card_le_of_inter_subset F.card_byzantine fun v hv => by
    have := not_mem_correct_of_supports_two hd hcr hrr (Finset.mem_inter.mp hv).1
      (Finset.mem_inter.mp hv).2
    simpa [mem_correct] using this

/-! ## The blame is Mahi-Mahi's at wave four -/

/-- Mahi-Mahi's voting round at wave `4` is this arc's decision round. -/
theorem mahiMahi_votingRound_four (r : ℕ) : MahiMahi.votingRound 4 r = decisionRoundAt r := by
  unfold MahiMahi.votingRound decisionRoundAt
  omega

/-- The blamers are Mahi-Mahi's at wave `4`, block for block. -/
theorem blamers_eq_mahiMahi {a : Validator} : blamers U a r = MahiMahi.blamers U 4 a r := by
  unfold blamers blamerBlocks MahiMahi.blamers
  rw [mahiMahi_votingRound_four]

/-- **ABB1″.** -/
theorem directSkip_iff_mahiMahi {a : Validator} :
    DirectSkip U a r ↔ MahiMahi.DirectSkip U 4 a r := by
  unfold DirectSkip MahiMahi.DirectSkip
  rw [blamers_eq_mahiMahi]

/-! ## ABB1 — commit versus skip, and twin uniqueness -/

/-- **ABB1 (the paper's Lemma 20, direct case).** No slot is both directly
committed and directly skipped: supporters and blamers together number
at most `n + f`, and two quorums are more. Needs only `n ≥ 3f+1`. -/
theorem not_directSkip_of_directCommit (hLr : (U.block L).round = r) (hc : DirectCommit U L r)
    (hk : DirectSkip U (U.block L).creator r) : False := by
  have := card_supporters_add_card_blamers_le (U := U) hLr
  have h3 := F.card_validators
  unfold DirectCommit at hc
  unfold DirectSkip at hk
  omega

/-- **ABB1′ (the paper's Lemma 19, strong case).** Two directly committed
blocks by one author at one round are equal: their supporter quorums
together exceed `n + f`. Needs only `n ≥ 3f+1`. -/
theorem eq_of_directCommit {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (h₂ : DirectCommit U L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator)
    (hrr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂ := by
  by_contra hd
  have := card_supporters_add_card_supporters_le (U := U) (r := r) hd hcr hrr
  have h3 := F.card_validators
  unfold DirectCommit at h₁ h₂
  omega

/-! ## ABB2 — a skipped slot cannot muster the weak threshold -/

/-- **ABB2, the counting half.** A directly skipped slot's candidate has
at most `2f` supporters: supporters and blamers together number at most
`n + f`, and the blamers are `n − f`. -/
theorem card_supporters_le_of_directSkip {a : Validator} (hk : DirectSkip U a r)
    (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r) :
    (supporters U L r).card ≤ 2 * F.f := by
  have := card_supporters_add_card_blamers_le (U := U) hLr
  rw [hLc] at this
  unfold DirectSkip at hk
  omega

/-- **ABB2 (the paper's Lemma 20, indirect case).** A directly skipped
slot's candidate fails the weak test against **every** anchor:
`≤ 2f < n − 3f`. This is where `n ≥ 5f+1` is used. -/
theorem not_weakLink_of_directSkip {a : Validator} (hk : DirectSkip U a r)
    (hLc : (U.block L).creator = a) (hLr : (U.block L).round = r) (A : BlockId) :
    ¬ WeakLink U A L r := by
  intro ht
  have h1 := Finset.card_le_card
    (coneSupporters_subset_supporters (U := U) (A := A) (L := L) (r := r))
  have h2 := card_supporters_le_of_directSkip hk hLc hLr
  have h5 := F.card_validators5
  unfold WeakLink at ht
  omega

/-! ## ABB3 — propagation: every anchor's cone holds a weak certificate -/

private theorem weakLink_of_directCommit_aux (h : DirectCommit U L r) :
    ∀ d, ∀ A, A ∈ U.ids → (U.block A).round = r + 3 + d → WeakLink U A L r := by
  intro d
  induction d with
  | zero =>
      intro A hA hround
      -- the parent quorum meets the supporter quorum in `n−2f` authors, of
      -- whom the `≥ n−3f` correct ones put their (unique, hence voting)
      -- decision-round block into `A`'s cone
      have hq : quorumCard Validator ≤ (creatorsOf U.block (U.block A).refs).card :=
        U.creators_quorum hA (by omega)
      have hsub : (creatorsOf U.block (U.block A).refs ∩ supporters U L r) ∩
          (Correct : Finset Validator) ⊆ coneSupporters U A L r := by
        intro v hv
        obtain ⟨hvPS, hvC⟩ := Finset.mem_inter.mp hv
        obtain ⟨hvP, hvS⟩ := Finset.mem_inter.mp hvPS
        obtain ⟨p, hp, hpc⟩ := mem_creatorsOf.mp hvP
        obtain ⟨q, hq_ids, hq_round, hqv, hqc⟩ := mem_supporters.mp hvS
        have hp_ids : p ∈ U.ids := U.complete A hA p hp
        have hp_round : (U.block p).round = r + 2 := by
          have := U.round_of_mem_refs hA hp
          omega
        have hpq : p = q :=
          U.eq_of_creator_eq hp_ids hq_ids hvC hpc hqc (by omega)
        exact mem_coneSupporters.mpr
          ⟨p, hp_ids, hp_round, hpq ▸ hqv, mem_history_of_mem_refs hA hp, hpc⟩
      have h1 := Finset.card_union_add_card_inter
        (creatorsOf U.block (U.block A).refs) (supporters U L r)
      have h2 := Finset.card_le_univ
        (creatorsOf U.block (U.block A).refs ∪ supporters U L r)
      have h3 := card_le_card_inter_correct_add_byzantine
        (creatorsOf U.block (U.block A).refs ∩ supporters U L r)
      have h4 := Finset.card_le_card hsub
      have h5 := F.card_byzantine
      unfold DirectCommit at h
      unfold WeakLink
      omega
  | succ d ih =>
      intro A hA hround
      obtain ⟨p, hp⟩ := U.refs_nonempty hA (by omega)
      have hp_ids : p ∈ U.ids := U.complete A hA p hp
      have hp_round : (U.block p).round = r + 3 + d := by
        have := U.round_of_mem_refs hA hp
        omega
      have := ih p hp_ids hp_round
      unfold WeakLink at this ⊢
      exact le_trans this (Finset.card_le_card
        (coneSupporters_subset_of_reaches hA (Reaches.single hp)))

/-- **ABB3 (the paper's Lemma 18) — propagation.** If `L` is directly
committed, every block from three rounds above it on carries at least
`n − 3f` distinct authors of votes for it in its cone — one hop by
quorum intersection minus the twin discount, depth by cone
monotonicity. -/
theorem weakLink_of_directCommit (h : DirectCommit U L r) (hA : A ∈ U.ids)
    (hround : r + 3 ≤ (U.block A).round) : WeakLink U A L r :=
  weakLink_of_directCommit_aux h ((U.block A).round - (r + 3)) A hA (by omega)

/-! ## ABB4′ — a direct commit excludes every rival candidate -/

/-- **ABB4′ (the paper's Lemma 19, weak case).** A directly committed
block is the only same-author block that can pass the weak test, at any
anchor: `n−f` supporters of `L₁` and `n−3f` in-cone supporters of `L₂`
would overlap in at least `n−5f ≥ 1` correct authors, each voting for
two twins — impossible. -/
theorem eq_of_directCommit_of_weakLink {L₁ L₂ : BlockId}
    (h₁ : DirectCommit U L₁ r) (ht : WeakLink U A L₂ r)
    (hcr : (U.block L₁).creator = (U.block L₂).creator)
    (hrr : (U.block L₁).round = (U.block L₂).round) : L₁ = L₂ := by
  by_contra hne
  have hsub : supporters U L₁ r ∩ coneSupporters U A L₂ r ⊆ F.byzantine := by
    intro v hv
    obtain ⟨hv₁, hv₂⟩ := Finset.mem_inter.mp hv
    have := not_mem_correct_of_supports_two hne hcr hrr hv₁
      (coneSupporters_subset_supporters hv₂)
    simpa [mem_correct] using this
  have h1 := Finset.card_union_add_card_inter (supporters U L₁ r) (coneSupporters U A L₂ r)
  have h2 := Finset.card_le_univ (supporters U L₁ r ∪ coneSupporters U A L₂ r)
  have h3 := Finset.card_le_card hsub
  have h4 := F.card_byzantine
  have h5 := F.card_validators5
  unfold DirectCommit at h₁
  unfold WeakLink at ht
  omega

end AsyncBlueBottle

end LeanDag
