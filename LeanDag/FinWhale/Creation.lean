import LeanDag.FinWhale.Decided

/-!
# FinWhale — the block-creation rule, and the votes it forces

FinWhale creates a round-`(r+1)` block when one of three conditions
holds: **C1**, the local DAG has the round-`r` leader's block (L1) and
either a quorum of voters for the round-`(r−1)` leader or an SP-skip
pattern for it (L2); **C2**, the `2∆` timeout has expired; **C3**, the
local DAG has `n − f` round-`(r+1)` blocks from distinct validators.

Lemmas 18 and 19 are what those conditions buy: every correct block votes
for a correct leader, and every correct block two rounds up carries a
quorum of votes. The reactive route takes them as the schedule's wait
clauses. This file derives them instead, from the conditions themselves
together with two properties of the network and one of parent selection.

**The induction replaces the paper's `H`.** The paper's C3 case argues
that the fastest `n − 2f` honest validators cannot have been triggered by
C3, and that a C3-triggered validator must have received one of their
blocks. The pigeonhole behind the second step needs the honest set to be
exactly `n − f`, and is unavailable when fewer than `f` validators are
actually faulty. Induction on build time needs neither: a C3-triggered
validator holds `n − f` blocks of its own round, at least one of them
from a correct validator that built *strictly earlier*, and the induction
hypothesis applies to that one. What its block references, the holder
holds — views are closed under references — so the leader's block is in
hand, and parent selection puts it among the parents.

Two network properties and one selection property are what remain
assumed:

* `holds_built` — a correct validator's block is held only after it is
  built. A message is not received before it is sent.
* `builds_distinct` — no two correct validators build the same round at
  the same instant. An idealisation, and the only place a tie would stall
  the induction.
* `selects_leader` and `selects_votes` — parent selection takes the
  leader's block, and the votes, when they are held. This is the paper's
  "selecting the blocks that satisfy conditions L1 and L2", stated for
  every trigger rather than only for C1, which is how its own Lemmas 18
  and 19 use it.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {N : ℕ}

/-- Which of the three conditions created a block. -/
inductive Trigger where
  /-- C1: the leader's block and a quorum of votes are in hand. -/
  | leaderAndQuorum
  /-- C2: the timeout expired. -/
  | timeout
  /-- C3: a quorum of blocks of this very round is in hand. -/
  | roundQuorum
  deriving DecidableEq

/-- **The block-creation rule, over the pacing trunk.** `lead` is the
leader schedule, one leader per round. -/
structure Creation (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) (lead : ℕ → Validator) extends PaceCore U T N where
  /-- Time advances with rounds. -/
  built_lt : ∀ v ∈ T, ∀ n < top v, built v n < built v (n + 1)
  /-- Which condition created each block. -/
  trigger : Validator → ℕ → Trigger
  /-- **The network does not deliver before it sends.** -/
  holds_built : ∀ v ∈ T, ∀ t, ∀ b ∈ holds v t, (U.block b).creator ∈ T →
    built ((U.block b).creator) ((U.block b).round) ≤ t
  /-- **No two reliable validators build one round at one instant.** -/
  builds_distinct : ∀ u ∈ T, ∀ v ∈ T, ∀ n, u ≠ v → built u n ≠ built v n
  /-- **C1's L1**: the round-`r` leader's block is in hand. -/
  c1_leader : ∀ v ∈ T, ∀ n, n + 1 ≤ N → trigger v (n + 1) = Trigger.leaderAndQuorum →
    ∀ L ∈ U.ids, (U.block L).round = n → (U.block L).creator = lead n →
      L ∈ holds v (built v (n + 1))
  /-- **C1's L2**: either a quorum of held voters for the round-`r`
  leader, or a quorum of held blocks declining to vote for it. -/
  c1_votes : ∀ v ∈ T, ∀ n, n + 2 ≤ N → trigger v (n + 2) = Trigger.leaderAndQuorum →
    ∀ L ∈ U.ids, (U.block L).round = n → (U.block L).creator = lead n →
    (∃ S : Finset Validator, spQuorum Validator ≤ S.card ∧ ∀ u ∈ S, ∃ b ∈ U.ids,
        b ∈ holds v (built v (n + 2)) ∧ (U.block b).creator = u ∧
        (U.block b).round = n + 1 ∧ L ∈ (U.block b).refs) ∨
    (∃ S : Finset Validator, spQuorum Validator ≤ S.card ∧ ∀ u ∈ S, ∃ b ∈ U.ids,
        b ∈ holds v (built v (n + 2)) ∧ (U.block b).creator = u ∧
        (U.block b).round = n + 1 ∧ L ∉ (U.block b).refs)
  /-- **C2**: the full timeout was waited out. -/
  c2_wait : ∀ v ∈ T, ∀ n, trigger v (n + 1) = Trigger.timeout →
    built v n + timeout n ≤ built v (n + 1)
  /-- **C3**: `n − f` blocks of the round being built are in hand. -/
  c3_quorum : ∀ v ∈ T, ∀ n, n + 1 ≤ N → trigger v (n + 1) = Trigger.roundQuorum →
    ∃ S : Finset Validator, quorumCard Validator ≤ S.card ∧ ∀ u ∈ S, ∃ b ∈ U.ids,
      b ∈ holds v (built v (n + 1)) ∧ (U.block b).creator = u ∧
      (U.block b).round = n + 1
  /-- **Parent selection takes the leader's block** when it is held. -/
  selects_leader : ∀ v ∈ T, ∀ n, ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = n + 1 → ∀ L ∈ U.ids, (U.block L).round = n →
    (U.block L).creator = lead n → L ∈ holds v (built v (n + 1)) →
      L ∈ (U.block c).refs
  /-- **And it takes the votes** it holds. -/
  selects_votes : ∀ v ∈ T, ∀ n, ∀ c ∈ U.ids, (U.block c).creator = v →
    (U.block c).round = n + 2 → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    b ∈ holds v (built v (n + 2)) → b ∈ (U.block c).refs

/-- A block whose parents voting for `L` are a slow-path quorum —
`SPCertificate`, in the universe's vocabulary. -/
def CertifiesSP (U : BlockUniverse Validator BlockId Payload) (c L : BlockId) : Prop :=
  spQuorum Validator ≤
    (creatorsOf U.block (((U.block c).refs).filter (fun q => L ∈ (U.block q).refs))).card

namespace Creation

variable {lead : ℕ → Validator} (cr : Creation U T N lead)

omit [DecidableEq BlockId] in
/-- Rounds advance real time. -/
theorem le_built {v : Validator} (hv : v ∈ T) : ∀ n ≤ cr.top v, n ≤ cr.built v n := by
  intro n
  induction n with
  | zero => intro _; omega
  | succ n ih =>
    intro hn
    have := cr.built_lt v hv n (by omega)
    have := ih (by omega)
    omega

omit [DecidableEq BlockId] in
/-- Drift, from the trunk's catch-up rule. -/
theorem driftOn_of_catchup {R : ℕ} (hcard : quorumCard Validator ≤ T.card)
    (hgst : cr.gst ≤ R) : DriftOn cr.built T R (cr.delay + cr.proc) N :=
  cr.toPaceCore.driftOn_of_catchup hcard hgst (fun _ hu => cr.le_built hu)

/-- **A timeout-triggered builder holds every reliable block of the round
below.** The block is in its author's hands when built, convergence
carries it across within `delay`, and the collapsed drift plus the full
timeout place that arrival before the waiter's build. -/
theorem holds_of_timeout {R n : ℕ} (hcard : quorumCard Validator ≤ T.card)
    (hgst : cr.gst ≤ R) (hto : ∀ m, R ≤ m → 2 * cr.delay + cr.proc ≤ cr.timeout m)
    (hR : R ≤ n) (hN : n + 1 ≤ N) {v : Validator} (hv : v ∈ T)
    (hwait : cr.built v n + cr.timeout n ≤ cr.built v (n + 1))
    {b : BlockId} (hb : b ∈ U.ids) (hbT : (U.block b).creator ∈ T)
    (hbr : (U.block b).round = n) :
    b ∈ cr.holds v (cr.built v (n + 1)) := by
  have hD := cr.driftOn_of_catchup hcard hgst
  have htopb : n ≤ cr.top ((U.block b).creator) := hbr ▸ cr.le_top_of_built _ hbT b hb rfl
  have hgstb : cr.gst ≤ cr.built ((U.block b).creator) n :=
    le_trans (le_trans hgst hR) (cr.le_built hbT n htopb)
  have hown := cr.holds_own _ hbT n (by omega) b hb rfl hbr
  have hconv := cr.converges v hv _ hbT _ hgstb hown
  refine cr.holds_mono v _ _ ?_ hconv
  have hdrift := hD v hv _ hbT n hR (by omega)
  have := hto n hR
  omega

/-- **Lemma 18, derived from the creation rule.** Past the coverage
round, every reliable round-`(n+1)` block references a reliable leader's
round-`n` block.

The three conditions are three ways of holding the leader's block when
building. C1 holds it by its own L1. C2 waited the full timeout, and the
drift bound places the arrival first. C3 holds `n − f` blocks of the
round it is building, and the two quorums meet in a reliable validator
other than the builder, which built strictly earlier — so the induction
hypothesis makes *its* block a vote, and a view closed under references
holds what that block references. Parent selection does the rest. -/
theorem lemma18 {R n : ℕ} (hcard : quorumCard Validator ≤ T.card)
    (hgst : cr.gst ≤ R) (hto : ∀ m, R ≤ m → 2 * cr.delay + cr.proc ≤ cr.timeout m)
    (hR : R ≤ n) (hN : n + 1 ≤ N)
    {L : BlockId} (hL : L ∈ U.ids) (hLr : (U.block L).round = n)
    (hLc : (U.block L).creator = lead n) (hlead : lead n ∈ T) :
    ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = n + 1 →
      L ∈ (U.block c).refs := by
  suffices h : ∀ t, ∀ v ∈ T, cr.built v (n + 1) = t → ∀ c ∈ U.ids,
      (U.block c).creator = v → (U.block c).round = n + 1 → L ∈ (U.block c).refs by
    intro v hv c hc hcc hcr
    exact h _ v hv rfl c hc hcc hcr
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hv hbuilt c hc hcc hcr
    have harith := params_arith (Validator := Validator)
    -- whichever condition fired, the leader's block is in hand
    have hheld : L ∈ cr.holds v (cr.built v (n + 1)) := by
      rcases htrig : cr.trigger v (n + 1) with _ | _ | _
      · exact cr.c1_leader v hv n hN htrig L hL hLr hLc
      · exact cr.holds_of_timeout hcard hgst hto hR hN hv (cr.c2_wait v hv n htrig) hL (by rw [hLc]; exact hlead) hLr
      · -- the round's own quorum meets the reliable set twice over
        obtain ⟨S, hS, hSb⟩ := cr.c3_quorum v hv n hN htrig
        have hmeet := card_add_card_le_card_inter_add_card S T
        have hpair : 1 < (S ∩ T).card := by
          have := Finset.card_le_univ (S ∩ T)
          omega
        obtain ⟨w₁, w₂, hw₁, hw₂, hne⟩ := Finset.one_lt_card_iff.1 hpair
        obtain ⟨w, hw, hwv⟩ : ∃ w ∈ S ∩ T, w ≠ v := by
          rcases eq_or_ne w₁ v with rfl | h
          · exact ⟨w₂, hw₂, fun hv2 => hne (by rw [hv2])⟩
          · exact ⟨w₁, hw₁, h⟩
        rw [Finset.mem_inter] at hw
        obtain ⟨b, hb, hbheld, hbc, hbr⟩ := hSb w hw.1
        -- it built strictly earlier, so the induction hypothesis applies
        have hle : cr.built w (n + 1) ≤ cr.built v (n + 1) := by
          have := cr.holds_built v hv _ b hbheld (by rw [hbc]; exact hw.2)
          rw [hbc, hbr] at this
          exact this
        have hlt : cr.built w (n + 1) < t := by
          have := cr.builds_distinct w hw.2 v hv (n + 1) hwv
          omega
        have hvote := ih _ hlt w hw.2 rfl b hb hbc hbr
        exact cr.holds_closed v hv _ b hbheld L hvote
    exact cr.selects_leader v hv n c hc hcc hcr L hL hLr hLc hheld

/-- **Lemma 19, derived from the creation rule.** Every reliable
round-`(n+2)` block carries a slow-path quorum of parents voting for a
reliable leader's round-`n` block.

C1 holds a quorum of voters by its own L2 — its other branch, a quorum
declining to vote, is refuted by Lemma 18: a reliable validator's single
round-`(n+1)` block does vote, so such a quorum would be Byzantine and
`f < 2f + p`. C2 holds every reliable vote, by the same timeout argument
one round up. C3 goes through a strictly earlier reliable builder of its
own round, whose parents are votes and whose references the holder
therefore holds. -/
theorem lemma19 {R n : ℕ} (hcard : quorumCard Validator ≤ T.card)
    (hgst : cr.gst ≤ R) (hto : ∀ m, R ≤ m → 2 * cr.delay + cr.proc ≤ cr.timeout m)
    (hR : R ≤ n) (hN : n + 2 ≤ N)
    {L : BlockId} (hL : L ∈ U.ids) (hLr : (U.block L).round = n)
    (hLc : (U.block L).creator = lead n) (hlead : lead n ∈ T) :
    ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = n + 2 →
      CertifiesSP U c L := by
  have harith := params_arith (Validator := Validator)
  have hvotes := cr.lemma18 hcard hgst hto hR (by omega) hL hLr hLc hlead
  -- what the conclusion comes to: a quorum of held votes, selected
  have key : ∀ (v : Validator), v ∈ T → ∀ c ∈ U.ids, (U.block c).creator = v →
      (U.block c).round = n + 2 → ∀ S : Finset Validator, spQuorum Validator ≤ S.card →
      (∀ u ∈ S, ∃ b ∈ U.ids, b ∈ cr.holds v (cr.built v (n + 2)) ∧
        (U.block b).creator = u ∧ (U.block b).round = n + 1 ∧ L ∈ (U.block b).refs) →
      CertifiesSP U c L := by
    intro v hv c hc hcc hcr S hS hSb
    refine le_trans hS (Finset.card_le_card fun u hu => ?_)
    obtain ⟨b, hb, hbheld, hbc, hbr, hbvote⟩ := hSb u hu
    refine mem_creatorsOf.2 ⟨b, ?_, hbc⟩
    exact Finset.mem_filter.2 ⟨cr.selects_votes v hv n c hc hcc hcr b hb hbr hbheld, hbvote⟩
  suffices h : ∀ t, ∀ v ∈ T, cr.built v (n + 2) = t → ∀ c ∈ U.ids,
      (U.block c).creator = v → (U.block c).round = n + 2 → CertifiesSP U c L by
    intro v hv c hc hcc hcr
    exact h _ v hv rfl c hc hcc hcr
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro v hv hbuilt c hc hcc hcr
    rcases htrig : cr.trigger v (n + 2) with _ | _ | _
    · -- C1: its own L2, once the skip branch is refuted
      rcases cr.c1_votes v hv n hN htrig L hL hLr hLc with ⟨S, hS, hSb⟩ | ⟨S, hS, hSb⟩
      · exact key v hv c hc hcc hcr S hS hSb
      · exfalso
        have hdisj : ∀ u ∈ S, u ∉ T := by
          intro u hu huT
          obtain ⟨b, hb, -, hbc, hbr, hbno⟩ := hSb u hu
          exact hbno (hvotes u huT b hb hbc hbr)
        have hsub : S ⊆ (Finset.univ : Finset Validator) \ T := by
          intro u hu
          exact Finset.mem_sdiff.2 ⟨Finset.mem_univ u, hdisj u hu⟩
        have hcard' := Finset.card_le_card hsub
        rw [Finset.card_univ_sdiff] at hcard'
        simp only [spQuorum] at hS
        omega
    · -- C2: the timeout, so every reliable vote is in hand
      refine key v hv c hc hcc hcr T (le_trans (spQuorum_le_quorumCard (Validator := Validator))
        hcard) fun u hu => ?_
      obtain ⟨b, hb, hbc, hbr⟩ :=
        cr.toPaceCore.populatedOn hcard (n + 1) (by omega) u hu
      exact ⟨b, hb, cr.holds_of_timeout hcard hgst hto (by omega) (by omega) hv
          (cr.c2_wait v hv (n + 1) htrig) hb (by rw [hbc]; exact hu) hbr,
        hbc, hbr, hvotes u hu b hb hbc hbr⟩
    · -- C3: a strictly earlier reliable builder of this round
      obtain ⟨S, hS, hSb⟩ := cr.c3_quorum v hv (n + 1) (by omega) htrig
      have hmeet := card_add_card_le_card_inter_add_card S T
      have hpair : 1 < (S ∩ T).card := by
        have := Finset.card_le_univ (S ∩ T)
        omega
      obtain ⟨w₁, w₂, hw₁, hw₂, hne⟩ := Finset.one_lt_card_iff.1 hpair
      obtain ⟨w, hw, hwv⟩ : ∃ w ∈ S ∩ T, w ≠ v := by
        rcases eq_or_ne w₁ v with rfl | h
        · exact ⟨w₂, hw₂, fun hv2 => hne (by rw [hv2])⟩
        · exact ⟨w₁, hw₁, h⟩
      rw [Finset.mem_inter] at hw
      obtain ⟨b, hb, hbheld, hbc, hbr⟩ := hSb w hw.1
      have hle : cr.built w (n + 2) ≤ cr.built v (n + 2) := by
        have := cr.holds_built v hv _ b hbheld (by rw [hbc]; exact hw.2)
        rw [hbc, hbr] at this
        exact this
      have hlt : cr.built w (n + 2) < t := by
        have := cr.builds_distinct w hw.2 v hv (n + 2) hwv
        omega
      have hwcert := ih _ hlt w hw.2 rfl b hb hbc hbr
      -- `w`'s voting parents are held by `v`, and selected
      refine le_trans hwcert (Finset.card_le_card fun u hu => ?_)
      obtain ⟨q, hq, hqc⟩ := mem_creatorsOf.1 hu
      rw [Finset.mem_filter] at hq
      have hqids : q ∈ U.ids := U.complete b hb q hq.1
      have hqr : (U.block q).round = n + 1 := by
        have := U.round_of_mem_refs hb hq.1; omega
      refine mem_creatorsOf.2 ⟨q, ?_, hqc⟩
      refine Finset.mem_filter.2 ⟨?_, hq.2⟩
      exact cr.selects_votes v hv n c hc hcc hcr q hqids hqr
        (cr.holds_closed v hv _ b hbheld q hq.1)

end Creation

/-! ## The liveness interface, from the creation rule -/

section Bridge

variable {D : Dag Validator BlockId Payload}

/-- The universe's reading of a certificate is the DAG's. -/
theorem spCertificate_of_certifiesSP (hblk : D.block = U.block) {c L : BlockId}
    (h : CertifiesSP U c L) : SPCertificate D c L := by
  show spQuorum Validator ≤ (parentsVoting D c L).card
  simpa only [CertifiesSP, parentsVoting, hblk] using h

/-- **Lemma 20, from the creation rule.** A reliable leader's block is
committed by the slow path: every reliable validator's round-`(r+2)`
block certifies it, and they are `n − f ≥ 2f + p`. -/
theorem lemma20_of_creation (cr : Creation U T N D.leader)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hcard : quorumCard Validator ≤ T.card) {R n : ℕ}
    (hgst : cr.gst ≤ R) (hto : ∀ m, R ≤ m → 2 * cr.delay + cr.proc ≤ cr.timeout m)
    (hR : R ≤ n) (hN : n + 2 ≤ N)
    {L : BlockId} (hL : L ∈ D.ids) (hLr : (D.block L).round = n)
    (hLc : (D.block L).creator = D.leader n) (hlead : D.leader n ∈ T) :
    SPCommit D L := by
  have hLu : L ∈ U.ids := hids ▸ hL
  have hLrU : (U.block L).round = n := by rw [← hblk]; exact hLr
  have hcert := cr.lemma19 hcard hgst hto hR hN hLu hLrU
    (by rw [← hblk]; exact hLc) hlead
  refine ⟨T, le_trans (spQuorum_le_quorumCard (Validator := Validator)) hcard, fun v hv => ?_⟩
  obtain ⟨b, hb, hbc, hbr⟩ := cr.toPaceCore.populatedOn hcard (n + 2) (by omega) v hv
  refine ⟨b, ?_, by rw [hblk]; exact hbc,
    spCertificate_of_certifiesSP hblk (hcert v hv b hb hbc hbr)⟩
  simp only [blocksAt, Finset.mem_filter, hids, hblk, hLrU]
  exact ⟨hb, hbr⟩

/-- **The liveness interface, from the creation rule.** Every correct-led
slot below the horizon carries a direct commit — with the vote and
certificate clauses derived from C1, C2 and C3 rather than assumed. -/
theorem commits_of_creation (cr : Creation U T N D.leader)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hTeq : T = (Correct : Finset Validator)) {R : ℕ}
    (hgst : cr.gst ≤ R) (hto : ∀ m, R ≤ m → 2 * cr.delay + cr.proc ≤ cr.timeout m) :
    CommitsCorrectLeaders D R N := by
  subst hTeq
  intro s hR hN hsc
  obtain ⟨L, hL, hLc, hLr⟩ :=
    cr.toPaceCore.populatedOn card_correct s (by omega) (D.leader s) hsc
  refine ⟨L, ?_, Or.inr (lemma20_of_creation cr hids hblk card_correct hgst hto hR hN
    (hids ▸ hL) (by rw [hblk]; exact hLr) (by rw [hblk]; exact hLc) hsc)⟩
  simp only [slotBlocks, blocksAt, Finset.mem_filter, hids, hblk]
  exact ⟨⟨hL, hLr⟩, hLc⟩

/-- **Theorem 21, from the creation rule.** Where at most `p` validators
are Byzantine, the reliable validators' votes alone are a fast commit. -/
theorem theorem21_of_creation (cr : Creation U T N D.leader)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hTeq : T = (Correct : Finset Validator)) (hfew : F.byzantine.card ≤ P.p)
    {R n : ℕ} (hgst : cr.gst ≤ R)
    (hto : ∀ m, R ≤ m → 2 * cr.delay + cr.proc ≤ cr.timeout m)
    (hR : R ≤ n) (hN : n + 1 ≤ N)
    {L : BlockId} (hL : L ∈ D.ids) (hLr : (D.block L).round = n)
    (hLc : (D.block L).creator = D.leader n) (hlead : D.leader n ∈ T) :
    FastCommit D L := by
  subst hTeq
  have hLu : L ∈ U.ids := hids ▸ hL
  have hLrU : (U.block L).round = n := by rw [← hblk]; exact hLr
  have hvotes := cr.lemma18 card_correct hgst hto hR hN hLu hLrU
    (by rw [← hblk]; exact hLc) hlead
  have hsub : (Correct : Finset Validator) ⊆ voters D L := by
    intro v hv
    obtain ⟨b, hb, hbc, hbr⟩ := cr.toPaceCore.populatedOn card_correct (n + 1) (by omega) v hv
    refine mem_creatorsOf.2 ⟨b, ?_, by rw [hblk]; exact hbc⟩
    simp only [Finset.mem_filter, blocksAt, hids, hblk, hLrU]
    exact ⟨⟨hb, hbr⟩, hvotes v hv b hb hbc hbr⟩
  have hcard : fastCard Validator ≤ (Correct : Finset Validator).card := by
    have := card_correct_add_byzantine (Validator := Validator)
    simp only [fastCard]; omega
  exact le_trans hcard (Finset.card_le_card hsub)

end Bridge

end FinWhale

end LeanDag
