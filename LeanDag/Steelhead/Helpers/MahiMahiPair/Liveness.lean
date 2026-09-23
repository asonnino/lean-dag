import LeanDag.Steelhead.MahiMahiPair.Liveness.Statement
import LeanDag.Steelhead.Helpers.Liveness
import LeanDag.Steelhead.Properties
import LeanDag.MahiMahi.Helpers.Liveness
import LeanDag.Properties.Derived.Descent
/-!
# Helpers — the `3f + 1` pair's liveness

Generated lemma infrastructure for `MahiMahiPair/Liveness/Statement.lean`;
not part of the audit surface. The pair supplies the clauses of
`Model/Clauses.lean` at `steelheadAnchored w`: the direct commit under
synchrony is the timed bridge at Steelhead's support at waves of three
rounds or more, the skip of a silent leader is a quorum of blames at the
vote round, and the rule has no tie. Each claim numbered like a generic
one is then the generic helper at this rule, with `FloorHop` read as
`FloorHopOf`. SH-MM6c and SH-MM6d read Mahi-Mahi's blames and votes
directly; SH-MM7 is Mahi-Mahi's descent and bridge at the chain schedule,
where the identity rounds discharge the spanning hypothesis; SH-MM8 is an
induction on the derivation, with the arithmetic of the residue class
`k − 1` done by hand since `omega` reads no variable modulus.
-/

namespace LeanDag

namespace Steelhead

namespace MahiMahiPair

open LeanDag.Properties SteelheadProperties

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}

/-- A correct quorum is a quorum of the core's fault model. -/
theorem isQuorum_core {T : Finset Validator} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) : (coreReliability Validator).IsQuorum T :=
  ⟨hT, by change Fintype.card Validator - Faults.f Validator ≤ T.card; exact hcard⟩

section Slots

variable [S : Slots Validator]

/-! ## The clauses at the pair -/

/-- A slot whose leader has no block at its round is directly skipped at its own wave in every view
holding its vote round, once a quorum populates that round: every block there blames the slot,
since no candidate lies in any cone. -/
theorem directSkipIn_of_crashed {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hcrash : ∀ L ∈ U.ids, (U.block L).round = S.slotRound k → (U.block L).creator ≠ S.leader k)
    (hpop : PopulatedOn U T (MahiMahi.votingRound (w (S.kind k)) (S.slotRound k)))
    (hV : V.CoversUpto (MahiMahi.votingRound (w (S.kind k)) (S.slotRound k))) :
    MahiMahi.DirectSkipIn U V (w (S.kind k)) (S.leader k) (S.slotRound k) := by
  unfold MahiMahi.DirectSkipIn HoldsAtLeast
  refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
  obtain ⟨q, hq, hqc, hqr⟩ := hpop v hv
  refine mem_heldAuthors.mpr ⟨q, Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hq, hqr⟩, ?_⟩,
    hV q hq (le_of_eq hqr), hqc⟩
  unfold MahiMahi.Blames
  refine Finset.eq_empty_of_forall_notMem fun L hL => ?_
  obtain ⟨hLids, hLr, hLc, -⟩ := MahiMahi.mem_candidatesAt.mp hL
  exact hcrash L hLids hLr hLc

/-- **SH-MM6c.** Every reliable block at the vote round blames a slot whose leader has no block at
the slot's round, and a view holding that round holds a quorum of them. -/
theorem skipsCrashed {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {k : ℕ}
    (hcard : quorumCard Validator ≤ T.card)
    (hcrash : ∀ L ∈ U.ids, (U.block L).round = S.slotRound k → (U.block L).creator ≠ S.leader k)
    (hpop : PopulatedOn U T (MahiMahi.votingRound (w (S.kind k)) (S.slotRound k)))
    (hV : V.CoversUpto (MahiMahi.votingRound (w (S.kind k)) (S.slotRound k))) :
    Decided w U V k none :=
  Decided.directSkip (directSkipIn_of_crashed hcard hcrash hpop hV)

/-- **Clause A4 at the pair**: the timed bridge at Steelhead's support for the one slot, then the
support's direct commit. Waves of three rounds or more, where the support's coverage law holds. -/
theorem commitsUnderSync_steelhead {w : ℕ → ℕ} (hw : ∀ κ, 3 ≤ w κ)
    (U : BlockUniverse Validator BlockId Payload) :
    CommitsUnderSync (steelheadAnchored Validator BlockId Payload w) U := by
  intro T V R₀ N k hT hcard hs hpop hR hN hV hlead
  have hdr : S.slotRound k + (w (S.kind k) - 1) ≤ N := hN
  refine shSupport_directCommitIn (fun κ => by have := hw κ; omega) S V hcard
    (fun n h1 h2 => hpop n (by omega) (by omega)) (fun L hL v hv c hc hcc hcr => ?_)
    (hV.mono hdr) hlead
  refine shSupport_ofCoverage hw U T (isQuorum_core hT hcard) (S.slotRound k) (S.kind k) L
    (fun n h1 h2 => hpop n (by omega) ?_) (Timed.coversToward_of_synchronisedOn hs hR) hL.1
    hL.2.1 ?_ c hc ?_ hcr
  · change n ≤ S.slotRound k + (w (S.kind k) - 1) at h2
    omega
  · change (BlockRecord.block U L).creator ∈ T
    rw [hL.2.2]
    exact hlead
  · change (BlockRecord.block U c).creator ∈ T
    rw [hcc]
    exact hv

/-- **A silent leader is skipped at the pair**: the vote round `r + w − 2` lies above the slot and
at or below its decision round `r + w − 1` at waves of three rounds or more, where a quorum's
blames skip it. -/
theorem skipsSilent_steelhead {w : ℕ → ℕ} (hw : ∀ κ, 3 ≤ w κ)
    (U : BlockUniverse Validator BlockId Payload) :
    SkipsSilent (steelheadAnchored Validator BlockId Payload w) U := by
  intro T V k hcard hcrash hpop hV
  have hw3 := hw (S.kind k)
  have hdr : (steelheadAnchored Validator BlockId Payload w).decisionRound k =
      S.slotRound k + (w (S.kind k) - 1) := rfl
  rw [hdr] at hpop hV
  exact directSkipIn_of_crashed hcard hcrash
    (hpop _ (by unfold MahiMahi.votingRound; omega) (by unfold MahiMahi.votingRound; omega))
    (hV.mono (by unfold MahiMahi.votingRound; omega))

omit S in
/-- **Every nonempty rung has a choice at the pair**: there is no tie. -/
theorem leastLinked_steelhead {w : ℕ → ℕ} :
    LeastLinked (steelheadAnchored Validator BlockId Payload w) :=
  fun hi h => exists_least hi h

/-- **A hop at the pair is a hop at its rule**: `FloorHop` reads the floor as `x + w κ` and the
rule as one round past `x + (w κ − 1)`, the same slot once the wave is one round or more. -/
theorem floorHopOf_iff {w : ℕ → ℕ} (hw : ∀ κ, 1 ≤ w κ) {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {x y : ℕ} :
    FloorHopOf (steelheadAnchored Validator BlockId Payload w) U V x y ↔ FloorHop w U V x y := by
  have := hw (S.kind x)
  have he : x + (steelheadAnchored Validator BlockId Payload w).waveAt (S.kind x) + 1 =
      x + w (S.kind x) := by
    simp only [steelheadAnchored_waveAt]
    omega
  unfold FloorHopOf FloorHop
  rw [he]

omit S in
/-- Waves of three rounds or more give the pair's laws, which ask two. -/
theorem laws_of_three {w : ℕ → ℕ} (hw : ∀ κ, 3 ≤ w κ) :
    (steelheadAnchored Validator BlockId Payload w).Laws :=
  steelheadLaws fun κ => by have := hw κ; omega

/-! ## SH-MM6 — the generic claims at the pair -/

/-- **SH-MM6a.** The clause at the pair, with the commit read as a verdict. -/
theorem commitsOfSynchrony {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {R N k : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hR : R ≤ S.slotRound k)
    (hN : ∀ j, j ≤ k → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N)
    (hV : V.CoversUpto N) (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧
      MahiMahi.DirectCommitIn U V (w (S.kind k)) L (S.slotRound k) ∧
      Decided w U V k (some L) := by
  obtain ⟨L, hL, hin⟩ :=
    commitsUnderSync_steelhead hw U T V R N k hT hcard hs hpop hR (hN k le_rfl) hV hlead
  exact ⟨L, hL, hin, Decided.directCommit hL hin⟩

/-- **SH-MM6b.** SH6b at the pair's rule. -/
theorem allDecidedBelowOfSynchrony {w : ℕ → ℕ} (hw : ∀ r, 3 ≤ w r) {T : Finset Validator}
    {c : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hspan : (steelheadAnchored Validator BlockId Payload w).SpansEligible (S := S) c)
    (fair : FairRunOn T c) (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N →
        (∀ j, j < b + c → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
        ∀ i, i < b → ∃ v, Decided w U V i v :=
  Steelhead.allDecidedBelowOfSynchrony leastLinked_steelhead (commitsUnderSync_steelhead hw) hT
    hcard hspan fair R k

/-- **SH-MM6e.** SH6e at the pair's rule, the floor `k + w κ` read as one round past its decision
round. -/
theorem decidedOfReliableAboveFloor {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) (hid : ∀ t, S.slotRound t = t) {T : Finset Validator}
    {V : View Validator BlockId Payload U} {R N k a : ℕ} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hs : SynchronisedOn U T R)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hR : R ≤ k) (hka : k + w (S.kind k) ≤ a)
    (hlead : S.leader a ∈ T)
    (hdec : ∀ j, k + w (S.kind k) ≤ j → j < a → ∃ v, Decided w U V j v)
    (hN : ∀ j, j ≤ a → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N)
    (hV : V.CoversUpto N) : ∃ v, Decided w U V k v := by
  have := hw (S.kind k)
  have he : k + (steelheadAnchored Validator BlockId Payload w).waveAt (S.kind k) + 1 =
      k + w (S.kind k) := by
    simp only [steelheadAnchored_waveAt]
    omega
  exact Steelhead.decidedOfReliableAboveFloor leastLinked_steelhead
    (commitsUnderSync_steelhead hw U) hid hT hcard hs hpop hR (by rw [he]; exact hka) hlead
    (fun j hj => hdec j (by rw [← he]; exact hj)) (hN a le_rfl) hV

/-- **SH-MM6f.** SH6f at the pair's rule. -/
theorem floorChainDecides {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) (hid : ∀ t, S.slotRound t = t) {T : Finset Validator}
    {V : View Validator BlockId Payload U} {R N : ℕ} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hs : SynchronisedOn U T R)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hV : V.CoversUpto N) :
    ∀ (h : ℕ) (x : ℕ → ℕ), R ≤ x 0 → (∀ i, i < h → FloorHop w U V (x i) (x (i + 1))) →
      S.leader (x h) ∈ T →
      (∀ j, j ≤ x h → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) →
      ∃ v, Decided w U V (x 0) v := fun h x hR hhop hlead hN =>
  Steelhead.floorChainDecides leastLinked_steelhead (commitsUnderSync_steelhead hw U) hid hT hcard
    hs hpop hV h x hR
    (fun i hi => (floorHopOf_iff (fun κ => by have := hw κ; omega)).mpr (hhop i hi)) hlead
    (hN _ le_rfl)

/-- **SH-MM6h.** SH6h at the pair's rule, at the constant wave. -/
theorem floorChainReachesReliable {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {ws n : ℕ} (hn : 0 < n) (hwr : ∀ κ, w κ = ws) (hws : 3 ≤ ws) (hid : ∀ t, S.slotRound t = t)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N) {lead : Fin n → Validator} (hbij : Function.Bijective lead)
    (hsched : ∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {x : ℕ → ℕ} (hR : R ≤ x 0) (hhop : ∀ i, i < n - T.card → FloorHop w U V (x i) (x (i + 1)))
    (hN : ∀ j, j ≤ x (n - T.card) →
      (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) :
    ∃ i, i ≤ n - T.card ∧ S.leader (x i) ∈ T := by
  have hw3 : ∀ κ, 3 ≤ w κ := fun κ => by rw [hwr κ]; exact hws
  exact Steelhead.floorChainReachesReliable hn (laws_of_three hw3)
    (commitsUnderSync_steelhead hw3 U)
    (fun t => by simp only [steelheadAnchored_waveAt, hwr]; omega) hid hT hcard hs hpop hV hbij
    hsched hlt hR (fun i hi => (floorHopOf_iff (fun κ => by have := hw3 κ; omega)).mpr (hhop i hi))
    hN

/-- **SH-MM6i.** SH6i at the pair's rule, at the constant wave. -/
theorem floorChainReachesReliableWithinByzantine {U : BlockUniverse Validator BlockId Payload}
    {w : ℕ → ℕ} {ws n : ℕ} (hn : 0 < n) (hwr : ∀ κ, w κ = ws) (hws : 3 ≤ ws)
    (hid : ∀ t, S.slotRound t = t) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {R N : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N)
    (hcrash : ∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R ≤ (U.block L).round → (U.block L).creator ≠ v)
    {lead : Fin n → Validator} (hbij : Function.Bijective lead)
    (hsched : ∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {x : ℕ → ℕ} (hR : R ≤ x 0) (hstart : ¬ Decided w U V (x 0) none)
    (hhop : ∀ i, i < F.byzantine.card → FloorHop w U V (x i) (x (i + 1)))
    (hN : ∀ j, j ≤ x F.byzantine.card →
      (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N) :
    ∃ i, i ≤ F.byzantine.card ∧ S.leader (x i) ∈ T := by
  have hw3 : ∀ κ, 3 ≤ w κ := fun κ => by rw [hwr κ]; exact hws
  exact Steelhead.floorChainReachesReliableWithinByzantine hn (laws_of_three hw3)
    (commitsUnderSync_steelhead hw3 U) (skipsSilent_steelhead hw3 U)
    (fun t => by simp only [steelheadAnchored_waveAt, hwr]; omega) hid hT hcard hs hpop hV hcrash
    hbij hsched hlt hR hstart
    (fun i hi => (floorHopOf_iff (fun κ => by have := hw3 κ; omega)).mpr (hhop i hi)) hN

/-- **SH-MM6j.** SH6j at the pair's rule, at the constant wave. -/
theorem floorChainDecidesWithinRounds {U : BlockUniverse Validator BlockId Payload}
    {w : ℕ → ℕ} {ws n : ℕ} (hn : 0 < n) (hwr : ∀ κ, w κ = ws) (hws : 3 ≤ ws)
    (hid : ∀ t, S.slotRound t = t) {T : Finset Validator} {V : View Validator BlockId Payload U}
    {R N : ℕ} (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N)
    (hcrash : ∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R ≤ (U.block L).round → (U.block L).creator ≠ v)
    {lead : Fin n → Validator} (hbij : Function.Bijective lead)
    (hsched : ∀ t, S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩) (hlt : ws * (n - T.card) < n)
    {k : ℕ} (hR : R ≤ k) (hstart : ¬ Decided w U V k none)
    (hN : k + (F.byzantine.card + 1) * (ws + (n - T.card)) ≤ N) :
    ∃ v, Decided w U V k v := by
  have hw3 : ∀ κ, 3 ≤ w κ := fun κ => by rw [hwr κ]; exact hws
  exact Steelhead.floorChainDecidesWithinRounds hn (laws_of_three hw3) leastLinked_steelhead
    (commitsUnderSync_steelhead hw3 U) (skipsSilent_steelhead hw3 U)
    (fun t => by simp only [steelheadAnchored_waveAt, hwr]; omega) hid hT hcard hs hpop hV hcrash
    hbij hsched hlt hR hstart hN

/-- **SH-MM6m.** SH6m at the pair's rule. -/
theorem floorChainDecidesFromCommit {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    (hw : ∀ r, 3 ≤ w r) (hid : ∀ t, S.slotRound t = t)
    {V : View Validator BlockId Payload U} :
    ∀ (h : ℕ) (x : ℕ → ℕ), (∀ i, i < h → FloorHop w U V (x i) (x (i + 1))) →
      (∃ A, Decided w U V (x h) (some A)) → ∃ v, Decided w U V (x 0) v := fun h x hhop hcom =>
  Steelhead.floorChainDecidesFromCommit leastLinked_steelhead hid h x
    (fun i hi => (floorHopOf_iff (fun κ => by have := hw κ; omega)).mpr (hhop i hi)) hcom

omit S in
/-- The pair's wave offsets at the two kinds. -/
theorem wavelength_waveAt_add_one {ws wa : ℕ} (hws : 1 ≤ ws) (hwa : 1 ≤ wa) :
    (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).waveAt 0 + 1 = ws ∧
      (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).waveAt 1 + 1 = wa := by
  simp only [steelheadAnchored_waveAt, wavelength_zero, wavelength_one]
  omega

/-- **SH-MM6o.** SH6o at the pair's rule, at the paper's dial. -/
theorem floorChainReachesAtPeriod {U : BlockUniverse Validator BlockId Payload}
    {ws wa p n : ℕ} (hn : 0 < n) (hp : 0 < p) (hws : 3 ≤ ws) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hkind : ∀ t, S.kind t = periodicKind p t)
    {lead : Fin n → Validator}
    (hsched : ∀ t, S.kind t = 0 → S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N) (hbij : Function.Bijective lead)
    (hlt : ws * (n - T.card) + ws * ((n + p - 1) / p) < n) {x : ℕ → ℕ}
    (hasync : ∀ t, x 0 ≤ t → S.kind t = 1 →
      ∃ v, Decided (wavelength ws wa) U V t v)
    (hR : R ≤ x 0) (hstart : ¬ Decided (wavelength ws wa) U V (x 0) none)
    (hhop : ∀ i, i < n - T.card → FloorHop (wavelength ws wa) U V (x i) (x (i + 1)))
    (hN : ∀ j, j ≤ x (n - T.card) →
      (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).decisionRound j ≤ N) :
    ∃ i, i ≤ n - T.card ∧
      (S.leader (x i) ∈ T ∨ ∃ A, Decided (wavelength ws wa) U V (x i) (some A)) := by
  have hw3 : ∀ κ, 3 ≤ wavelength ws wa κ := wavelength_three_le hws hwa
  exact Steelhead.floorChainReachesAtPeriod hn hp (laws_of_three hw3)
    (commitsUnderSync_steelhead hw3 U) (wavelength_waveAt_add_one (by omega) (by omega)).1 hid hkind
    hsched hT hcard hs hpop hV hbij hlt hasync hR hstart
    (fun i hi => (floorHopOf_iff (fun κ => by have := hw3 κ; omega)).mpr (hhop i hi)) hN

/-- **SH-MM6p.** SH6p at the pair's rule, at the paper's dial. -/
theorem floorChainDecidesWithinRoundsAtPeriod {U : BlockUniverse Validator BlockId Payload}
    {ws wa p n W : ℕ} (hn : 0 < n) (hp : 0 < p) (hws : 3 ≤ ws) (hwa : 3 ≤ wa)
    (hid : ∀ t, S.slotRound t = t) (hkind : ∀ t, S.kind t = periodicKind p t)
    {lead : Fin n → Validator}
    (hsched : ∀ t, S.kind t = 0 → S.leader t = lead ⟨t % n, Nat.mod_lt t hn⟩)
    {T : Finset Validator} {V : View Validator BlockId Payload U} {R N : ℕ}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hV : V.CoversUpto N)
    (hcrash : ∀ v, v ∉ T → v ∉ F.byzantine →
      ∀ L ∈ U.ids, R ≤ (U.block L).round → (U.block L).creator ≠ v)
    (hbij : Function.Bijective lead)
    (hlt : ws * (n - T.card) + ws * ((n + p - 1) / p) < n)
    (hwait : ∀ r, ∃ a, r ≤ a ∧ a ≤ r + W ∧ S.kind a = 0 ∧ S.leader a ∈ T) {k : ℕ}
    (hasync : ∀ t, k ≤ t → S.kind t = 1 → ∃ v, Decided (wavelength ws wa) U V t v)
    (hR : R ≤ k) (hstart : ¬ Decided (wavelength ws wa) U V k none)
    (hN : k + (F.byzantine.card + 1) * (ws + W) + wa ≤ N) :
    ∃ v, Decided (wavelength ws wa) U V k v := by
  have hw3 : ∀ κ, 3 ≤ wavelength ws wa κ := wavelength_three_le hws hwa
  have hwv := wavelength_waveAt_add_one (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) (show 1 ≤ ws by omega) (show 1 ≤ wa by omega)
  exact Steelhead.floorChainDecidesWithinRoundsAtPeriod hn hp (laws_of_three hw3)
    leastLinked_steelhead (commitsUnderSync_steelhead hw3 U) (skipsSilent_steelhead hw3 U) hwv.1
    hwv.2 hid hkind hsched hT hcard hs hpop hV hcrash hbij hlt hwait hasync hR hstart hN

/-- **SH-MM6l.** SH6l at the pair's rule, the whole prefix of the slot deciding below the
horizon. -/
theorem timed_commits {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {N N' k : ℕ}
    (vp : ViewPace U T N) (hw : ∀ κ, 3 ≤ w κ) (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card) (hrate : Rated vp.timeout)
    (hR : max (2 * vp.delay + vp.proc) vp.gst ≤ S.slotRound k)
    (hpop : ∀ r, max (2 * vp.delay + vp.proc) vp.gst ≤ r → r ≤ N' → PopulatedOn U T r)
    (hN : ∀ j, j ≤ k → (steelheadAnchored Validator BlockId Payload w).decisionRound j ≤ N')
    (hV : V.CoversUpto N') (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided w U V k (some L) :=
  Steelhead.commitsOfViewPace (commitsUnderSync_steelhead hw U) vp hT hcard hrate hR hpop
    (hN k le_rfl) hV hlead

/-! ## SH-MM6d — dissemination -/

omit S in
/-- A block reaching the only block of its author at a round votes for it: `Votes` asks for the
least candidate of that author and round in the cone, and there is one. -/
theorem votes_of_reaches_of_unique {U : BlockUniverse Validator BlockId Payload} {q L : BlockId}
    (hq : q ∈ U.ids) (hL : L ∈ U.ids)
    (huniq : ∀ L' ∈ U.ids, (U.block L').round = (U.block L).round →
      (U.block L').creator = (U.block L).creator → L' = L)
    (h : Reaches U q L) : MahiMahi.Votes U q L := by
  refine ⟨MahiMahi.mem_candidatesAt.mpr ⟨hL, rfl, rfl, (mem_history_iff hq).mpr h⟩, ?_⟩
  intro L' hL' hlt
  obtain ⟨hL'ids, hL'r, hL'c, -⟩ := MahiMahi.mem_candidatesAt.mp hL'
  rw [huniq L' hL'ids hL'r hL'c] at hlt
  exact lt_irrefl _ hlt

omit S [LinearOrder BlockId] in
/-- Under synchrony from `R`, a block one reliable round-`R` block references lies in the cone of
every reliable block at the rounds past `R` the reliable set populates: each reliable block
references every reliable block one round down, one of which reaches it. -/
theorem reaches_of_synchronised_of_ref {U : BlockUniverse Validator BlockId Payload}
    {T : Finset Validator} {R N : ℕ} {L q : BlockId} (hcard : quorumCard Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r)
    (hq : q ∈ U.ids) (hqr : (U.block q).round = R) (hqT : (U.block q).creator ∈ T)
    (hqL : L ∈ (U.block q).refs) :
    ∀ c ∈ U.ids, R + 1 ≤ (U.block c).round → (U.block c).round ≤ N →
      (U.block c).creator ∈ T → Reaches U c L := by
  suffices H : ∀ m, R + 1 ≤ m → m ≤ N → ∀ c ∈ U.ids, (U.block c).round = m →
      (U.block c).creator ∈ T → Reaches U c L by
    intro c hc h1 h2 hcT
    exact H _ h1 h2 c hc rfl hcT
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro _ c hc hcr hcT
    exact Reaches.trans (Reaches.single (hs R le_rfl c hc hcr hcT q hq hqr hqT))
      (Reaches.single hqL)
  | succ m hRm ih =>
    intro hmN c hc hcr hcT
    obtain ⟨v, hv⟩ := MahiMahi.nonempty_of_quorum hcard
    obtain ⟨b, hb, hbc, hbr⟩ := hpop m (by omega) (by omega) v hv
    exact Reaches.trans (Reaches.single (hs m (by omega) c hc hcr hcT b hb hbr (hbc ▸ hv)))
      (ih (by omega) b hb hbr (hbc ▸ hv))

/-- **SH6d.** Synchrony carries the candidate into every reliable cone from two rounds up; the
reliable voters vote for it, the leader's only block at its round; every reliable block at the
decision round references all of them and so certifies; and a view holding the decision round
holds those certificates. -/
theorem commitsOfDissemination {U : BlockUniverse Validator BlockId Payload} {w : ℕ → ℕ}
    {T : Finset Validator} {V : View Validator BlockId Payload U} {k : ℕ} {L q : BlockId}
    (hw : 4 ≤ w (S.kind k)) (hcard : quorumCard Validator ≤ T.card)
    (hL : IsLeaderBlock U k L)
    (huniq : ∀ L' ∈ U.ids, (U.block L').round = S.slotRound k →
      (U.block L').creator = S.leader k → L' = L)
    (hq : q ∈ U.ids) (hqr : (U.block q).round = S.slotRound k + 1) (hqT : (U.block q).creator ∈ T)
    (hqL : L ∈ (U.block q).refs) (hs : SynchronisedOn U T (S.slotRound k + 1))
    (hpop : ∀ r, S.slotRound k + 1 ≤ r →
      r ≤ MahiMahi.decisionRoundAt (w (S.kind k)) (S.slotRound k) → PopulatedOn U T r)
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt (w (S.kind k)) (S.slotRound k))) :
    Decided w U V k (some L) := by
  have hreach := reaches_of_synchronised_of_ref hcard hs hpop hq hqr hqT hqL
  have huniq' : ∀ L' ∈ U.ids, (U.block L').round = (U.block L).round →
      (U.block L').creator = (U.block L).creator → L' = L :=
    fun L' h1 h2 h3 => huniq L' h1 (h2.trans hL.2.1) (h3.trans hL.2.2)
  -- every reliable block at the decision round certifies L
  have hcert : ∀ C ∈ U.ids,
      (U.block C).round = MahiMahi.decisionRoundAt (w (S.kind k)) (S.slotRound k) →
      (U.block C).creator ∈ T →
      C ∈ MahiMahi.certificates U (w (S.kind k)) L (S.slotRound k) := by
    intro C hC hCr hCT
    refine mem_certificatesAt.mpr ⟨hC, hCr, ?_⟩
    unfold CarriesVotes
    refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
    obtain ⟨b, hb, hbc, hbr⟩ := hpop (MahiMahi.votingRound (w (S.kind k)) (S.slotRound k))
      (by unfold MahiMahi.votingRound; omega)
      (by unfold MahiMahi.votingRound MahiMahi.decisionRoundAt; omega) v hv
    refine mem_creatorsOf.mpr ⟨b, mem_carriedVotes.mpr ⟨?_, ?_⟩, hbc⟩
    · refine hs (MahiMahi.votingRound (w (S.kind k)) (S.slotRound k))
        (by unfold MahiMahi.votingRound; omega) C hC ?_ hCT b hb hbr (hbc ▸ hv)
      rw [hCr]
      unfold MahiMahi.votingRound MahiMahi.decisionRoundAt
      omega
    · refine votes_of_reaches_of_unique hb hL.1 huniq' (hreach b hb ?_ ?_ (hbc ▸ hv))
      · rw [hbr]; unfold MahiMahi.votingRound; omega
      · rw [hbr]; unfold MahiMahi.votingRound MahiMahi.decisionRoundAt; omega
  -- so L is directly committed, and the view holds the certificates
  have hdc : MahiMahi.DirectCommit U (w (S.kind k)) L (S.slotRound k) := by
    unfold MahiMahi.DirectCommit
    refine le_trans hcard (Finset.card_le_card fun v hv => ?_)
    obtain ⟨C, hC, hCc, hCr⟩ := hpop _ (by unfold MahiMahi.decisionRoundAt; omega) le_rfl v hv
    exact mem_creatorsOf.mpr ⟨C, hcert C hC hCr (hCc ▸ hv), hCc⟩
  exact Decided.directCommit hL (MahiMahiProperties.directCommitIn_of_coversUpto hdc hV)

end Slots

/-! ## SH7 — the chain

Stated at any schedule whose rounds strictly increase: the coin schedule and every control
schedule. Consecutive slots of such a schedule lie at least one round apart, so `wa` of them span
the wave, which is all the descent asks. -/

/-- A strictly increasing schedule puts slot `m` at least `m − i` rounds above slot `i`. -/
theorem slotRound_add_le_of_strictMono {S' : Slots Validator} (hmono : StrictMono S'.slotRound)
    {i m : ℕ} (h : i ≤ m) : S'.slotRound i + (m - i) ≤ S'.slotRound m := by
  have := hmono.add_le_nat (m - i) i
  rw [Nat.sub_add_cancel h] at this
  omega

/-- At a strictly increasing schedule a run of `wa` slots spans, at wave `wa`. -/
theorem spansEligible_of_strictMono {wa : ℕ} (hwa : 1 ≤ wa) {S' : Slots Validator}
    (hmono : StrictMono S'.slotRound) :
    (MahiMahi.mahiMahiAnchored Validator BlockId Payload wa).SpansEligible (S := S') wa := by
  intro b i hi
  rw [AnchoredRule.eligible_iff]
  simp only [MahiMahi.mahiMahiAnchored_waveAt]
  have := slotRound_add_le_of_strictMono hmono (show i ≤ b + wa - 1 by omega)
  omega

/-- **SH7c, at any strictly increasing schedule.** The core's descent below a run of direct
commits: the run's slots are led by committed candidates, so they commit directly, and a view
holding their decision rounds holds their certificates. -/
theorem allDecidedBelowOfGoodRun {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 1 ≤ wa) {S' : Slots Validator} (hmono : StrictMono S'.slotRound)
    {V : View Validator BlockId Payload U} {b : ℕ}
    (hgood : ∀ i, i < wa → S'.leader (b + i) ∈ MahiMahi.good (S := S') U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (S'.slotRound (b + wa - 1)))) :
    ∀ i, i < b → ∃ v, MahiMahi.Decided (S := S') wa U V i v := by
  refine AnchoredRule.decided_below_of_run (S := S')
    (fun hi h => MahiMahi.exists_least (S := S') hi h) hwa
    (spansEligible_of_strictMono hwa hmono)
    (Led := fun j => S'.leader j ∈ MahiMahi.good (S := S') U wa j) hgood
    fun j _ hj2 hj => ?_
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp hj
  refine ⟨L, MahiMahi.Decided.directCommit (S := S') ⟨hL, hLr, hLc⟩
    (MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono ?_))⟩
  have := S'.mono hj2
  unfold MahiMahi.decisionRoundAt
  omega

/-- **SH7c.** The descent at the coin schedule, the run named by rounds. -/
theorem chainAllDecidedBelowOfRun {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 1 ≤ wa) {coin : ℕ → Validator} {V : View Validator BlockId Payload U} {b : ℕ}
    (hgood : ∀ i, i < wa → coin (b + i) ∈ MahiMahi.goodAt U wa (b + i))
    (hV : V.CoversUpto (MahiMahi.decisionRoundAt wa (b + wa - 1))) :
    ∀ i, i < b → ∃ v, ChainDecided wa coin U V i v :=
  allDecidedBelowOfGoodRun hwa (S' := chainSlots coin) strictMono_id hgood hV

/-- **SH7a.** MM3c at a strictly increasing schedule, in any view caught up to the horizon: the
clause names a run past `k`, and SH7c settles everything below it. -/
theorem chainAllDecidedBelow {U : BlockUniverse Validator BlockId Payload} {wa : ℕ}
    (hwa : 1 ≤ wa) {S' : Slots Validator} (hmono : StrictMono S'.slotRound)
    {V : View Validator BlockId Payload U} {c N : ℕ}
    (hrun : MahiMahi.UnpredictableRunWithin (S := S') U wa c wa N) (hV : V.CoversUpto N) (k : ℕ)
    (hk : MahiMahi.decisionRoundAt wa (S'.slotRound (k + c + wa - 1)) ≤ N) :
    ∃ b, k ≤ b ∧ ∀ i, i < b → ∃ v, MahiMahi.Decided (S := S') wa U V i v := by
  obtain ⟨k', hk1, hk2, hgood⟩ := hrun k (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := S') hwa]; exact hk)
  refine ⟨k', hk1, allDecidedBelowOfGoodRun hwa hmono hgood (hV.mono ?_)⟩
  have := S'.mono (show k' + wa - 1 ≤ k + c + wa - 1 by omega)
  unfold MahiMahi.decisionRoundAt at hk ⊢
  omega

/-- **SH7b.** The timed descent at Mahi-Mahi's support, at a strictly increasing schedule. -/
theorem chainAllDecidedBelowOfSynchrony {wa : ℕ} (hwa : 4 ≤ wa) {S' : Slots Validator}
    (hmono : StrictMono S'.slotRound) {T : Finset Validator}
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : quorumCard Validator ≤ T.card)
    (fair : FairRunOn (S := S') T wa) (R k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S'.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
        (N : ℕ),
        SynchronisedOn U T R → (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) →
        V.CoversUpto N → MahiMahi.decisionRoundAt wa (S'.slotRound (b + wa - 1)) ≤ N →
        ∀ i, i < b → ∃ v, MahiMahi.Decided (S := S') wa U V i v := by
  have hd : Descends (MahiMahiProperties.mahiMahiRule (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) wa) S' wa :=
    Descends.of_indirect (MahiMahiProperties.indirect (by omega)) (by omega) fun b i hi => by
      change S'.slotRound i + wa ≤ S'.slotRound (b + wa - 1)
      have := slotRound_add_le_of_strictMono hmono (show i ≤ b + wa - 1 by omega)
      omega
  obtain ⟨b, hb, hRb, h⟩ := Timed.decidedBelow_of_fairRun (MahiMahiProperties.mmSupport wa)
    (MahiMahiProperties.mmSupport_ofCoverage hwa) (MahiMahiProperties.mmSupport_commits (by omega))
    hd (isQuorum_core hT hcard) fair R k
  refine ⟨b, hb, hRb, fun U V N hs hpop hV hN i hi => ?_⟩
  obtain ⟨v, hv⟩ := h V N hs hpop hV (fun j hj => by
    change S'.slotRound j + (wa - 1) ≤ N
    have := S'.mono (show j ≤ b + wa - 1 by omega)
    unfold MahiMahi.decisionRoundAt at hN
    omega) i hi
  exact ⟨v, hv.2.1⟩

/-! ## SH8 — the stall -/

section Stall

variable [S : Slots Validator] {U : BlockUniverse Validator BlockId Payload}
  {V : View Validator BlockId Payload U} {ws wa k : ℕ}

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Under a periodic schedule an asynchronous slot's round is a multiple of the period. -/
theorem isAsync_of_kind (hkind : ∀ s, S.kind s = periodicKind k s) {j : ℕ} (h : S.kind j = 1) :
    IsAsync k j :=
  periodicKind_eq_one_iff.mp (hkind j ▸ h)

/-- **A synchronous slot never commits** when no synchronous candidate of the slots `Q` names is
certified: the direct commit and the link both need a certificate. -/
theorem not_commit_sync_of_pred (hid : ∀ s, S.slotRound s = s) {Q : ℕ → Prop}
    (hcert : ∀ (j : ℕ) (L : BlockId), Q j → S.kind j = 0 → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅)
    {j : ℕ} {A : BlockId} (hQ : Q j) (hj : S.kind j = 0)
    (h : Decided (wavelength ws wa) U V j (some A)) : False := by
  have hne : (MahiMahi.certificates U ws A j).Nonempty := by
    cases h with
    | directCommit hL hc =>
      change MahiMahi.DirectCommitIn U V (wavelength ws wa (S.kind j)) A (S.slotRound j) at hc
      rw [hid, hj, wavelength_zero] at hc
      exact MahiMahi.certificates_nonempty_of_directCommit
        (MahiMahi.directCommit_of_directCommitIn hc)
    | indirectCommit _ _ _ _ _ _ _ hlink _ =>
      change MahiMahi.CertifiedIn U (wavelength ws wa (S.kind j)) _ A (S.slotRound j) at hlink
      rw [hid, hj, wavelength_zero] at hlink
      exact MahiMahi.certificates_nonempty_of_certifiedIn hlink
  rw [hcert j A hQ hj (AnchoredRule.isLeaderBlock_of_decided h)] at hne
  exact Finset.not_nonempty_empty hne

/-- **A synchronous slot never commits** when no synchronous candidate is
certified: the direct commit and the link both need a certificate. -/
theorem not_commit_sync (hid : ∀ s, S.slotRound s = s)
    (hcert : ∀ (j : ℕ) (L : BlockId), S.kind j = 0 → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅)
    {j : ℕ} {A : BlockId} (hj : S.kind j = 0)
    (h : Decided (wavelength ws wa) U V j (some A)) : False :=
  not_commit_sync_of_pred hid (Q := fun _ => True) (fun j L _ => hcert j L) trivial hj h

/-- An asynchronous round above `i + 1`, where `i ≡ k − 1`, lies a full
period above `i`: the arithmetic `omega` cannot do at a variable modulus. -/
theorem add_period_le_of_isAsync {i j : ℕ} (hk : 2 ≤ k) (hi : i % k = k - 1) (hj : IsAsync k j)
    (hij : i + 2 ≤ j) : i + k + 1 ≤ j := by
  unfold IsAsync at hj
  have hi' := Nat.div_add_mod i k
  have hj' := Nat.div_add_mod j k
  rw [hi] at hi'
  rw [hj] at hj'
  have hlt : k * (i / k + 1) < k * (j / k) := by
    have e : k * (i / k + 1) = k * (i / k) + k := by rw [Nat.mul_add, Nat.mul_one]
    omega
  have hq : i / k + 1 < j / k := Nat.lt_of_mul_lt_mul_left hlt
  have : k * (i / k + 2) ≤ k * (j / k) := Nat.mul_le_mul_left k hq
  rw [Nat.mul_add] at this
  omega

/-- **SH8, at the slots a view can decide.** Induction on the derivation: a class-`(k − 1)`
slot's direct verdicts are excluded outright, a synchronous anchor never commits, and an
asynchronous anchor leaves the class-`(k − 1)` slot one period up as an eligible slot between,
which must be skipped, which is the claim one period up. The certificate and skip hypotheses are
asked at the slots `Q` names, which every slot a derivation in `V` mentions satisfies; on a view
that reaches no further than some round, that is the slots below it. -/
theorem stall_of_pred (hws : 2 ≤ ws) (hk : ws ≤ k) (hid : ∀ s, S.slotRound s = s) {Q : ℕ → Prop}
    (hkind : ∀ s, Q s → S.kind s = periodicKind k s)
    (hQ : ∀ (j : ℕ) (v : Option BlockId), Decided (wavelength ws wa) U V j v → Q j)
    (hcert : ∀ (j : ℕ) (L : BlockId), Q j → S.kind j = 0 → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅)
    (hskip : ∀ j, Q j → S.kind j = 0 → ¬ MahiMahi.DirectSkipIn U V ws (S.leader j) j)
    {i : ℕ} (hi : i % k = k - 1) {v : Option BlockId}
    (h : Decided (wavelength ws wa) U V i v) : False := by
  have hk2 : 2 ≤ k := le_trans hws hk
  -- a class-(k − 1) slot the view names is synchronous
  have hsync_of_mod : ∀ {i : ℕ}, Q i → i % k = k - 1 → S.kind i = 0 := by
    intro i hQi hi
    rw [hkind i hQi]
    unfold periodicKind
    rw [if_neg]
    omega
  -- the middle slot of an asynchronous anchor's search is one period up
  have hmid_of_async : ∀ {i j : ℕ}, Q i → Q j → i % k = k - 1 → S.kind j = 1 →
      (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).Eligible i j →
      i < i + k ∧ i + k < j ∧
        (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).Eligible i (i + k) := by
    intro i j hQi hQj hi hj helig
    have hsync := hsync_of_mod hQi hi
    have hasync : IsAsync k j := periodicKind_eq_one_iff.mp (hkind j hQj ▸ hj)
    rw [AnchoredRule.eligible_iff] at helig ⊢
    simp only [steelheadAnchored_waveAt, hid, hsync, wavelength_zero] at helig ⊢
    have := add_period_le_of_isAsync hk2 hi hasync (by omega)
    omega
  revert hi
  induction h with
  | @directCommit j L hL hc =>
    intro hi
    have hQj := hQ j _ (Decided.directCommit hL hc)
    exact not_commit_sync_of_pred hid hcert hQj (hsync_of_mod hQj hi) (Decided.directCommit hL hc)
  | @directSkip j hs =>
    intro hi
    have hQj := hQ j none (Decided.directSkip hs)
    have hj := hsync_of_mod hQj hi
    change MahiMahi.DirectSkipIn U V (wavelength ws wa (S.kind j)) (S.leader j)
      (S.slotRound j) at hs
    rw [hid, hj, wavelength_zero] at hs
    exact hskip j hQj hj hs
  | @indirectCommit i j A L _ hkj helig hj hmid hi' hemp hL hlink hleast _ ihmid =>
    intro hi
    have hQi := hQ i _ (Decided.indirectCommit hkj helig hj hmid hi' hemp hL hlink hleast)
    by_cases hasync : S.kind j = 1
    · obtain ⟨h1, h2, h3⟩ := hmid_of_async hQi (hQ j _ hj) hi hasync helig
      exact ihmid (i + k) h1 h2 h3 (by rw [Nat.add_mod_right]; exact hi)
    · exact not_commit_sync_of_pred hid hcert (hQ j _ hj)
        (by rw [hkind j (hQ j _ hj)] at hasync ⊢; exact periodicKind_eq_zero_of_ne_one hasync) hj
  | @indirectSkip i j A hkj helig hj hmid hnone _ ihmid =>
    intro hi
    have hQi := hQ i _ (Decided.indirectSkip hkj helig hj hmid hnone)
    by_cases hasync : S.kind j = 1
    · obtain ⟨h1, h2, h3⟩ := hmid_of_async hQi (hQ j _ hj) hi hasync helig
      exact ihmid (i + k) h1 h2 h3 (by rw [Nat.add_mod_right]; exact hi)
    · exact not_commit_sync_of_pred hid hcert (hQ j _ hj)
        (by rw [hkind j (hQ j _ hj)] at hasync ⊢; exact periodicKind_eq_zero_of_ne_one hasync) hj

/-- **SH8.** `stall_of_pred` with nothing asked of the slots. -/
theorem stall (hws : 2 ≤ ws) (hk : ws ≤ k) (hid : ∀ s, S.slotRound s = s)
    (hkind : ∀ s, S.kind s = periodicKind k s)
    (hcert : ∀ (j : ℕ) (L : BlockId), S.kind j = 0 → IsLeaderBlock U j L →
      MahiMahi.certificates U ws L j = ∅)
    (hskip : ∀ j, S.kind j = 0 → ¬ MahiMahi.DirectSkipIn U V ws (S.leader j) j)
    {i : ℕ} (hi : i % k = k - 1) {v : Option BlockId}
    (h : Decided (wavelength ws wa) U V i v) : False :=
  stall_of_pred hws hk hid (Q := fun _ => True) (fun s _ => hkind s) (fun _ _ _ => trivial)
    (fun j L _ => hcert j L) (fun j _ => hskip j) hi h

end Stall

/-! ## SH-MM9 — the drain, period one, and the cost of an asynchronous slot -/

section Drain

variable [S : Slots Validator] {U : BlockUniverse Validator BlockId Payload}

/-- **SH-MM9a.** SH9a at the pair's rule, each slot at its own wave. -/
theorem allDecidedBelowOfRun {w : ℕ → ℕ} {wa : ℕ} {V : View Validator BlockId Payload U} {b : ℕ}
    (hw : ∀ s, 1 ≤ w (S.kind s)) (hle : ∀ s, w (S.kind s) ≤ wa) (hid : ∀ s, S.slotRound s = s)
    (hrun : ∀ i, i < wa → ∃ L, Decided w U V (b + i) (some L)) :
    ∀ i, i < b → ∃ v, Decided w U V i v :=
  Steelhead.allDecidedBelowOfRun leastLinked_steelhead
    (fun s => by simp only [steelheadAnchored_waveAt]; have := hw s; have := hle s; omega) hid hrun

/-- **SH9b.** SH7a's argument at the output schedule: the clause names a run of `wa` committed
leaders past `r`, each committed directly in a view holding its decision round, and the run
decides everything below it (SH9a). -/
theorem allDecidedBelowAtPeriodOne {ws wa : ℕ} (hwa : 1 ≤ wa) {V : View Validator BlockId Payload U}
    (hid : ∀ s, S.slotRound s = s) (hone : ∀ s, S.kind s = 1) {c N : ℕ}
    (hrun : MahiMahi.UnpredictableRunWithin (S := S) U wa c wa N) (hV : V.CoversUpto N) (r : ℕ)
    (hr : MahiMahi.decisionRoundAt wa (r + c + wa - 1) ≤ N) :
    ∃ b, r ≤ b ∧ ∀ i, i < b → ∃ v, Decided (wavelength ws wa) U V i v := by
  obtain ⟨k', hk1, hk2, hgood⟩ := hrun r (by
    rw [MahiMahi.mahiMahiAnchored_decisionRound (S := S) hwa, hid]; exact hr)
  refine ⟨k', hk1, allDecidedBelowOfRun (fun s => by rw [hone, wavelength_one]; exact hwa)
    (fun s => by rw [hone, wavelength_one]) hid fun i hi => ?_⟩
  obtain ⟨L, hL, hLr, hLc, hdc⟩ := MahiMahi.mem_goodAt.mp (hgood i hi)
  refine ⟨L, Decided.directCommit ⟨hL, hLr, hLc⟩ ?_⟩
  change MahiMahi.DirectCommitIn U V (wavelength ws wa (S.kind (k' + i))) L
    (S.slotRound (k' + i))
  rw [hone, wavelength_one]
  refine MahiMahiProperties.directCommitIn_of_coversUpto hdc (hV.mono ?_)
  rw [hid]
  unfold MahiMahi.decisionRoundAt at hr ⊢
  omega

/-- **SH-MM9c.** SH9c at the pair's rule, the synchronous slot there read at `fun _ => ws`. -/
theorem asyncSlotCost {ws wa k : ℕ} (hid : ∀ s, S.slotRound s = s)
    (hkind : ∀ s, S.kind s = periodicKind k s) (hws : 1 ≤ ws) (hwa : ws ≤ wa)
    {r : ℕ} (hr : S.kind r = 1) :
    (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).decisionRound (S := S) r =
      (steelheadAnchored Validator BlockId Payload (fun _ => ws)).decisionRound (S := S) r +
        (wa - ws) ∧
    ∀ i, 1 ≤ i → i < k →
      (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).decisionRound (S := S) r ≤
        (steelheadAnchored Validator BlockId Payload (wavelength ws wa)).decisionRound (S := S)
          (r + i) + (wa - ws - i) := by
  have hwv := wavelength_waveAt_add_one (Validator := Validator) (BlockId := BlockId)
    (Payload := Payload) hws (show 1 ≤ wa by omega)
  obtain ⟨h1, h2⟩ := Steelhead.asyncSlotCost hid hkind hwv.1 hwv.2 hwa hr
  refine ⟨?_, h2⟩
  rw [h1]
  unfold AnchoredRule.decisionRound
  simp only [steelheadAnchored_waveAt, hid]

end Drain

end MahiMahiPair

end Steelhead

end LeanDag
