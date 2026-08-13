import LeanDag.Adaptive.Liveness
import LeanDag.Odontoceti.Liveness

/-!
# Adaptive leaders under the two-round rule

The Odontoceti mirror of the arc, exhibiting that the adaptive layer is
rule-agnostic: the epoching, the induced instance, the policy and its
clauses are consumed *as found* — `AdaptivePolicy` and `PlacesRuns` are
the very objects of the Mysticeti development, protocol-free — and only
the decision relation is mirrored. `Odontoceti.DecidedWithin` carries
the canonicity clause of the two-round indirect commit through the
bound; its congruence transports the clause in both directions, the
candidate set being schedule-dependent only through `IsLeaderBlock`,
which the two protocols share. Agreement per epoch is O5
(`Odontoceti.decided_unique`) through the embedding, exactly as the
three-round side used M6; existence consumes O7 and the two-round
descent, with two populated rounds where Mysticeti needs three.
-/

namespace LeanDag

namespace Odontoceti

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

/-- The bounded two-round decision relation: `Odontoceti.Decided` with
every slot mentioned strictly below `B`, canonicity clause included. -/
inductive DecidedWithin (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (B : ℕ) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      k < B → IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      DecidedWithin U V B k (some L)
  /-- The direct rule blames every candidate. -/
  | directSkip {k : ℕ} :
      k < B → (∀ L, IsLeaderBlock U k L → DirectSkipIn U V L (S.slotRound k)) →
      DecidedWithin U V B k none
  /-- Anchored below the bound, the least candidate passing the indirect
  test is committed. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      IsLeaderBlock U k L → ThickLink U A L (S.slotRound k) →
      (∀ L', IsLeaderBlock U k L' → ThickLink U A L' (S.slotRound k) →
        ¬ L' < L) →
      DecidedWithin U V B k (some L)
  /-- Anchored below the bound, no candidate passes. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → j < B → Eligible Validator k j → DecidedWithin U V B j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → DecidedWithin U V B i none) →
      (∀ L, IsLeaderBlock U k L → ¬ ThickLink U A L (S.slotRound k)) →
      DecidedWithin U V B k none

namespace DecidedWithin

variable {V : View Validator BlockId Payload U} {B B' k : ℕ} {v : Option BlockId}

/-- Forgetting the bound: agreement for the bounded relation *is* O5. -/
theorem toDecided (h : DecidedWithin U V B k v) : Decided U V k v := by
  induction h with
  | directCommit _ hL hdc => exact Decided.directCommit hL hdc
  | directSkip _ hall => exact Decided.directSkip hall
  | indirectCommit hkj _ helig _ _ hL ht hmin ihj ihmid =>
      exact Decided.indirectCommit hkj helig ihj ihmid hL ht hmin
  | indirectSkip hkj _ helig _ _ hnone ihj ihmid =>
      exact Decided.indirectSkip hkj helig ihj ihmid hnone

/-- The bound relaxes upward. -/
theorem mono (h : DecidedWithin U V B k v) (hBB : B ≤ B') :
    DecidedWithin U V B' k v := by
  induction h with
  | directCommit hk hL hdc => exact directCommit (by omega) hL hdc
  | directSkip hk hall => exact directSkip (by omega) hall
  | indirectCommit hkj hj helig _ _ hL ht hmin ihj ihmid =>
      exact indirectCommit hkj (by omega) helig ihj
        (fun i h1 h2 h3 => ihmid i h1 h2 h3) hL ht hmin
  | indirectSkip hkj hj helig _ _ hnone ihj ihmid =>
      exact indirectSkip hkj (by omega) helig ihj
        (fun i h1 h2 h3 => ihmid i h1 h2 h3) hnone

/-- Two bounded verdicts agree — O5, through the embedding. -/
theorem agree {V₁ V₂ : View Validator BlockId Payload U} {B₁ B₂ k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : DecidedWithin U V₁ B₁ k v₁)
    (h₂ : DecidedWithin U V₂ B₂ k v₂) : v₁ = v₂ :=
  decided_unique h₁.toDecided V₂ v₂ h₂.toDecided

end DecidedWithin

/-- Congruence below the bound, canonicity clause included: the
candidate set reads the schedule only through `IsLeaderBlock`, which
transports in both directions at the decided slot. -/
theorem decidedWithin_congr {hinj : Function.Injective S.slotRound}
    {a₁ a₂ : ℕ → Validator} {V : View Validator BlockId Payload U} {B k : ℕ}
    {v : Option BlockId} (ha : ∀ m, m < B → a₁ m = a₂ m)
    (h : DecidedWithin (S := slotsOf hinj a₁) U V B k v) :
    DecidedWithin (S := slotsOf hinj a₂) U V B k v := by
  induction h with
  | @directCommit k L hk hL hdc =>
      exact DecidedWithin.directCommit (S := slotsOf hinj a₂) hk
        (isLeaderBlock_slotsOf_congr (ha k hk) hL) hdc
  | @directSkip k hk hall =>
      exact DecidedWithin.directSkip (S := slotsOf hinj a₂) hk
        (fun L hL => hall L (isLeaderBlock_slotsOf_congr (ha k hk).symm hL))
  | @indirectCommit k j A L hkj hj helig _ _ hL ht hmin ihj ihmid =>
      exact DecidedWithin.indirectCommit (S := slotsOf hinj a₂) hkj hj helig ihj
        (fun i h1 h2 h3 => ihmid i h1 h2 h3)
        (isLeaderBlock_slotsOf_congr (ha k (by omega)) hL) ht
        (fun L' hL' ht' =>
          hmin L' (isLeaderBlock_slotsOf_congr (ha k (by omega)).symm hL') ht')
  | @indirectSkip k j A hkj hj helig _ _ hnone ihj ihmid =>
      exact DecidedWithin.indirectSkip (S := slotsOf hinj a₂) hkj hj helig ihj
        (fun i h1 h2 h3 => ihmid i h1 h2 h3)
        (fun L hL => hnone L (isLeaderBlock_slotsOf_congr (ha k (by omega)).symm hL))

/-- A run closed up to epoch height `E`, two-round rule. -/
structure PartialRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (E : ℕ) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot of a closed epoch is decided inside its window. -/
  closed : ∀ k, epochOf P.W k < E →
    DecidedWithin (S := slotsOf P.inj assign) U V
      (P.W * (epochOf P.W k + 2)) k (vdct k)
  /-- The assignment is the policy's, as far as the derivations read it. -/
  coherent : ∀ m, epochOf P.W m < E + 1 → assign m = P.pick U vdct m

/-- A total run: the adaptive fixpoint, two-round rule. -/
structure AdaptiveRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot is decided inside its epoch window. -/
  closed : ∀ k, DecidedWithin (S := slotsOf P.inj assign) U V
    (P.W * (epochOf P.W k + 2)) k (vdct k)
  /-- The assignment is the policy's, everywhere. -/
  coherent : ∀ m, assign m = P.pick U vdct m

/-- A total run is partial at every height. -/
def AdaptiveRun.toPartial {P : AdaptivePolicy Validator BlockId Payload}
    {V : View Validator BlockId Payload U} (R : AdaptiveRun P U V) (E : ℕ) :
    PartialRun P U V E where
  assign := R.assign
  vdct := R.vdct
  closed := fun k _ => R.closed k
  coherent := fun m _ => R.coherent m

/-- The master agreement lemma, two-round rule — the Mysticeti induction
verbatim, with O5 where it used M6. -/
theorem partialRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U} {E₁ E₂ : ℕ}
    (R₁ : PartialRun P U V₁ E₁) (R₂ : PartialRun P U V₂ E₂) :
    ∀ k, epochOf P.W k < min E₁ E₂ → R₁.vdct k = R₂.vdct k := by
  suffices main : ∀ e k, epochOf P.W k = e → epochOf P.W k < min E₁ E₂ →
      R₁.vdct k = R₂.vdct k by
    intro k hk; exact main _ k rfl hk
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro k hke hk
    have hassign : ∀ m, m < P.W * (epochOf P.W k + 2) →
        R₁.assign m = R₂.assign m := by
      intro m hm
      have hme : epochOf P.W m < epochOf P.W k + 2 :=
        (epochOf_lt_iff P.W_pos).mpr hm
      rw [R₁.coherent m (by omega), R₂.coherent m (by omega)]
      refine P.adapted U R₁.vdct R₂.vdct m (fun j hj => ?_)
      exact ih (epochOf P.W j) (by omega) j rfl (by omega)
    have h₁ := R₁.closed k (by omega)
    have h₂ := R₂.closed k (by omega)
    exact DecidedWithin.agree (S := slotsOf P.inj R₂.assign)
      (decidedWithin_congr hassign h₁) h₂

/-- **Safety, two-round rule: the adaptive fixpoint is unique** — with
no fairness, synchrony or view hypothesis, exactly as on the
three-round side. -/
theorem adaptiveRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) :
    ∀ k, R₁.vdct k = R₂.vdct k := fun k =>
  partialRun_agree (R₁.toPartial (epochOf P.W k + 1))
    (R₂.toPartial (epochOf P.W k + 1)) k (by omega)

section Existence

variable {P : AdaptivePolicy Validator BlockId Payload}
variable {T : Finset Validator} {c R N : ℕ}

/-- The committed-run descent, bounded — the base `Odontoceti` descent
with the anchor's bound carried through, least-candidate selection
included. -/
theorem decidedWithin_below_of_committed_run
    {V : View Validator BlockId Payload U} {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B', DecidedWithin U V (n + 1) j (some B')) :
    ∀ i, i < b → ∃ v, DecidedWithin U V (n + 1) i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, DecidedWithin U V (n + 1) i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      have hex : ∃ j, Eligible Validator i j ∧
          ∃ B', DecidedWithin U V (n + 1) j (some B') :=
        ⟨n, hspan i hi, hrun n hbn (le_refl n)⟩
      have hle : Nat.find hex ≤ n :=
        Nat.find_le ⟨hspan i hi, hrun n hbn (le_refl n)⟩
      obtain ⟨helig, B', hB⟩ := Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < Nat.find hex → Eligible Validator i i' →
          DecidedWithin U V (n + 1) i' none := by
        intro i' h1 h2 h3
        have hnc : ¬ ∃ C, DecidedWithin U V (n + 1) i' (some C) :=
          fun hc => Nat.find_min hex h2 ⟨h3, hc⟩
        have hi'b : i' < b := by
          by_contra hge
          exact hnc (hrun i' (by omega) (by omega))
        obtain ⟨v, hv⟩ := ih i' hi'b (by omega)
        cases v with
        | none => exact hv
        | some C => exact absurd ⟨C, hv⟩ hnc
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ ThickLink U B' L (S.slotRound i)
      · have hCne : (U.ids.filter fun L => IsLeaderBlock U i L ∧
            ThickLink U B' L (S.slotRound i)).Nonempty := by
          obtain ⟨L, hL, ht⟩ := hc
          exact ⟨L, Finset.mem_filter.mpr ⟨hL.1, hL, ht⟩⟩
        have hmem := Finset.min'_mem _ hCne
        rw [Finset.mem_filter] at hmem
        refine ⟨some ((U.ids.filter fun L => IsLeaderBlock U i L ∧
            ThickLink U B' L (S.slotRound i)).min' hCne),
          DecidedWithin.indirectCommit (lt_of_eligible helig) (by omega)
            helig hB hmid hmem.2.1 hmem.2.2 ?_⟩
        intro L' hL' ht' hlt
        exact absurd hlt (not_lt.mpr (Finset.min'_le _ L'
          (Finset.mem_filter.mpr ⟨hL'.1, hL', ht'⟩)))
      · push Not at hc
        exact ⟨none, DecidedWithin.indirectSkip (lt_of_eligible helig)
          (by omega) helig hB hmid hc⟩
  intro i hi
  exact key (b - i) i hi (le_refl _)

/-- One epoch closes, two-round rule: O7 commits the placed run — two
populated rounds where Mysticeti needs three — and the bounded descent
clears the epoch below. -/
theorem epoch_closes (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible Validator c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (v : ℕ → Option BlockId) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 2)) + 1 ≤ N) :
    ∀ k, epochOf P.W k < E + 1 →
      ∃ w, DecidedWithin (S := slotsOf P.inj (fun m => P.pick U v m)) U
        (View.full U) (P.W * (E + 2)) k w := by
  obtain ⟨b, hb1, hb2, hbT⟩ := hruns U v E
  have hWpos := P.W_pos
  have hrun : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B', DecidedWithin (S := slotsOf P.inj (fun m => P.pick U v m)) U
        (View.full U) (b + c - 1 + 1) j (some B') := by
    intro j hj1 hj2
    have hlead : (slotsOf P.inj (fun m => P.pick U v m)).leader j ∈ T := by
      have := hbT (j - b) (by omega)
      rw [slotsOf_leader]
      have hjb : b + (j - b) = j := by omega
      rwa [hjb] at this
    have hWle : P.W ≤ j := by
      have h1 : P.W * 1 ≤ P.W * (E + 1) := Nat.mul_le_mul_left P.W (by omega)
      omega
    have hRj : R ≤ S.slotRound j := le_trans hRW (S.mono hWle)
    have hround : S.slotRound j + 1 ≤ N := by
      have hj3 : j ≤ P.W * (E + 2) := by omega
      have := S.mono hj3
      omega
    obtain ⟨L, hL, hdc⟩ :=
      directCommit_of_leader_mem (S := slotsOf P.inj (fun m => P.pick U v m))
        hcard hs hRj
        (hpop _ (by omega) (by omega))
        (hpop _ (by omega) (by omega)) hlead
    exact ⟨L, DecidedWithin.directCommit
      (S := slotsOf P.inj (fun m => P.pick U v m)) (by omega) hL
      (directCommitIn_full hdc)⟩
  have hbelow :=
    decidedWithin_below_of_committed_run (V := View.full U)
      (S := slotsOf P.inj (fun m => P.pick U v m))
      (b := b) (n := b + c - 1) (by omega)
      (fun i hi => hspans b i hi) hrun
  intro k hk
  have hkb : k < b :=
    lt_of_lt_of_le ((epochOf_lt_iff hWpos).mp hk) hb1
  obtain ⟨w, hw⟩ := hbelow k hkb
  exact ⟨w, DecidedWithin.mono (S := slotsOf P.inj (fun m => P.pick U v m))
    hw (by omega)⟩

/-- Partial runs exist at every height, two-round rule. -/
theorem exists_partialRun (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible Validator c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (E : ℕ)
    (hN : S.slotRound (P.W * (E + 1)) + 1 ≤ N) :
    Nonempty (PartialRun P U (View.full U) E) := by
  classical
  revert hN
  induction E with
  | zero =>
      intro hN
      exact ⟨{ assign := fun m => P.pick U (fun _ => none) m
               vdct := fun _ => none
               closed := fun k hk => absurd hk (by omega)
               coherent := fun _ _ => rfl }⟩
  | succ E ih =>
      intro hN
      have hNprev : S.slotRound (P.W * (E + 1)) + 1 ≤ N := by
        have hmul : P.W * (E + 1) ≤ P.W * (E + 1 + 1) :=
          Nat.mul_le_mul_left P.W (by omega)
        have := S.mono hmul
        omega
      obtain ⟨R₀⟩ := ih hNprev
      have hclose := epoch_closes hT hcard hc hruns hspans hs hRW hpop
        R₀.vdct E hN
      set v' : ℕ → Option BlockId := fun k =>
        if h : epochOf P.W k = E then (hclose k (by omega)).choose
        else R₀.vdct k with hv'
      have hagree : ∀ j, epochOf P.W j < E → v' j = R₀.vdct j := by
        intro j hj
        simp only [hv', dif_neg (by omega : ¬ epochOf P.W j = E)]
      have hsched : ∀ m, m < P.W * (E + 2) →
          P.pick U R₀.vdct m = P.pick U v' m := by
        intro m hm
        refine P.adapted U R₀.vdct v' m (fun j hj => ?_)
        have hjE : epochOf P.W j < E := by
          have := (epochOf_lt_iff P.W_pos).mpr hm
          omega
        exact (hagree j hjE).symm
      refine ⟨{ assign := fun m => P.pick U v' m
                vdct := v'
                closed := ?_
                coherent := fun _ _ => rfl }⟩
      intro k hk
      by_cases hkE : epochOf P.W k = E
      · have hspec := (hclose k (by omega)).choose_spec
        have : v' k = (hclose k (by omega)).choose := by
          simp only [hv', dif_pos hkE]
        rw [this, hkE]
        exact decidedWithin_congr (fun m hm => hsched m hm) hspec
      · have hkE' : epochOf P.W k < E := by omega
        have hold := R₀.closed k hkE'
        have hsched' : ∀ m, m < P.W * (epochOf P.W k + 2) →
            R₀.assign m = P.pick U v' m := by
          intro m hm
          have hmE : epochOf P.W m < epochOf P.W k + 2 :=
            (epochOf_lt_iff P.W_pos).mpr hm
          rw [R₀.coherent m (by omega)]
          refine P.adapted U R₀.vdct v' m (fun j hj => ?_)
          exact (hagree j (by omega)).symm
        have := decidedWithin_congr hsched' hold
        rw [hagree k hkE']
        exact this

/-- **AL7: adaptive Odontoceti is safe and live.** The fixpoint exists
on the full view — glued along the diagonal exactly as on the
three-round side — and by `Odontoceti.adaptiveRun_agree` it is unique. -/
theorem adaptiveRun_exists (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (hc : 0 < c) (hruns : PlacesRuns P T c)
    (hspans : SpansEligible Validator c)
    (hs : SynchronisedOn U T R) (hRW : R ≤ S.slotRound P.W)
    (hpop : ∀ r, Populated U r) :
    Nonempty (AdaptiveRun P U (View.full U)) := by
  classical
  have hex : ∀ E, Nonempty (PartialRun P U (View.full U) E) := fun E =>
    exists_partialRun hT hcard hc hruns hspans hs hRW
      (N := S.slotRound (P.W * (E + 1)) + 1) (fun r _ _ => PopulatedOn.mono hT (hpop r)) E (le_refl _)
  set Rs : ∀ E, PartialRun P U (View.full U) E :=
    fun E => (hex E).some with hRs
  set vd : ℕ → Option BlockId := fun k => (Rs (epochOf P.W k + 1)).vdct k with hvd
  have hdiag : ∀ E j, epochOf P.W j < E → (Rs E).vdct j = vd j := by
    intro E j hj
    exact partialRun_agree (Rs E) (Rs (epochOf P.W j + 1)) j (by omega)
  refine ⟨{ assign := fun m => P.pick U vd m
            vdct := vd
            closed := ?_
            coherent := fun _ => rfl }⟩
  intro k
  have hclosed := (Rs (epochOf P.W k + 1)).closed k (by omega)
  refine decidedWithin_congr (fun m hm => ?_) hclosed
  have hmE : epochOf P.W m < epochOf P.W k + 2 := (epochOf_lt_iff P.W_pos).mpr hm
  rw [(Rs (epochOf P.W k + 1)).coherent m (by omega)]
  refine P.adapted U (Rs (epochOf P.W k + 1)).vdct vd m (fun j hj => ?_)
  exact hdiag _ j (by omega)

end Existence

end Odontoceti

end LeanDag
