import LeanDag.Hybrid.Decision
import LeanDag.Liveness
import Mathlib.Data.Finset.Max

/-!
# Hybrid liveness

H7: the Odontoceti liveness chain at the hybrid quorum, over the
`T`-relativised interface consumed exactly as the base development
states it — `T ⊆ Correct` now excludes the crash-prone through the
derived instance, `q ≤ T.card` is satisfiable because the fully-correct
class numbers at least `q`, and coverage (`SynchronisedOn`) and
production (`Populated`) never mention a leader or a fault class.

Note what liveness does *not* need: `HonestNoEquiv` appears nowhere —
no liveness argument counts an equivocator — and the indirect threshold
`k` is unconstrained, every step below holding at *any* `k`. Only
agreement prices the threshold; the committed-run descent merely
selects the least candidate passing whatever test is in force, which is
exactly what the canonicity premise asks for.

At the tight committee `n = 5·fb + 3·fc + 1` the correct class is
exactly `q`: the reliable set must be *all* of it, the hybrid analogue
of the base development's remark that at `f = 1` every correct
validator is needed for a quorum.
-/

namespace LeanDag

namespace Hybrid

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {L : BlockId} {s R N k : ℕ}

/-- The fully-correct class carries the hybrid quorum: liveness's card
hypothesis is satisfiable at `T := Correct`, with equality at the tight
committee. -/
theorem q_le_card_correct : q Validator ≤ (Correct : Finset Validator).card := by
  have h1 := card_correct_add_byzantine (Validator := Validator)
  have h2 : (Faults.byzantine (Validator := Validator)).card ≤ H.fb + H.fc :=
    Faults.card_byzantine
  unfold q
  omega

/-! ## H7a — a reliable leader commits directly, in one step -/

/-- **H7, commit half (O7's mirror).** Post-`R`, a `T`-led slot is
directly committed: coverage makes every `T` block at the decision
round reference the leader's block, and `T` carries the quorum. Two
populated rounds — propose and decide. -/
theorem directCommit_of_leader_mem
    (hcard : q Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ DirectCommit U L (S.slotRound s) := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop0 (S.leader s) hlead
  refine ⟨L, ⟨hL, hLr, hLc⟩, ?_⟩
  have hsub : T ⊆ supporters U L (S.slotRound s + 1) := by
    intro w hw
    obtain ⟨b, hb, hbc, hbr⟩ := hpop1 w hw
    refine mem_supporters.mpr ⟨b, hb, hbr, ?_, hbc⟩
    exact hs (S.slotRound s) hR b hb hbr (by rw [hbc]; exact hw)
      L hL hLr (by rw [hLc]; exact hlead)
  exact le_trans hcard (Finset.card_le_card hsub)

/-- The full view sees every supporter. -/
theorem supportersIn_full {r : ℕ} :
    supportersIn U (View.full U) L r = supporters U L (r + 1) := by
  unfold supportersIn supporters
  congr 1
  refine Finset.inter_eq_left.mpr ?_
  intro p hp
  exact (mem_blocksAt.mp (Finset.mem_filter.mp hp).1).1

theorem directCommitIn_full {r : ℕ} (h : DirectCommit U L r) :
    DirectCommitIn U (View.full U) L r := by
  rw [DirectCommitIn, supportersIn_full]
  exact h

/-- **H7, as a decision** — at every threshold `k`. -/
theorem decided_of_leader_mem
    (hcard : q Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided k U (View.full U) s (some L) := by
  obtain ⟨L, hLb, hdc⟩ :=
    directCommit_of_leader_mem hcard hs hR hpop0 hpop1 hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_full hdc)⟩

/-- H7 against a horizon: two rounds read off it. -/
theorem decided_of_leader_of_populated (hT : T ⊆ (Correct : Finset Validator))
    (hcard : q Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop : ∀ r ≤ N, Populated U r) (hN : S.slotRound s + 1 ≤ N)
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided k U (View.full U) s (some L) :=
  decided_of_leader_mem hcard hs hR
    (PopulatedOn.mono hT (hpop _ (by omega)))
    (PopulatedOn.mono hT (hpop _ (by omega))) hlead

/-! ## H7b — a run of two spans eligibility -/

variable (Validator) in
/-- A run of `c` slots reaches past everything below it. -/
def SpansEligible (c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator i (b + c - 1)

omit [Fintype Validator] [DecidableEq Validator] H in
/-- Under a pipelined identity-round schedule, `c = 2` spans — two
consecutive reliable leaders, exactly as in the pure-Byzantine
two-round development. -/
theorem spansEligible_two (hid : ∀ s, S.slotRound s = s) :
    SpansEligible Validator 2 := by
  intro b i hi
  rw [eligible_iff, hid, hid]
  omega

/-! ## H7c — a committed run clears everything below it -/

/-- **The committed-run descent (O9's mirror).** Every slot below a
committed run of eligible span is decided, at every threshold `k`:
anchor each slot on the nearest eligible committed slot above it and
commit the least candidate passing the indirect test — exactly the
canonicity premise. -/
theorem decided_below_of_committed_run
    {V : View Validator BlockId Payload U} {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B, Decided k U V j (some B)) :
    ∀ i, i < b → ∃ v, Decided k U V i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, Decided k U V i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      have hex : ∃ j, Eligible Validator i j ∧ ∃ B, Decided k U V j (some B) :=
        ⟨n, hspan i hi, hrun n hbn (le_refl n)⟩
      obtain ⟨helig, B, hB⟩ := Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < Nat.find hex →
          Eligible Validator i i' → Decided k U V i' none := by
        intro i' h1 h2 h3
        have hnc : ¬ ∃ C, Decided k U V i' (some C) := fun hc =>
          Nat.find_min hex h2 ⟨h3, hc⟩
        have hi'b : i' < b := by
          by_contra hge
          have hle : Nat.find hex ≤ n :=
            Nat.find_le ⟨hspan i hi, hrun n hbn (le_refl n)⟩
          exact hnc (hrun i' (by omega) (by omega))
        obtain ⟨v, hv⟩ := ih i' hi'b (by omega)
        cases v with
        | none => exact hv
        | some C => exact absurd ⟨C, hv⟩ hnc
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ ThickLink k U B L (S.slotRound i)
      · -- commit a minimal passing candidate
        have hCne : (U.ids.filter fun L => IsLeaderBlock U i L ∧
            ThickLink k U B L (S.slotRound i)).Nonempty := by
          obtain ⟨L, hL, ht⟩ := hc
          exact ⟨L, Finset.mem_filter.mpr ⟨hL.1, hL, ht⟩⟩
        have hmem := Finset.min'_mem _ hCne
        rw [Finset.mem_filter] at hmem
        refine ⟨some ((U.ids.filter fun L => IsLeaderBlock U i L ∧
            ThickLink k U B L (S.slotRound i)).min' hCne),
          Decided.indirectCommit (lt_of_eligible helig)
            helig hB hmid hmem.2.1 hmem.2.2 ?_⟩
        intro L' hL' ht' hlt
        exact absurd hlt (not_lt.mpr (Finset.min'_le _ L'
          (Finset.mem_filter.mpr ⟨hL'.1, hL', ht'⟩)))
      · push Not at hc
        exact ⟨none, Decided.indirectSkip (lt_of_eligible helig) helig hB
          hmid hc⟩
  intro i hi
  exact key (b - i) i hi (le_refl _)

/-! ## H7 — liveness, composed -/

/-- **H7 (O10's mirror).** Under post-`R` coverage, growth to the
horizon, and a recurring run of `c` reliable-led slots, every slot
below the run is decided — at every threshold `k`, the run placed past
both the target and `R` by fairness. The reliable set excludes the
crash-prone by construction: `T ⊆ Correct` reads through the derived
instance. -/
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : q Validator ≤ T.card)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn T c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r ≤ N, Populated U r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Decided k U (View.full U) i v := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨b, hb, hrunT⟩ := fair (max s k₀)
  have hRb : R ≤ S.slotRound b :=
    le_trans hk₀ (S.mono (le_trans (le_max_right s k₀) hb))
  refine ⟨b, le_trans (le_max_left _ _) hb, hRb, ?_⟩
  intro U N hpop hs hN
  have hrun : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B, Decided k U (View.full U) j (some B) := by
    intro j hj1 hj2
    have hlead : S.leader j ∈ T := by
      have := hrunT (j - b) (by omega)
      rwa [Nat.add_sub_cancel' hj1] at this
    have hRj : R ≤ S.slotRound j := le_trans hRb (S.mono hj1)
    have hjr : S.slotRound j ≤ S.slotRound (b + c - 1) := S.mono (by omega)
    obtain ⟨L, _, hdec⟩ :=
      decided_of_leader_of_populated hT hcard hs hRj hpop (by omega) hlead
    exact ⟨L, hdec⟩
  exact decided_below_of_committed_run (by omega)
    (fun i hi => hspan b i hi) hrun

/-- **H7 at `T := Correct`** — the whole fully-correct class, which the
tight committee requires exactly. -/
theorem all_decided_below_of_fairRun_correct {c : ℕ} (hc : 0 < c)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn (Correct : Finset Validator) c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r ≤ N, Populated U r) → Synchronised U R →
        S.slotRound (b + c - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Decided k U (View.full U) i v :=
  all_decided_below_of_fairRun hc Finset.Subset.rfl q_le_card_correct hspan
    fair R s

end Hybrid

end LeanDag
