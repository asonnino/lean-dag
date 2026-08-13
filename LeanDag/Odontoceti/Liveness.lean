import LeanDag.Odontoceti.Decision
import Mathlib.Data.Finset.Max

/-!
# Odontoceti: liveness

`odontoceti.md` §5, OP4 — O7 through O10. The two-round rule's liveness
is *simpler* than Mysticeti's, which is the protocol's whole point:

* **O7** (`directCommit_of_leader_mem`, `decided_of_leader_mem`) —
  post-`R`, a correct leader's block is referenced by every correct
  decision-round block (`SynchronisedOn`, one step), so its supporters
  include a full quorum: **two** populated rounds against Mysticeti's
  three.
* **O8** (`SpansEligible`, `spansEligible_two`) — under a pipelined
  identity-round schedule a run of **two** consecutive committed slots
  spans eligibility for everything below: a slot cannot anchor on the
  round immediately above it, but the second slot of the run clears
  `slotRound + 2`. Two consecutive honest leaders is the thesis's
  Lemma 10; the schedule fact itself is hypothesized (`FairRunOn`), in
  house style.
* **O9** (`decided_below_of_committed_run`) — a run of committed slots
  clears every slot below it, by the nearest-eligible-committed-anchor
  induction. The indirect commit picks the **least** passing candidate
  (`Finset.min'`), which is exactly what the canonicity premise of
  `Decided.indirectCommit` asks for.
* **O10** (`all_decided_below_of_fairRun`) — the composition, under
  enforceable hypotheses only: `Live`, `DeliversQuorum`,
  `SynchronisedOn`, and a recurring run of `c` correct-led slots. Note
  the horizon: the run's last slot needs rounds up to
  `slotRound + 1` — one round of certificates fewer than Mysticeti's
  `+ 2`.
-/

namespace LeanDag

namespace Odontoceti

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {L : BlockId} {k R N : ℕ}

/-! ## O7 — honest leaders commit directly, in one step -/

/-- **The commit argument, stated once** — the two-round counterpart of
`directCommit_of_certifiesAt`. A quorum-sized `T` whose blocks one round
above `r` all vote for `L` directly commits it: a vote *is* a support,
each `v ∈ T` has a supporting block by production, and `T`'s cardinality
does the counting. Both pacing disciplines end here — the full-timeout
one arriving through `votesAt_of_synchronisedOn`, the reactive one
through `ReactivePace.votes`. -/
theorem directCommit_of_votesAt {r : ℕ}
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hpop1 : PopulatedOn U T (r + 1))
    (hv : VotesAt U T r L) :
    DirectCommit U L r := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨b, hb, hbc, hbr⟩ := hpop1 w hw
  exact mem_supporters.mpr ⟨b, hb, hbr, hv w hw b hb hbc hbr, hbc⟩

/-- **O7, commit half (thesis Lemma 8 + Corollary 9).** Post-`R`, a
`T`-led slot is directly committed: `SynchronisedOn` makes every `T`
block at the decision round reference the leader's block, and `T`
carries a quorum. Two populated rounds — propose and decide — and one
synchronised step, routed through the targeted interface. -/
theorem directCommit_of_leader_mem
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop0 (S.leader k) hlead
  exact ⟨L, ⟨hL, hLr, hLc⟩,
    directCommit_of_votesAt hcard hpop1
      (votesAt_of_synchronisedOn hs hR hL hLr (by rw [hLc]; exact hlead))⟩

/-- The full view sees every supporter. -/
theorem supportersIn_full {r : ℕ} :
    supportersIn U (View.full U) L r = supporters U L (r + 1) := by
  unfold supportersIn supporters
  congr 1
  refine Finset.inter_eq_left.mpr ?_
  intro q hq
  exact (mem_blocksAt.mp (Finset.mem_filter.mp hq).1).1

theorem directCommitIn_full {r : ℕ} (h : DirectCommit U L r) :
    DirectCommitIn U (View.full U) L r := by
  rw [DirectCommitIn, supportersIn_full]
  exact h

/-- **O7, as a decision.** -/
theorem decided_of_leader_mem
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLb, hdc⟩ :=
    directCommit_of_leader_mem hcard hs hR hpop0 hpop1 hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_full hdc)⟩

/-- **O7 against a horizon**, the two-round counterpart of
`decided_of_leader_of_populated`: the rule needs the leader's round and
the one above it, so two rounds are read off the horizon rather than
three. -/
theorem decided_of_leader_of_populated (_hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop : ∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_leader_mem hcard hs hR
    (hpop _ (by omega) (by omega)) (hpop _ (by omega) (by omega)) hlead

/-- The same at `T := Correct`. -/
theorem decided_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_leader_mem card_correct hs hR hpop0 hpop1 hlead

/-! ## O8 — a run of two spans eligibility -/

variable (Validator) in
/-- A run of `c` slots reaches past everything below it: the last slot
of a run starting at `b` is an eligible anchor for every slot below
`b`. -/
def SpansEligible (c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator i (b + c - 1)

omit [Fintype Validator] [DecidableEq Validator] F in
/-- **O8.** Under a pipelined identity-round schedule, `c = 2` spans:
slot `b − 1` cannot anchor on slot `b` — one round is one too close —
but slot `b + 1` clears `slotRound + 2`. This is why the thesis's
Lemma 10 asks for **two consecutive** honest leaders. -/
theorem spansEligible_two (hid : ∀ k, S.slotRound k = k) :
    SpansEligible Validator 2 := by
  intro b i hi
  rw [eligible_iff, hid, hid]
  omega

/-! ## O9 — a committed run clears everything below it -/

/-- **O9 (thesis Lemma 11).** Every slot below a committed run of
eligible span is decided: walk down from the run, anchoring each slot
on the nearest eligible committed slot above it — whose intermediate
premise the induction supplies — and commit the **least** candidate
passing the indirect test, exactly what the canonicity premise asks
for. -/
theorem decided_below_of_committed_run
    {V : View Validator BlockId Payload U} {b n : ℕ} (hbn : b ≤ n)
    (hspan : ∀ i, i < b → Eligible Validator i n)
    (hrun : ∀ j, b ≤ j → j ≤ n → ∃ B, Decided U V j (some B)) :
    ∀ i, i < b → ∃ v, Decided U V i v := by
  classical
  have key : ∀ d i, i < b → b - i ≤ d → ∃ v, Decided U V i v := by
    intro d
    induction d with
    | zero => intro i hi hd; omega
    | succ d ih =>
      intro i hi hd
      -- the nearest slot above `i` that is both eligible for it and committed
      have hex : ∃ j, Eligible Validator i j ∧ ∃ B, Decided U V j (some B) :=
        ⟨n, hspan i hi, hrun n hbn (le_refl n)⟩
      obtain ⟨helig, B, hB⟩ := Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < Nat.find hex →
          Eligible Validator i i' → Decided U V i' none := by
        intro i' h1 h2 h3
        have hnc : ¬ ∃ C, Decided U V i' (some C) := fun hc =>
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
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ ThickLink U B L (S.slotRound i)
      · -- commit a minimal passing candidate
        have hCne : (U.ids.filter fun L => IsLeaderBlock U i L ∧
            ThickLink U B L (S.slotRound i)).Nonempty := by
          obtain ⟨L, hL, ht⟩ := hc
          exact ⟨L, Finset.mem_filter.mpr ⟨hL.1, hL, ht⟩⟩
        have hmem := Finset.min'_mem _ hCne
        rw [Finset.mem_filter] at hmem
        refine ⟨some ((U.ids.filter fun L => IsLeaderBlock U i L ∧
            ThickLink U B L (S.slotRound i)).min' hCne),
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

/-! ## O10 — liveness, composed -/

/-- **O10 (thesis Theorem 12).** Under production and post-`R`
synchrony, a recurring run of `c` correct-led slots decides
every slot below it — with the run placed past both the target and `R`
by fairness. Note the horizon: the run's last slot needs rounds up to
its `slotRound + 1` only. -/
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn T c) (R : ℕ) (k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → PopulatedOn U T r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨b, hb, hrunT⟩ := fair (max k k₀)
  have hRb : R ≤ S.slotRound b :=
    le_trans hk₀ (S.mono (le_trans (le_max_right k k₀) hb))
  refine ⟨b, le_trans (le_max_left _ _) hb, hRb, ?_⟩
  intro U N hpop hs hN
  have hrun : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B, Decided U (View.full U) j (some B) := by
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

/-- **O10 at `T := Correct`.** -/
theorem all_decided_below_of_fairRun_correct {c : ℕ} (hc : 0 < c)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn (Correct : Finset Validator) c) (R : ℕ) (k : ℕ) :
    ∃ b, k ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r, R ≤ r → r ≤ N → Populated U r) → Synchronised U R →
        S.slotRound (b + c - 1) + 1 ≤ N →
        ∀ i, i < b → ∃ v, Decided U (View.full U) i v :=
  all_decided_below_of_fairRun hc Finset.Subset.rfl card_correct hspan
    fair R k

end Odontoceti

end LeanDag
