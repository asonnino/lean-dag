import LeanDag.Nemo.Decision
import LeanDag.Liveness

/-!
# Nemo-Nemo: crash liveness

The liveness chain for the crash arc, mirroring the hybrid arc's structure
at the majority quorum over the crash `Universe`.

**The fault bound enters here for the first time.** Everything in
`Basic`..`Decision` holds on any committee with no bound whatsoever — crash
safety is free. Only liveness pays: the `CrashFaults` class (`crashed.card ≤
f`, `2f + 1 ≤ n`) is defined in this file, imported by nothing on the safety
side, and consumed through a single bridge, `majority_le_card_live`.

**No `directSkip`, so no slot-local skip of a crashed leader.** The
implementation pins the direct-skip quorum to the full stake, so `Decided`
has three constructors — a slot whose leader crashed and produced no block
cannot be skipped at its own round the way the core's L5 skips an absent
leader. Every skip routes through `indirectSkip`, anchored on a later
live-led commit, which is why the arc's headline is
`all_decided_below_of_fairRun` and there is no L5 analogue.

**Why a *run* of two consecutive commits.** A crashed validator is
indistinguishable from a slow one, so there is no failure detector: the
anchor scan cannot step past an undecided slot (deciding through a farther
anchor would break the nearest-anchor determinism on which `decided_unique`
rests), and the only evidence that a slot can never commit is the
full-stake blame census, unattainable once anyone crashes. Every commit at
round `r` therefore casts a *shadow* at round `r − 1` — a slot it can
neither anchor (one round too close) nor step past. A lone commit settles
only itself and round `r − 2`: for any commit set with no two members at
adjacent rounds, the settled slots are exactly the commits and their
round-minus-two neighbours, and everything else stalls forever — commits at
every even round, both pipeline stages committing infinitely often, still
settle no odd slot. Two commits at *consecutive* rounds are the minimal
self-sufficient configuration: the upper one anchors the lower one's shadow
with a vacuous intermediate premise, and the upper one's shadow is the
lower commit itself. Hence `FairRunOn T 2`. The hypothesis is harmless for
the intended schedule: round-robin over `n = 2f + 1` with at most `f`
crashed always has two adjacent live leaders, since `f + 1` live validators
cannot be pairwise non-adjacent on a cycle of `2f + 1`.

The participation vocabulary (`PopulatedOn`, `SynchronisedOn`, `View.full`,
`View.CoversUpto`) is restated over the crash `Universe`; the schedule
vocabulary (`FairScheduleOn`, `FairRunOn`) is fault-agnostic and reused from
the core; `SpansEligible` is restated at this arc's wavelength-two
`Eligible`. The descent is the *core's* simple form — `isLeaderBlock_unique`
leaves no twins to tie-break, so the hybrid arc's canonicity block and its
`[LinearOrder BlockId]` never appear.

Every decision-valued statement concludes on a validator's own view,
caught up to the horizon it reads (`View.CoversUpto`): the supporters sit
one round above the leader, so a caught-up view holds them
(`directCommitIn_of_coversUpto`), and the descent is view-parametric. The
full view is caught up to every horizon (`View.coversUpto_full`), so the
whole-universe reading is the special case (`liveness.md` §4.2).
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : Universe Validator BlockId Payload}
variable {T : Finset Validator} {L : BlockId} {s R N : ℕ}

/-! ## The crash fault model -/

/-- The crash fault model: `n ≥ 2f+1` validators, at most `f` of them
crashed. A crashed validator halts — its blocks, while they lasted, are
consistent (`no_equivocation` is universal); only its availability is in
doubt. Safety never consults this class; it exists for liveness alone. -/
class CrashFaults (Validator : Type*) [Fintype Validator] [DecidableEq Validator] where
  /-- The fault bound. -/
  f : ℕ
  /-- The crashed validators. Everything else is live. -/
  crashed : Finset Validator
  /-- At most `f` validators crash. -/
  card_crashed : crashed.card ≤ f
  /-- There are at least `2f+1` validators. -/
  card_validators : 2 * f + 1 ≤ Fintype.card Validator

section CrashModel

variable [C : CrashFaults Validator]

variable (Validator) in
/-- The live validators: everyone outside the crashed set. -/
def Live : Finset Validator := (C.crashed)ᶜ

@[simp]
theorem mem_live {v : Validator} : v ∈ Live Validator ↔ v ∉ C.crashed := by
  simp [Live]

/-- **The bridge** — the arc's only consumer of the fault bound: the live
class carries the majority quorum, since `n − f ≥ n/2 + 1` whenever
`2f + 1 ≤ n`. -/
theorem majority_le_card_live : majority Validator ≤ (Live Validator).card := by
  have h : (Live Validator).card = Fintype.card Validator - C.crashed.card :=
    Finset.card_compl C.crashed
  have hle : C.crashed.card ≤ Fintype.card Validator := Finset.card_le_univ _
  have h1 := C.card_crashed
  have h2 := C.card_validators
  unfold majority
  omega

end CrashModel

/-! ## Participation and coverage -/

/-- Every validator in `T` has a block at round `r` — the shared
`PopulatedFrom` at the crash universe's data. A *quorum* of reliable
validators, not all of `Live`: demanding the whole class would make the
theorems lapse when a single live validator misses a single round. -/
def PopulatedOn (U : Universe Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) : Prop :=
  PopulatedFrom U.block U.ids T r

/-- Decidable on concrete data, so a model can settle it by `decide`. -/
instance decidablePopulatedOn (r : ℕ) : Decidable (PopulatedOn U T r) :=
  inferInstanceAs (Decidable (PopulatedFrom U.block U.ids T r))

omit [DecidableEq BlockId] in
/-- Population is antitone: a smaller set is easier to populate. -/
theorem PopulatedOn.mono {T T' : Finset Validator} {r : ℕ} (hsub : T ⊆ T')
    (h : PopulatedOn U T' r) : PopulatedOn U T r :=
  PopulatedFrom.mono hsub h

/-- From round `R` on, every `T`-authored block references every `T`-authored
block of the round below — the shared `SynchronisedFrom` at the crash
universe's data, the post-GST coverage assumption. -/
def SynchronisedOn (U : Universe Validator BlockId Payload)
    (T : Finset Validator) (R : ℕ) : Prop :=
  SynchronisedFrom U.block U.ids T R

omit [DecidableEq BlockId] in
/-- Coverage is antitone too. -/
theorem SynchronisedOn.mono {T T' : Finset Validator} {R : ℕ} (hsub : T ⊆ T')
    (h : SynchronisedOn U T' R) : SynchronisedOn U T R :=
  SynchronisedFrom.mono hsub h

omit [DecidableEq BlockId] in
/-- Every live validator's *eventual* view. Downward-closed by
`U.complete`. -/
def View.full (U : Universe Validator BlockId Payload) :
    View Validator BlockId Payload U where
  ids := U.ids
  subset_ids := Finset.Subset.rfl
  complete := U.complete

omit [DecidableEq BlockId] in
/-- **A view caught up to round `N`**: it holds every block of the
universe at a round at or below `N` — the crash arc's copy of the
core's `View.CoversUpto`, the hypothesis under which a liveness result
holds of a validator's own view rather than of the full view. The full
view satisfies it at every `N`. -/
def View.CoversUpto (V : View Validator BlockId Payload U) (N : ℕ) : Prop :=
  ∀ b ∈ U.ids, (U.block b).round ≤ N → b ∈ V.ids

omit [DecidableEq BlockId] in
/-- The full view is caught up to every horizon. -/
theorem View.coversUpto_full (U : Universe Validator BlockId Payload) (N : ℕ) :
    (View.full U).CoversUpto N :=
  fun _ hb _ => hb

omit [DecidableEq BlockId] in
/-- Caught up to `N` is caught up to every lower horizon. -/
theorem View.CoversUpto.mono {V : View Validator BlockId Payload U} {M N : ℕ}
    (h : V.CoversUpto N) (hMN : M ≤ N) : V.CoversUpto M :=
  fun b hb hr => h b hb (le_trans hr hMN)

/-! ## Decisions are monotone in the view -/

variable [S : Slots Validator]

omit S in
/-- A larger view can only see more supporters. -/
theorem directCommitIn_mono {V V' : View Validator BlockId Payload U}
    (hsub : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ} (h : DirectCommitIn U V L r) :
    DirectCommitIn U V' L r :=
  le_trans h (Finset.card_le_card (Finset.image_subset_image
    (Finset.inter_subset_inter Finset.Subset.rfl hsub)))

/-- **Decisions are monotone in the view.** Induction on the derivation:
the direct case is the monotonicity lemma above, and the two indirect cases
rebuild themselves from the inductive hypotheses, carrying their
`CertifiedIn` premises across unchanged — the indirect test is
universe-level, so growth cannot disturb it. -/
theorem decided_mono {V V' : View Validator BlockId Payload U}
    (hsub : V.ids ⊆ V'.ids) {k : ℕ} {v : Option BlockId} (h : Decided U V k v) :
    Decided U V' k v := by
  induction h with
  | directCommit hL hdc => exact Decided.directCommit hL (directCommitIn_mono hsub hdc)
  | indirectCommit hkj helig _ _ hL hcert ihj ihmid =>
      exact Decided.indirectCommit hkj helig ihj ihmid hL hcert
  | indirectSkip hkj helig _ _ hnc ihj ihmid =>
      exact Decided.indirectSkip hkj helig ihj ihmid hnc

/-- **Commit propagation.** Whatever any validator decides on any view, the
same verdict holds on the full view — and the full view is every live
validator's eventual view, so this *is* "all live validators eventually
reach the same decision". -/
theorem decided_full {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId} (h : Decided U V k v) : Decided U (View.full U) k v :=
  decided_mono V.subset_ids h

/-! ## A reliable leader commits directly -/

/-- **The commit half.** Post-`R`, a `T`-led slot is directly committed:
coverage makes every `T` block at the decision round reference the leader's
block, and `T` carries the majority. Two populated rounds — propose and
decide, wavelength two. -/
theorem directCommit_of_leader_mem
    (hcard : majority Validator ≤ T.card)
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

omit S in
/-- A view caught up to the decision round sees every supporter, so a
direct commit in the universe is a direct commit in the view. -/
theorem directCommitIn_of_coversUpto {V : View Validator BlockId Payload U} {r : ℕ}
    (h : DirectCommit U L r) (hcov : V.CoversUpto (r + 1)) :
    DirectCommitIn U V L r := by
  have hsub : (blocksAt U (r + 1)).filter (fun p => L ∈ (U.block p).refs) ⊆ V.ids := by
    intro p hp
    obtain ⟨hp, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpids, hpr⟩ := mem_blocksAt.mp hp
    exact hcov p hpids (le_of_eq hpr)
  rw [DirectCommitIn, supportersIn, Finset.inter_eq_left.2 hsub]
  exact h

/-- The commit half, as a decision — on any view caught up to the
decision round. -/
theorem decided_of_leader_mem
    (hcard : majority Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop0 : PopulatedOn U T (S.slotRound s))
    (hpop1 : PopulatedOn U T (S.slotRound s + 1))
    (V : View Validator BlockId Payload U)
    (hcov : V.CoversUpto (S.slotRound s + 1))
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided U V s (some L) := by
  obtain ⟨L, hLb, hdc⟩ :=
    directCommit_of_leader_mem hcard hs hR hpop0 hpop1 hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_of_coversUpto hdc hcov)⟩

/-! ## A run of two spans eligibility -/

variable (Validator) in
/-- A run of `c` slots reaches past everything below it. -/
def SpansEligible (c : ℕ) : Prop :=
  ∀ b i : ℕ, i < b → Eligible Validator i (b + c - 1)

omit [Fintype Validator] [DecidableEq Validator] in
/-- Under a pipelined identity-round schedule, `c = 2` spans — two
consecutive reliable leaders suffice at wavelength two. -/
theorem spansEligible_two (hid : ∀ s, S.slotRound s = s) :
    SpansEligible Validator 2 := by
  intro b i hi
  rw [eligible_iff, hid, hid]
  omega

/-! ## The descent -/

/-- **Everything below a committed run is decided.** Given a block of
consecutive committed slots `b … n` whose top is eligible for everything
below `b`, every slot below `b` resolves — commit or skip — by anchoring on
the nearest eligible committed slot.

The core's proof, verbatim: the crash `indirectCommit` carries no canonicity
premise (`isLeaderBlock_unique` leaves no twins), so the commit branch is a
plain constructor application and no minimum-selection tie-break appears. -/
theorem decided_below_of_committed_run {V : View Validator BlockId Payload U} {b n : ℕ}
    (hbn : b ≤ n)
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
      -- The nearest slot above `i` that is both eligible for it and committed.
      have hex : ∃ j, Eligible Validator i j ∧ ∃ B, Decided U V j (some B) :=
        ⟨n, hspan i hi, hrun n hbn (le_refl n)⟩
      have hle : Nat.find hex ≤ n :=
        Nat.find_le ⟨hspan i hi, hrun n hbn (le_refl n)⟩
      obtain ⟨helig, B, hB⟩ := Nat.find_spec hex
      have hmid : ∀ i', i < i' → i' < Nat.find hex → Eligible Validator i i' →
          Decided U V i' none := by
        intro i' h1 h2 h3
        -- Minimality: an eligible slot below the anchor is not committed ...
        have hnc : ¬ ∃ C, Decided U V i' (some C) := fun hc => Nat.find_min hex h2 ⟨h3, hc⟩
        -- ... so it cannot lie in the run, so it lies below `b`, so the
        -- induction hypothesis reaches it.
        have hi'b : i' < b := by
          by_contra hge
          exact hnc (hrun i' (by omega) (by omega))
        obtain ⟨v, hv⟩ := ih i' hi'b (by omega)
        cases v with
        | none => exact hv
        | some C => exact absurd ⟨C, hv⟩ hnc
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ CertifiedIn U B L (S.slotRound i)
      · obtain ⟨L, hL, hcert⟩ := hc
        exact ⟨some L, Decided.indirectCommit (lt_of_eligible helig) helig hB hmid hL hcert⟩
      · push Not at hc
        exact ⟨none, Decided.indirectSkip (lt_of_eligible helig) helig hB hmid hc⟩
  intro i hi
  exact key (b - i) i hi (le_refl _)

/-! ## Composition: a fair schedule decides everything -/

section Composed

variable [C : CrashFaults Validator]

/-- The all-of-`Live` participation case. -/
abbrev Populated (U : Universe Validator BlockId Payload) (r : ℕ) : Prop :=
  PopulatedOn U (Live Validator) r

/-- The all-of-`Live` coverage case. -/
abbrev Synchronised (U : Universe Validator BlockId Payload) (R : ℕ) : Prop :=
  SynchronisedOn U (Live Validator) R

/-- The commit half against a horizon: two rounds read off it. `T ⊆ Live` is
consumed here and only here, converting `Populated` into `PopulatedOn T`. -/
theorem decided_of_leader_of_populated (hT : T ⊆ Live Validator)
    (hcard : majority Validator ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound s)
    (hpop : ∀ r ≤ N, Populated U r) (hN : S.slotRound s + 1 ≤ N)
    (V : View Validator BlockId Payload U) (hcov : V.CoversUpto N)
    (hlead : S.leader s ∈ T) :
    ∃ L, IsLeaderBlock U s L ∧ Decided U V s (some L) :=
  decided_of_leader_mem hcard hs hR
    (PopulatedOn.mono hT (hpop _ (by omega)))
    (PopulatedOn.mono hT (hpop _ (by omega))) V (hcov.mono hN) hlead

/-- **Liveness.** Under post-`R` coverage, growth to the horizon, and a
recurring run of `c` reliable-led slots, every slot below the run is
decided — the run placed past both the target and `R` by fairness.

The quantifier order is the content: the slot `b` is fixed by the *schedule*
alone, before any universe is named, so "eventually" means "any DAG grown
past this schedule-fixed slot". Crashed-leader slots are settled here and
only here: they descend onto the run via `indirectSkip`. -/
theorem all_decided_below_of_fairRun {c : ℕ} (hc : 0 < c)
    (hT : T ⊆ Live Validator)
    (hcard : majority Validator ≤ T.card)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn T c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : Universe Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r ≤ N, Populated U r) → SynchronisedOn U T R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided U V i v := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨b, hb, hrunT⟩ := fair (max s k₀)
  have hRb : R ≤ S.slotRound b :=
    le_trans hk₀ (S.mono (le_trans (le_max_right s k₀) hb))
  refine ⟨b, le_trans (le_max_left _ _) hb, hRb, ?_⟩
  intro U N V hpop hs hN hcov
  have hrun : ∀ j, b ≤ j → j ≤ b + c - 1 →
      ∃ B, Decided U V j (some B) := by
    intro j hj1 hj2
    have hlead : S.leader j ∈ T := by
      have := hrunT (j - b) (by omega)
      rwa [Nat.add_sub_cancel' hj1] at this
    have hRj : R ≤ S.slotRound j := le_trans hRb (S.mono hj1)
    have hjr : S.slotRound j ≤ S.slotRound (b + c - 1) := S.mono (by omega)
    obtain ⟨L, _, hdec⟩ :=
      decided_of_leader_of_populated hT hcard hs hRj hpop (by omega) V hcov hlead
    exact ⟨L, hdec⟩
  exact decided_below_of_committed_run (by omega)
    (fun i hi => hspan b i hi) hrun

/-- **Liveness at `T := Live`** — the whole live class, which the tight
committee `n = 2f + 1` requires exactly. -/
theorem all_decided_below_of_fairRun_live {c : ℕ} (hc : 0 < c)
    (hspan : SpansEligible Validator c)
    (fair : FairRunOn (Live Validator) c) (R : ℕ) (s : ℕ) :
    ∃ b, s ≤ b ∧ R ≤ S.slotRound b ∧
      ∀ (U : Universe Validator BlockId Payload) (N : ℕ)
        (V : View Validator BlockId Payload U),
        (∀ r ≤ N, Populated U r) → Synchronised U R →
        S.slotRound (b + c - 1) + 1 ≤ N → V.CoversUpto N →
        ∀ i, i < b → ∃ v, Decided U V i v :=
  all_decided_below_of_fairRun hc Finset.Subset.rfl majority_le_card_live hspan
    fair R s

end Composed

end Nemo

end LeanDag
