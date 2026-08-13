import LeanDag.Nemo.Rules
import LeanDag.Mysticeti

/-!
# Nemo-Nemo: the decision relation and its safety

The crash decision layer: slots, view-relative rules, the `Decided`
relation, agreement, and the ledger. The scaffolding is the core's — the
fault-agnostic `Slots` class, the polymorphic `anchor_eq`, and the generic
`commitSeq` are consumed verbatim from `LeanDag.Mysticeti` — while the
eligibility arithmetic is the hybrid arc's wavelength-two version:
`decisionRound k = slotRound k + 1`, so an anchor needs only two rounds of
clearance.

Three crash simplifications against the Byzantine mirrors, all downstream of
universal `no_equivocation`:

* **`Decided` has three constructors** — no `directSkip`: the implementation
  pins the direct-skip quorum to the full stake, so leaders are skipped only
  indirectly, via an anchor.
* **No canonicity clause and no `[LinearOrder BlockId]`** on
  `indirectCommit`: the candidate leader block of a slot is unique outright
  (`isLeaderBlock_unique`), so there are no twins to tie-break.
* **`decided_unique` is hypothesis-free** — non-equivocation is baked into
  the crash `Universe`, and every commit-versus-commit case closes by
  candidate uniqueness with no certificate counting at all. The direct-rule
  quorum is consumed exactly once, in the visibility lemma
  `certifiedIn_of_directCommitIn_at_anchor`.
-/

namespace LeanDag

namespace Nemo

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : Universe Validator BlockId Payload}
variable [S : Slots Validator]

/-! ## Eligibility at wavelength two -/

variable (Validator) in
/-- The round at which a slot's verdict is settled: its votes live here.
One round — at wave length two the votes are the certificates. -/
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 1

variable (Validator) in
/-- `j` may anchor `k`: its proposal lies past `k`'s decision round. -/
def Eligible (k j : ℕ) : Prop := decisionRound Validator k < S.slotRound j

omit [Fintype Validator] [DecidableEq Validator] in
/-- Eligibility, unfolded: two rounds. -/
theorem eligible_iff {k j : ℕ} :
    Eligible Validator k j ↔ S.slotRound k + 2 ≤ S.slotRound j := by
  simp [Eligible, decisionRound]
  omega

instance decidableEligible (k j : ℕ) : Decidable (Eligible Validator k j) :=
  inferInstanceAs (Decidable (decisionRound Validator k < S.slotRound j))

omit [Fintype Validator] [DecidableEq Validator] in
/-- An eligible anchor is a later slot. -/
theorem lt_of_eligible {k j : ℕ} (h : Eligible Validator k j) : k < j := by
  by_contra hle
  have : S.slotRound j ≤ S.slotRound k := S.mono (by omega)
  rw [eligible_iff] at h
  omega

/-! ## Leader blocks -/

/-- `L` is a candidate leader block of slot `k`. -/
def IsLeaderBlock (U : Universe Validator BlockId Payload) (k : ℕ) (L : BlockId) : Prop :=
  L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧ (U.block L).creator = S.leader k

instance decidableIsLeaderBlock (k : ℕ) (L : BlockId) : Decidable (IsLeaderBlock U k L) :=
  inferInstanceAs (Decidable (L ∈ U.ids ∧ (U.block L).round = S.slotRound k ∧
    (U.block L).creator = S.leader k))

omit [DecidableEq BlockId] in
/-- **A slot has at most one candidate.** The crash simplification that
retires the Byzantine arcs' twin-uniqueness machinery (M5′/H5): universal
`no_equivocation` identifies two blocks sharing the slot's round and leader
before any question of commitment arises. -/
theorem isLeaderBlock_unique {k : ℕ} {L₁ L₂ : BlockId}
    (h₁ : IsLeaderBlock U k L₁) (h₂ : IsLeaderBlock U k L₂) : L₁ = L₂ :=
  U.eq_of_creator_eq h₁.1 h₂.1 (by rw [h₁.2.2, h₂.2.2]) (by rw [h₁.2.1, h₂.2.1])

omit [DecidableEq BlockId] in
/-- **A block is the candidate of at most one slot** — what `Slots.keyed`
buys: two slots sharing a round are told apart by their leaders. -/
theorem slot_eq_of_isLeaderBlock {k₁ k₂ : ℕ} {L : BlockId}
    (h₁ : IsLeaderBlock U k₁ L) (h₂ : IsLeaderBlock U k₂ L) : k₁ = k₂ :=
  S.keyed (by simp only [← h₁.2.1, ← h₂.2.1, ← h₁.2.2, ← h₂.2.2])

omit [DecidableEq BlockId] in
/-- The anchor's round clears the slot's decision round by one — exactly the
`r + 2` clearance that link integrity (`certifiedIn_of_directCommit`)
consumes. -/
theorem anchor_round_le {k j : ℕ} {A : BlockId} (hA : IsLeaderBlock U j A)
    (helig : Eligible Validator k j) :
    S.slotRound k + 2 ≤ (U.block A).round := by
  rw [hA.2.1]
  exact eligible_iff.mp helig

/-! ## The view-relative direct rule -/

/-- The supporters a view actually holds. -/
def supportersIn (U : Universe Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) :
    Finset Validator :=
  creatorsOf U.block
    (((blocksAt U (r + 1)).filter (fun p => L ∈ (U.block p).refs)) ∩ V.ids)

/-- Direct commit, as judged from a single view. -/
def DirectCommitIn (U : Universe Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (L : BlockId) (r : ℕ) : Prop :=
  majority Validator ≤ (supportersIn U V L r).card

instance {V : View Validator BlockId Payload U} (L : BlockId) (r : ℕ) :
    Decidable (DirectCommitIn U V L r) :=
  inferInstanceAs (Decidable (_ ≤ _))

omit S in
/-- A view can only under-report: its direct commit is genuine. -/
theorem directCommit_of_directCommitIn
    {V : View Validator BlockId Payload U} {L : BlockId} {r : ℕ}
    (h : DirectCommitIn U V L r) : DirectCommit U L r :=
  le_trans h (Finset.card_le_card
    (Finset.image_subset_image Finset.inter_subset_left))

/-! ## The decision relation -/

/-- **The decision relation.** `Decided U V k v` — a validator holding the
view `V` has settled slot `k`, committing the block `v = some L` or skipping
it, `v = none`.

Three rules. The *direct* rule reads the slot's own votes: a candidate
carrying a majority of them is committed. The *indirect* pair applies when
the direct evidence is inconclusive, and decides `k` by looking up to an
**anchor** — the nearest eligible slot above `k` that is itself committed —
and asking whether a vote for a candidate of `k` lies in the anchor's cone.
There is no direct skip: the implementation pins its quorum to the full
stake, so skips only ever arrive via an anchor.

"Nearest" is stated positively: every eligible slot strictly between `k` and
the anchor is decided `none`. The negative reading would be a negative
premise, which an inductive definition cannot carry; the positive form is
equivalent, since the sweep decides every slot it passes, and it keeps every
recursive occurrence strictly positive.

The `indirectSkip` premise still quantifies over candidates even though a
slot has at most one (`isLeaderBlock_unique`): the ∀ ranges over a
possibly-empty set, covering the crashed leader that produced no block.

The relation is indexed by a view, so two validators may reach different
verdicts by the letter of the definition; `decided_unique` is the theorem
that they cannot. -/
inductive Decided (U : Universe Validator BlockId Payload)
    (V : View Validator BlockId Payload U) : ℕ → Option BlockId → Prop
  /-- The direct rule commits a candidate outright. -/
  | directCommit {k : ℕ} {L : BlockId} :
      IsLeaderBlock U k L → DirectCommitIn U V L (S.slotRound k) →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, a vote is in reach. -/
  | indirectCommit {k j : ℕ} {A L : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      Decided U V k (some L)
  /-- Anchored on the nearest eligible committed slot, no candidate is in
  reach. -/
  | indirectSkip {k j : ℕ} {A : BlockId} :
      k < j → Eligible Validator k j → Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none) →
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      Decided U V k none

/-- Whatever route it took, a committed verdict names a genuine candidate for
that slot. -/
theorem isLeaderBlock_of_decided {V : View Validator BlockId Payload U} {j : ℕ} {A : BlockId}
    (h : Decided U V j (some A)) : IsLeaderBlock U j A := by
  cases h with
  | directCommit hL _ => exact hL
  | indirectCommit _ _ _ _ hL _ => exact hL

/-- **A committed block belongs to one slot.** The ledger reads verdicts off
in slot order, so without this a single block could be delivered twice. -/
theorem slot_eq_of_decided_commit {V₁ V₂ : View Validator BlockId Payload U}
    {k₁ k₂ : ℕ} {L : BlockId}
    (h₁ : Decided U V₁ k₁ (some L)) (h₂ : Decided U V₂ k₂ (some L)) : k₁ = k₂ :=
  slot_eq_of_isLeaderBlock (isLeaderBlock_of_decided h₁) (isLeaderBlock_of_decided h₂)

/-! ## Agreement -/

/-- **The visibility lemma.** A view-level direct commit is certified at any
committed anchor of any eligible slot — the eligibility premise places the
anchor far enough above for link integrity to reach it. The only place the
direct-rule quorum is consumed in the agreement proof. -/
theorem certifiedIn_of_directCommitIn_at_anchor
    {V W : View Validator BlockId Payload U} {k j : ℕ} {L A : BlockId}
    (h : DirectCommitIn U V L (S.slotRound k))
    (hj : Decided U W j (some A)) (helig : Eligible Validator k j) :
    CertifiedIn U A L (S.slotRound k) :=
  certifiedIn_of_directCommit (directCommit_of_directCommitIn h)
    (isLeaderBlock_of_decided hj).1
    (anchor_round_le (isLeaderBlock_of_decided hj) helig)

/-- **Agreement.** No two validators reach conflicting decisions for a slot,
whatever views they hold and whichever routes they took. Hypothesis-free —
non-equivocation is baked into the crash `Universe`.

Structural induction on the first derivation: nine constructor pairings.
Every commit-versus-commit case closes by `isLeaderBlock_unique` — no
certificate counting. The direct-versus-indirect crossings close by the
visibility lemma against the skipper's own anchor, and the one real case —
indirect commit against indirect skip — by comparing the two anchors with
the core's polymorphic `anchor_eq`. -/
theorem decided_unique {V₁ : View Validator BlockId Payload U} {k : ℕ} {v₁ : Option BlockId}
    (h₁ : Decided U V₁ k v₁) :
    ∀ (V₂ : View Validator BlockId Payload U) (v₂ : Option BlockId),
      Decided U V₂ k v₂ → v₁ = v₂ := by
  induction h₁ with
  | @directCommit k L hL h =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ _ => exact congrArg some (isLeaderBlock_unique hL hL₂)
    | indirectCommit _ _ _ _ hL₂ _ => exact congrArg some (isLeaderBlock_unique hL hL₂)
    | @indirectSkip _ j₂ A₂ _ helig₂ hj₂ _ hnone₂ =>
      exact absurd (certifiedIn_of_directCommitIn_at_anchor h hj₂ helig₂) (hnone₂ _ hL)
  | @indirectCommit k j A L hkj helig hj hmid hL hcert ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ _ => exact congrArg some (isLeaderBlock_unique hL hL₂)
    | indirectCommit _ _ _ _ hL₂ _ => exact congrArg some (isLeaderBlock_unique hL hL₂)
    | @indirectSkip _ j₂ A₂ hkj₂ helig₂ hj₂ hmid₂ hnone₂ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact absurd hcert (hnone₂ _ hL)
  | @indirectSkip k j A hkj helig hj hmid hnone ihj ihmid =>
    intro V₂ v₂ h₂
    cases h₂ with
    | directCommit hL₂ h₂ =>
      exact absurd (certifiedIn_of_directCommitIn_at_anchor h₂ hj helig) (hnone _ hL₂)
    | @indirectCommit _ j₂ A₂ L₂ hkj₂ helig₂ hj₂ hmid₂ hL₂ hcert₂ =>
      obtain ⟨rfl, rfl⟩ := anchor_eq hkj helig hkj₂ helig₂ hj₂ hmid₂ ihj ihmid
      exact absurd hcert₂ (hnone _ hL₂)
    | indirectSkip _ _ _ _ _ => rfl

/-- Agreement, in the shape callers want: two validators' verdicts for a
slot agree. -/
theorem decided_agree {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {v₁ v₂ : Option BlockId} (h₁ : Decided U V₁ k v₁) (h₂ : Decided U V₂ k v₂) :
    v₁ = v₂ :=
  decided_unique h₁ V₂ v₂ h₂

/-- No two validators commit *different* blocks for one slot. -/
theorem eq_of_decided_commit {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ}
    {L₁ L₂ : BlockId} (h₁ : Decided U V₁ k (some L₁)) (h₂ : Decided U V₂ k (some L₂)) :
    L₁ = L₂ :=
  Option.some.inj (decided_agree h₁ h₂)

/-- No validator commits a slot another has skipped: a committed block never
has to be retracted. -/
theorem not_decided_skip_of_decided_commit {V₁ V₂ : View Validator BlockId Payload U}
    {k : ℕ} {L : BlockId} (h₁ : Decided U V₁ k (some L)) (h₂ : Decided U V₂ k none) :
    False := by
  simpa using decided_agree h₁ h₂

/-! ## The committed-leader sequence

`commitSeq` itself is the core's — it is generic in the verdict assignment
and mentions no universe — so only the agreement statement is restated over
the crash `Decided`. -/

/-- **The committed-leader sequence is agreed.** Two validators that have
settled the first `n` slots — on whatever views, by whatever mix of direct
and indirect routes — read off the same list of committed blocks. -/
theorem commitSeq_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    commitSeq g₁ n = commitSeq g₂ n := by
  have h : ∀ k ∈ List.range n, g₁ k = g₂ k := by
    intro k hk
    rw [List.mem_range] at hk
    exact decided_agree (h₁ k hk) (h₂ k hk)
  simp only [commitSeq]
  exact List.filterMap_congr h

/-! ## No retraction

The ledger statements, ported from the core: whether and when a block is
output needs no order on ids, and that is what retraction would violate. -/

/-- The blocks output after settling slots `0, …, n-1`: everything in the
causal history of a committed leader. -/
def ledgerSet (U : Universe Validator BlockId Payload)
    (g : ℕ → Option BlockId) (n : ℕ) : Set BlockId :=
  {b | ∃ k, k < n ∧ ∃ L, g k = some L ∧ Reaches U L b}

omit [DecidableEq BlockId] S in
/-- **Nothing is ever dropped.** The ledger only grows as more slots settle. -/
theorem ledgerSet_mono {g : ℕ → Option BlockId} {n m : ℕ} (h : n ≤ m) :
    ledgerSet U g n ⊆ ledgerSet U g m := by
  rintro b ⟨k, hk, hrest⟩
  exact ⟨k, by omega, hrest⟩

/-- **Two validators output the same blocks.** -/
theorem ledgerSet_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId}
    (h₁ : ∀ k, k < n → Decided U V₁ k (g₁ k))
    (h₂ : ∀ k, k < n → Decided U V₂ k (g₂ k)) :
    ledgerSet U g₁ n = ledgerSet U g₂ n := by
  have hg : ∀ k, k < n → g₁ k = g₂ k := fun k hk => decided_agree (h₁ k hk) (h₂ k hk)
  ext b
  constructor
  · rintro ⟨k, hk, L, hL, hr⟩
    exact ⟨k, hk, L, (hg k hk) ▸ hL, hr⟩
  · rintro ⟨k, hk, L, hL, hr⟩
    exact ⟨k, hk, L, (hg k hk).symm ▸ hL, hr⟩

/-- `b` enters the ledger at slot `k`: the first committed slot whose leader
reaches it. -/
def OutputAt (U : Universe Validator BlockId Payload)
    (g : ℕ → Option BlockId) (b : BlockId) (k : ℕ) : Prop :=
  (∃ L, g k = some L ∧ Reaches U L b) ∧
    ∀ j, j < k → ∀ L, g j = some L → ¬ Reaches U L b

omit [DecidableEq BlockId] S in
/-- **A block enters the ledger once.** Its position is not merely stable
over time — there is no second slot it could have entered at. -/
theorem outputAt_unique {g : ℕ → Option BlockId} {b : BlockId} {k₁ k₂ : ℕ}
    (h₁ : OutputAt U g b k₁) (h₂ : OutputAt U g b k₂) : k₁ = k₂ := by
  rcases lt_trichotomy k₁ k₂ with h | h | h
  · obtain ⟨L, hL, hr⟩ := h₁.1
    exact absurd hr (h₂.2 k₁ h L hL)
  · exact h
  · obtain ⟨L, hL, hr⟩ := h₂.1
    exact absurd hr (h₁.2 k₂ h L hL)

/-- **And validators agree on which slot that is.** -/
theorem outputAt_agree {V₁ V₂ : View Validator BlockId Payload U} {n : ℕ}
    {g₁ g₂ : ℕ → Option BlockId} {b : BlockId} {k : ℕ}
    (h₁ : ∀ j, j < n → Decided U V₁ j (g₁ j))
    (h₂ : ∀ j, j < n → Decided U V₂ j (g₂ j))
    (hk : k < n) (ho : OutputAt U g₁ b k) : OutputAt U g₂ b k := by
  have hg : ∀ j, j < n → g₁ j = g₂ j := fun j hj => decided_agree (h₁ j hj) (h₂ j hj)
  refine ⟨?_, ?_⟩
  · obtain ⟨L, hL, hr⟩ := ho.1
    exact ⟨L, (hg k hk) ▸ hL, hr⟩
  · intro j hj L hL hr
    exact ho.2 j hj L ((hg j (by omega)).symm ▸ hL) hr

end Nemo

end LeanDag
