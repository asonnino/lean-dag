import LeanDag.Chop
import LeanDag.Liveness

/-!
# Decisions survive the cut

`garbage.md` **G3** and **G4** at the `Decided` level. The per-slot verdicts
(`directCommit_chop` and friends) said each *rule* reads only the window
above the horizon; this file lifts that to the full decision relation — the
recursion through anchors and intermediate skips included — and closes with
the cross-cut agreement theorem: a validator that joined from the truncation
and never saw the pruned prefix decides every slot exactly as a full-history
validator does.

Three pieces of transport, then the theorem:

* **`View.chop`** — a validator's view, truncated at the horizon. Downward
  closure survives because a retained block's references sit one round below
  it, hence at or above the cut — except at the base layer, where `chop`
  emptied them.
* **`Slots.chop`** — the induced schedule: slots re-indexed from a base slot
  `d` whose round clears the horizon, rounds rebased by `−G`. Monotonicity,
  unboundedness and keying all descend from the original schedule; keying
  needs the base-slot condition `G ≤ slotRound d`, which pins the rebased
  rounds above zero where subtraction is faithful.
* **the rule correspondences** — `IsLeaderBlock`, `Eligible`,
  `DirectCommitIn`, `DirectSkipIn` and the indirect test, each computed in
  the truncation against the truncated view, agree with the original. The
  view-relative ones ride on the fact that everything a rule counts lives
  strictly above the cut, so the view filter is invisible to it.

**`decided_chop`** then follows by structural induction both ways: the
derivation trees match constructor for constructor, with anchors and
intermediate slots re-indexed by `d`. The slot-`d` premise is the *only*
condition — no synchrony, no fairness, no liveness.

**`decided_agree_chop`** is the payoff (G4), and it is deliberately
asymmetric: the joiner's view `W` is an **arbitrary** view of the
truncation — not a truncated full-history view. A joiner's view is never of
the form `V.chop`: lifted to `U` it would not be downward closed, its base
layer having lost its references. The theorem instead plays `decided_unique`
*inside the truncation* against a truncated view, and moves across the cut
through `decided_chop`. So the two validators need share nothing but the
truncation itself.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {G : ℕ}

/-! ## The truncated view -/

/-- A validator's view, truncated at the horizon: keep what clears the cut.
Closure survives: a retained block's references sit one round below it,
hence at or above the cut — except at the base layer, where they are gone. -/
def View.chop (V : View Validator BlockId Payload U) (G : ℕ) :
    View Validator BlockId Payload (chop U G) where
  ids := V.ids.filter fun i => G ≤ (U.block i).round
  subset_ids := by
    intro i hi
    rw [Finset.mem_filter] at hi
    exact mem_chop_ids.mpr ⟨V.subset_ids hi.1, hi.2⟩
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rw [chop_block_eq] at hj
    rcases Nat.lt_or_ge G (U.block i).round with hlt | hge
    · rw [chopBlock_refs_of_lt hlt] at hj
      have := U.round_of_mem_refs (V.subset_ids hi.1) hj
      exact Finset.mem_filter.mpr ⟨V.complete i hi.1 j hj, by omega⟩
    · rw [chopBlock_refs_of_le hge] at hj
      simp at hj

theorem View.chop_ids (V : View Validator BlockId Payload U) :
    (V.chop G).ids = V.ids.filter fun i => G ≤ (U.block i).round := rfl

/-! ## The induced schedule -/

/-- The truncation's slot schedule: slots re-indexed from a base slot `d`
whose round clears the horizon, rounds rebased by `−G`. The base-slot
condition keeps subtraction faithful, which is what keying needs. -/
@[reducible]
def Slots.chop (S : Slots Validator) (G d : ℕ) (hd : G ≤ S.slotRound d) :
    Slots Validator where
  slotRound k := S.slotRound (d + k) - G
  leader k := S.leader (d + k)
  mono _ _ h := Nat.sub_le_sub_right (S.mono (Nat.add_le_add_left h d)) G
  unbounded := by
    intro n
    obtain ⟨k, hk⟩ := S.unbounded (G + n)
    rcases Nat.le_total k d with hkd | hdk
    · refine ⟨0, ?_⟩
      have := S.mono hkd
      simp only [Nat.add_zero]
      omega
    · refine ⟨k - d, ?_⟩
      have hcancel : d + (k - d) = k := by omega
      simp only [hcancel]
      omega
  keyed := by
    intro k₁ k₂ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨hr, hl⟩ := h
    have h₁ := hd.trans (S.mono (Nat.le_add_right d k₁))
    have h₂ := hd.trans (S.mono (Nat.le_add_right d k₂))
    have hpair : (S.slotRound (d + k₁), S.leader (d + k₁))
        = (S.slotRound (d + k₂), S.leader (d + k₂)) := by
      have : S.slotRound (d + k₁) = S.slotRound (d + k₂) := by omega
      rw [this, hl]
    have := S.keyed hpair
    omega

@[simp]
theorem Slots.chop_slotRound (S : Slots Validator) {d : ℕ}
    (hd : G ≤ S.slotRound d) (k : ℕ) :
    (S.chop G d hd).slotRound k = S.slotRound (d + k) - G := rfl

@[simp]
theorem Slots.chop_leader (S : Slots Validator) {d : ℕ}
    (hd : G ≤ S.slotRound d) (k : ℕ) :
    (S.chop G d hd).leader k = S.leader (d + k) := rfl

variable [S : Slots Validator] {d : ℕ}

/-- Every slot from the base slot on clears the horizon. -/
theorem horizon_le_slotRound (hd : G ≤ S.slotRound d) (k : ℕ) :
    G ≤ S.slotRound (d + k) :=
  hd.trans (S.mono (Nat.le_add_right d k))

/-! ## The rules, transported -/

theorem isLeaderBlock_chop (hd : G ≤ S.slotRound d) {k : ℕ} {L : BlockId} :
    IsLeaderBlock (S := S.chop G d hd) (chop U G) k L ↔
      IsLeaderBlock U (d + k) L := by
  have hGk := horizon_le_slotRound hd k
  unfold IsLeaderBlock
  rw [chop_block_eq]
  simp only [chopBlock_round, chopBlock_creator, mem_chop_ids,
    Slots.chop_slotRound, Slots.chop_leader]
  constructor
  · rintro ⟨⟨hL, hLr⟩, hround, hcreator⟩
    exact ⟨hL, by omega, hcreator⟩
  · rintro ⟨hL, hround, hcreator⟩
    exact ⟨⟨hL, by omega⟩, by omega, hcreator⟩

theorem eligible_chop (hd : G ≤ S.slotRound d) {k j : ℕ} :
    Eligible (S := S.chop G d hd) Validator k j ↔
      Eligible Validator (d + k) (d + j) := by
  have hk := horizon_le_slotRound hd k
  have hj := horizon_le_slotRound hd j
  rw [eligible_iff (S := S.chop G d hd), eligible_iff (S := S)]
  simp only [Slots.chop_slotRound]
  omega

omit S in
/-- The view filter is invisible to the certificate count: certificates for
a slot above the cut live two rounds higher still. -/
theorem certificatesIn_chop {V : View Validator BlockId Payload U}
    {L : BlockId} (s : ℕ) :
    certificatesIn (chop U G) (V.chop G) L s = certificatesIn U V L (G + s) := by
  unfold certificatesIn
  rw [certificates_chop]
  ext C
  simp only [Finset.mem_inter, View.chop_ids, Finset.mem_filter, mem_certificates]
  constructor
  · rintro ⟨hC, hv, -⟩
    exact ⟨hC, hv⟩
  · rintro ⟨⟨hC, hCr, hcert⟩, hv⟩
    exact ⟨⟨hC, hCr, hcert⟩, hv, by omega⟩

omit S in
theorem directCommitIn_chop {V : View Validator BlockId Payload U}
    {L : BlockId} (s : ℕ) :
    DirectCommitIn (chop U G) (V.chop G) L s ↔ DirectCommitIn U V L (G + s) := by
  unfold DirectCommitIn
  rw [certificatesIn_chop, chop_block_eq, creatorsOf_chopBlock]

omit S in
theorem directSkipIn_chop {V : View Validator BlockId Payload U}
    {L : BlockId} (s : ℕ) :
    DirectSkipIn (chop U G) (V.chop G) L s ↔ DirectSkipIn U V L (G + s) := by
  unfold DirectSkipIn
  rw [chop_block_eq, blocksAt_chop, creatorsOf_chopBlock]
  have hset : ((blocksAt U (G + (s + 1))).filter
        fun q => L ∉ (chopBlock U G q).refs) ∩ (V.chop G).ids
      = ((blocksAt U (G + s + 1)).filter fun q => L ∉ (U.block q).refs) ∩ V.ids := by
    ext q
    simp only [Finset.mem_inter, Finset.mem_filter, mem_blocksAt, View.chop_ids]
    constructor
    · rintro ⟨⟨⟨hq, hqr⟩, hnot⟩, hv, -⟩
      rw [chopBlock_refs_of_lt (by omega)] at hnot
      exact ⟨⟨⟨hq, by omega⟩, hnot⟩, hv⟩
    · rintro ⟨⟨⟨hq, hqr⟩, hnot⟩, hv⟩
      refine ⟨⟨⟨hq, by omega⟩, ?_⟩, hv, by omega⟩
      rw [chopBlock_refs_of_lt (by omega)]
      exact hnot
  rw [hset]

/-- The anchor of a decided slot at or past the base slot survives the cut. -/
theorem anchor_mem_chop_ids (hd : G ≤ S.slotRound d) {j : ℕ} {A : BlockId}
    (h : IsLeaderBlock U (d + j) A) : A ∈ (chop U G).ids := by
  obtain ⟨hA, hAr, -⟩ := h
  have := horizon_le_slotRound hd j
  exact mem_chop_ids.mpr ⟨hA, by omega⟩

/-! ## G3 — the decision relation survives the cut -/

/-- Forward: a decision reached on the truncation, from a truncated view, is
the original decision. Structural induction; anchors re-index by `d`. -/
theorem decided_of_decided_chop (hd : G ≤ S.slotRound d)
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId}
    (h : Decided (S := S.chop G d hd) (chop U G) (V.chop G) k v) :
    Decided U V (d + k) v := by
  induction h with
  | @directCommit k L hL hc =>
    have hGk := horizon_le_slotRound hd k
    refine Decided.directCommit ((isLeaderBlock_chop hd).mp hL) ?_
    have := (directCommitIn_chop (V := V) (S.slotRound (d + k) - G)).mp hc
    rwa [Nat.add_sub_cancel' hGk] at this
  | @directSkip k hskip =>
    have hGk := horizon_le_slotRound hd k
    refine Decided.directSkip fun L hL => ?_
    have := (directSkipIn_chop (V := V) (S.slotRound (d + k) - G)).mp
      (hskip L ((isLeaderBlock_chop hd).mpr hL))
    rwa [Nat.add_sub_cancel' hGk] at this
  | @indirectCommit k j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
    have hGk := horizon_le_slotRound hd k
    have hA : A ∈ (chop U G).ids :=
      (isLeaderBlock_of_decided (S := S.chop G d hd) hanchor).1
    refine Decided.indirectCommit (by omega) ((eligible_chop hd).mp helig)
      ihj ?_ ((isLeaderBlock_chop hd).mp hL) ?_
    · intro i h1 h2 he
      obtain ⟨i', rfl⟩ : ∃ i', i = d + i' := ⟨i - d, by omega⟩
      exact ihmid i' (by omega) (by omega) ((eligible_chop hd).mpr he)
    · have := (certifiedIn_chop hA (S.slotRound (d + k) - G)).mp hcert
      rwa [Nat.add_sub_cancel' hGk] at this
  | @indirectSkip k j A hkj helig hanchor hmid hnone ihj ihmid =>
    have hGk := horizon_le_slotRound hd k
    have hA : A ∈ (chop U G).ids :=
      (isLeaderBlock_of_decided (S := S.chop G d hd) hanchor).1
    refine Decided.indirectSkip (by omega) ((eligible_chop hd).mp helig)
      ihj ?_ ?_
    · intro i h1 h2 he
      obtain ⟨i', rfl⟩ : ∃ i', i = d + i' := ⟨i - d, by omega⟩
      exact ihmid i' (by omega) (by omega) ((eligible_chop hd).mpr he)
    · intro L hL hcert
      have hup : CertifiedIn U A L (G + (S.slotRound (d + k) - G)) := by
        rwa [Nat.add_sub_cancel' hGk]
      exact hnone L ((isLeaderBlock_chop hd).mpr hL)
        ((certifiedIn_chop hA _).mpr hup)

/-- Backward: the original decision is reached on the truncation. Stated
over an arbitrary slot `n = d + k` so the induction can move through
anchors. -/
theorem decided_chop_of_decided (hd : G ≤ S.slotRound d)
    {V : View Validator BlockId Payload U} {n : ℕ} {v : Option BlockId}
    (h : Decided U V n v) :
    ∀ k, n = d + k → Decided (S := S.chop G d hd) (chop U G) (V.chop G) k v := by
  induction h with
  | @directCommit n L hL hc =>
    rintro k rfl
    have hGk := horizon_le_slotRound hd k
    refine Decided.directCommit (S := S.chop G d hd) ((isLeaderBlock_chop hd).mpr hL) ?_
    show DirectCommitIn (chop U G) (V.chop G) L (S.slotRound (d + k) - G)
    refine (directCommitIn_chop _).mpr ?_
    rwa [Nat.add_sub_cancel' hGk]
  | @directSkip n hskip =>
    rintro k rfl
    have hGk := horizon_le_slotRound hd k
    refine Decided.directSkip (S := S.chop G d hd) fun L hL => ?_
    show DirectSkipIn (chop U G) (V.chop G) L (S.slotRound (d + k) - G)
    refine (directSkipIn_chop _).mpr ?_
    have := hskip L ((isLeaderBlock_chop hd).mp hL)
    rwa [Nat.add_sub_cancel' hGk]
  | @indirectCommit n j A L hkj helig hanchor hmid hL hcert ihj ihmid =>
    rintro k rfl
    have hGk := horizon_le_slotRound hd k
    obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
    have hA : A ∈ (chop U G).ids :=
      anchor_mem_chop_ids hd (isLeaderBlock_of_decided hanchor)
    refine Decided.indirectCommit (S := S.chop G d hd) (by omega)
      ((eligible_chop hd).mpr helig) (ihj j' rfl) ?_ ((isLeaderBlock_chop hd).mpr hL) ?_
    · intro i' h1 h2 he
      exact ihmid (d + i') (by omega) (by omega)
        ((eligible_chop hd).mp he) i' rfl
    · show CertifiedIn (chop U G) A L (S.slotRound (d + k) - G)
      refine (certifiedIn_chop hA _).mpr ?_
      rwa [Nat.add_sub_cancel' hGk]
  | @indirectSkip n j A hkj helig hanchor hmid hnone ihj ihmid =>
    rintro k rfl
    have hGk := horizon_le_slotRound hd k
    obtain ⟨j', rfl⟩ : ∃ j', j = d + j' := ⟨j - d, by omega⟩
    have hA : A ∈ (chop U G).ids :=
      anchor_mem_chop_ids hd (isLeaderBlock_of_decided hanchor)
    refine Decided.indirectSkip (S := S.chop G d hd) (by omega)
      ((eligible_chop hd).mpr helig) (ihj j' rfl) ?_ ?_
    · intro i' h1 h2 he
      exact ihmid (d + i') (by omega) (by omega)
        ((eligible_chop hd).mp he) i' rfl
    · intro L hL hcert
      refine hnone L ((isLeaderBlock_chop hd).mp hL) ?_
      have := (certifiedIn_chop hA (S.slotRound (d + k) - G)).mp hcert
      rwa [Nat.add_sub_cancel' hGk] at this

/-- **G3.** The decision relation survives the cut, both ways: a validator
re-running Mysticeti on the truncation, from its truncated view, decides
slot `k` exactly as it decided slot `d + k` on the full universe. The only
condition is that the base slot clears the horizon — no synchrony, no
liveness, nothing about the prefix. -/
theorem decided_chop (hd : G ≤ S.slotRound d)
    {V : View Validator BlockId Payload U} {k : ℕ} {v : Option BlockId} :
    Decided (S := S.chop G d hd) (chop U G) (V.chop G) k v ↔
      Decided U V (d + k) v :=
  ⟨decided_of_decided_chop hd, fun h => decided_chop_of_decided hd h k rfl⟩

/-! ## G4 — cross-cut agreement -/

/-- **G4.** A validator that joined from the truncation — holding an
**arbitrary** view `W` of `chop U G`, with no history below the cut and no
relation to any full-history view — agrees slot for slot with every
full-history validator. `decided_unique` runs inside the truncation against
the truncated full-history view, and `decided_chop` carries the verdict
across the cut. -/
theorem decided_agree_chop (hd : G ≤ S.slotRound d)
    {W : View Validator BlockId Payload (chop U G)}
    {V : View Validator BlockId Payload U} {k : ℕ} {w v : Option BlockId}
    (hW : Decided (S := S.chop G d hd) (chop U G) W k w)
    (hV : Decided U V (d + k) v) :
    w = v :=
  decided_unique (S := S.chop G d hd) hW (V.chop G) v (decided_chop_of_decided hd hV k rfl)

end LeanDag
