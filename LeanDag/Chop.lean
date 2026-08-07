import LeanDag.Mysticeti
import LeanDag.Exposure

/-!
# The horizon: truncation as rebasing

`garbage.md` §2, §4 — the operator and the safety half: **G1** (truncation
is a universe, with the one-way `DoSValid` transfer) and **G2** (verdict
invariance): `supporters`, `blames`, `certificates`, `DirectCommit`,
`DirectSkip` and the indirect test `CertifiedIn` computed in `chop U G`
agree with `U` for slots at or above the cut.

The design (`garbage.md` §2): `chop U G` keeps the blocks of rounds `≥ G`,
rebases rounds by `−G`, and empties the reference sets of the new base
layer — the round-`G` blocks become the new geneses. Every validity clause
then holds of the truncation exactly as it held of the original, so
`chop U G` is a bona-fide `BlockUniverse` and every existing theorem
applies to it verbatim. Verdict invariance is pure window-locality: each
rule reads rounds strictly above the base layer, where `chop` changes
nothing but the round label.

The one-way `DoSValid` transfer (`dosValid_chop`) is where the *statute of
limitations* lives: cones shrink under truncation, so exposure shrinks, so
the condition weakens per block. The converse fails by design — an
equivocation whose witnessing pair falls strictly below the cut is
forgiven — and the witness file makes that visible on data.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {G : ℕ} {b i j : BlockId}

/-! ## The operator -/

/-- One block of the truncation: the round is rebased by `−G`, and blocks
at or below the cut — the new base layer, plus junk — lose their
references. -/
def chopBlock (U : BlockUniverse Validator BlockId Payload) (G : ℕ)
    (i : BlockId) : Block Validator BlockId Payload :=
  if (U.block i).round ≤ G then
    { U.block i with round := (U.block i).round - G, refs := ∅ }
  else
    { U.block i with round := (U.block i).round - G }

@[simp]
theorem chopBlock_creator :
    (chopBlock U G i).creator = (U.block i).creator := by
  unfold chopBlock; split <;> rfl

@[simp]
theorem chopBlock_round :
    (chopBlock U G i).round = (U.block i).round - G := by
  unfold chopBlock; split <;> rfl

@[simp]
theorem chopBlock_payload :
    (chopBlock U G i).payload = (U.block i).payload := by
  unfold chopBlock; split <;> rfl

theorem chopBlock_refs_of_le (h : (U.block i).round ≤ G) :
    (chopBlock U G i).refs = ∅ := by
  unfold chopBlock; rw [if_pos h]

theorem chopBlock_refs_of_lt (h : G < (U.block i).round) :
    (chopBlock U G i).refs = (U.block i).refs := by
  unfold chopBlock; rw [if_neg (by omega)]

/-- The truncation's references never exceed the original's. -/
theorem chopBlock_refs_subset :
    (chopBlock U G i).refs ⊆ (U.block i).refs := by
  rcases Nat.lt_or_ge G (U.block i).round with h | h
  · rw [chopBlock_refs_of_lt h]
  · rw [chopBlock_refs_of_le h]; exact Finset.empty_subset _

/-- Creators are untouched, so creator sets are, pointwise. -/
theorem creatorsOf_chopBlock (s : Finset BlockId) :
    creatorsOf (chopBlock U G) s = creatorsOf U.block s := by
  unfold creatorsOf
  exact Finset.image_congr fun i _ => chopBlock_creator

/-- **The horizon** (`garbage.md` §2): the universe above the cut, rounds
rebased, the round-`G` layer as the new geneses. -/
def chop (U : BlockUniverse Validator BlockId Payload) (G : ℕ) :
    BlockUniverse Validator BlockId Payload where
  ids := U.ids.filter fun i => G ≤ (U.block i).round
  block := chopBlock U G
  complete := by
    intro i hi j hj
    rw [Finset.mem_filter] at hi
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    · rw [chopBlock_refs_of_lt h] at hj
      have hj_ids := U.complete i hi.1 j hj
      have hj_round := U.round_of_mem_refs hi.1 hj
      exact Finset.mem_filter.mpr ⟨hj_ids, by omega⟩
    · rw [chopBlock_refs_of_le h] at hj
      exact absurd hj (Finset.notMem_empty j)
  valid := by
    intro i hi
    rw [Finset.mem_filter] at hi
    have hv := U.valid i hi.1
    rcases Nat.lt_or_ge G (U.block i).round with h | h
    swap
    · -- the new base layer (and junk): no references, nothing to prove
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
          | (intro j hj
             rw [chopBlock_refs_of_le h] at hj
             exact absurd hj (Finset.notMem_empty j))
          | (intro hr
             rw [chopBlock_round] at hr
             omega)
    · refine ⟨?_, ?_, ?_, ?_⟩
      · -- predecessor, rebased
        intro j hj
        rw [chopBlock_refs_of_lt h] at hj
        have := hv.predecessor j hj
        rw [chopBlock_round, chopBlock_round]
        omega
      · -- distinct creators, untouched
        intro a ha b hb hab
        rw [chopBlock_refs_of_lt h] at ha hb
        rw [chopBlock_creator, chopBlock_creator] at hab
        exact hv.distinct_creators a ha b hb hab
      · -- quorum, untouched
        intro _
        have hcr : creators (chopBlock U G) (chopBlock U G i) =
            creators U.block (U.block i) := by
          unfold creators
          rw [chopBlock_refs_of_lt h, creatorsOf_chopBlock]
        rw [hcr]
        exact hv.quorum (by omega)
      · -- self-parent, untouched
        intro _
        obtain ⟨p, hp, hpc⟩ := hv.self_parent (by omega)
        refine ⟨p, ?_, ?_⟩
        · rw [chopBlock_refs_of_lt h]; exact hp
        · rw [chopBlock_creator, chopBlock_creator]; exact hpc
  no_equivocation := by
    intro i hi j hj hic hcreator hround
    rw [Finset.mem_filter] at hi hj
    rw [chopBlock_creator] at hic hcreator
    rw [chopBlock_creator] at hcreator
    rw [chopBlock_round, chopBlock_round] at hround
    exact U.no_equivocation i hi.1 j hj.1 hic hcreator (by omega)

@[simp]
theorem mem_chop_ids :
    i ∈ (chop U G).ids ↔ i ∈ U.ids ∧ G ≤ (U.block i).round :=
  Finset.mem_filter

@[simp]
theorem chop_block_eq : (chop U G).block = chopBlock U G := rfl

/-! ## Transfer lemmas: rounds, layers, reachability, cones -/

theorem blocksAt_chop (m : ℕ) :
    blocksAt (chop U G) m = blocksAt U (G + m) := by
  ext i
  simp only [mem_blocksAt, mem_chop_ids, chop_block_eq, chopBlock_round]
  constructor
  · rintro ⟨⟨hi, hG⟩, hr⟩
    exact ⟨hi, by omega⟩
  · rintro ⟨hi, hr⟩
    exact ⟨⟨hi, by omega⟩, by omega⟩

theorem authorsAt_chop (m : ℕ) :
    authorsAt (chop U G) m = authorsAt U (G + m) := by
  unfold authorsAt
  rw [chop_block_eq, blocksAt_chop]
  exact creatorsOf_chopBlock _

/-- A step in the truncation is a step in the original. -/
theorem reaches_of_reaches_chop (h : Reaches (chop U G) b i) :
    Reaches U b i := by
  induction h with
  | refl => exact Reaches.refl
  | tail _ hstep ih =>
      exact ih.trans (Reaches.single (chopBlock_refs_subset hstep))

/-- A path of the original whose endpoint stays at or above the cut never
dips below it, so it survives truncation whole. -/
theorem reaches_chop_of_reaches (hb : b ∈ U.ids) (h : Reaches U b i)
    (hi : G ≤ (U.block i).round) : Reaches (chop U G) b i := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Reaches.refl
  | head hstep hrest ih =>
      rename_i x y
      have hy_ids : y ∈ U.ids := U.complete x hb y hstep
      have hy_round := U.round_of_mem_refs hb hstep
      have hi_le := round_le_of_reaches hy_ids hrest
      refine Relation.ReflTransGen.head ?_ (ih hy_ids)
      show y ∈ (chopBlock U G x).refs
      rw [chopBlock_refs_of_lt (by omega)]
      exact hstep

theorem reaches_chop_iff (hb : b ∈ (chop U G).ids) :
    Reaches (chop U G) b i ↔ Reaches U b i ∧ G ≤ (U.block i).round := by
  rw [mem_chop_ids] at hb
  constructor
  · intro h
    have hi_ids := mem_ids_of_reaches (mem_chop_ids.mpr hb) h
    rw [mem_chop_ids] at hi_ids
    exact ⟨reaches_of_reaches_chop h, hi_ids.2⟩
  · rintro ⟨h, hi⟩
    exact reaches_chop_of_reaches hb.1 h hi

/-- **The cone above the cut**: truncation intersects every cone with the
window. This is the lemma the windowed budget (`garbage.md` G13) and the
statute of limitations both run on. -/
theorem history_chop (hb : b ∈ (chop U G).ids) :
    history (chop U G) b =
      (history U b).filter fun i => G ≤ (U.block i).round := by
  have hbU : b ∈ U.ids := (mem_chop_ids.mp hb).1
  ext i
  rw [mem_history_iff hb, reaches_chop_iff hb, Finset.mem_filter,
    mem_history_iff hbU]

/-! ## The statute of limitations, and its one-way door -/

/-- Exposure in the truncation is exposure in the original: the witnessing
pair survives un-rebasing. -/
theorem exposedIn_of_exposedIn_chop {X : Validator}
    (hb : b ∈ (chop U G).ids) (h : ExposedIn (chop U G) b X) :
    ExposedIn U b X := by
  obtain ⟨x, hx, y, hy, hpair⟩ := h
  rw [history_chop hb, Finset.mem_filter] at hx hy
  have hbU := (mem_chop_ids.mp hb).1
  refine ⟨x, hx.1, y, hy.1, ?_⟩
  obtain ⟨hne, hxc, hyc, hround⟩ := hpair
  refine ⟨hne, ?_, ?_, ?_⟩
  · rw [← chopBlock_creator (U := U) (G := G)]; exact hxc
  · rw [← chopBlock_creator (U := U) (G := G)]; exact hyc
  · have hxG := hx.2
    have hyG := hy.2
    have hr := hround
    rw [chop_block_eq, chopBlock_round, chopBlock_round] at hr
    omega

/-- **G1, DoS half — the one-way door.** The condition survives
truncation; the converse fails by design (the statute of limitations,
witnessed in `LeanDagTest/Chop.lean`). -/
theorem dosValid_chop (hdos : DoSValid U) : DoSValid (chop U G) := by
  intro b hb i hi
  intro hexp
  have hbU := (mem_chop_ids.mp hb).1
  have hiU : i ∈ (U.block b).refs := chopBlock_refs_subset hi
  have := hdos b hbU i hiU
  rw [← chopBlock_creator (U := U) (G := G)] at this
  exact this (exposedIn_of_exposedIn_chop hb hexp)

/-! ## G2 — verdict invariance

Every commit-rule notion for a slot at rebased round `s` (original round
`G + s`) reads only rounds strictly above the base layer, where `chop`
changes nothing but the label. -/

theorem supporters_chop {m : ℕ} (hm : 1 ≤ m) :
    supporters (chop U G) b m = supporters U b (G + m) := by
  unfold supporters
  rw [chop_block_eq, blocksAt_chop, creatorsOf_chopBlock]
  congr 1
  refine Finset.filter_congr fun q hq => ?_
  rw [mem_blocksAt] at hq
  rw [chopBlock_refs_of_lt (by omega)]

theorem blames_chop {L : BlockId} {m : ℕ} (hm : 1 ≤ m) :
    blames (chop U G) L m = blames U L (G + m) := by
  unfold blames
  rw [chop_block_eq, blocksAt_chop, creatorsOf_chopBlock]
  congr 1
  refine Finset.filter_congr fun q hq => ?_
  rw [mem_blocksAt] at hq
  rw [chopBlock_refs_of_lt (by omega)]

theorem votesIn_chop {C L : BlockId} (hC : C ∈ U.ids)
    (hCr : G < (U.block C).round - 1) :
    votesIn (chop U G) C L = votesIn U C L := by
  unfold votesIn
  rw [chop_block_eq, chopBlock_refs_of_lt (by omega)]
  refine Finset.filter_congr fun q hq => ?_
  have := U.round_of_mem_refs hC hq
  rw [chopBlock_refs_of_lt (by omega)]

theorem certifies_chop {C L : BlockId} (hC : C ∈ U.ids)
    (hCr : G < (U.block C).round - 1) :
    Certifies (chop U G) C L ↔ Certifies U C L := by
  unfold Certifies
  rw [votesIn_chop hC hCr, chop_block_eq, creatorsOf_chopBlock]

/-- Certificates for the slot at rebased round `s` are the original
slot's certificates, verbatim. -/
theorem certificates_chop {L : BlockId} (s : ℕ) :
    certificates (chop U G) L s = certificates U L (G + s) := by
  unfold certificates
  rw [blocksAt_chop]
  refine Finset.filter_congr fun C hC => ?_
  rw [mem_blocksAt] at hC
  exact certifies_chop hC.1 (by omega)

theorem directCommit_chop {L : BlockId} (s : ℕ) :
    DirectCommit (chop U G) L s ↔ DirectCommit U L (G + s) := by
  unfold DirectCommit
  rw [certificates_chop, chop_block_eq, creatorsOf_chopBlock]

theorem directSkip_chop {L : BlockId} (s : ℕ) :
    DirectSkip (chop U G) L s ↔ DirectSkip U L (G + s) := by
  unfold DirectSkip
  rw [blames_chop (by omega : 1 ≤ s + 1)]
  exact Iff.rfl

/-- **The indirect test survives the cut**: an anchor above the horizon
certifies a slot above the horizon in the truncation exactly when it did
in the original. With `directCommit_chop`/`directSkip_chop` this is the
per-slot decision invariance of `garbage.md` G3 — the indirect verdict is
a property of the anchor's cone, and never consults the pruned prefix. -/
theorem certifiedIn_chop {A L : BlockId} (hA : A ∈ (chop U G).ids) (s : ℕ) :
    CertifiedIn (chop U G) A L s ↔ CertifiedIn U A L (G + s) := by
  unfold CertifiedIn
  rw [certificates_chop]
  constructor
  · rintro ⟨C, hC, hreach⟩
    exact ⟨C, hC, reaches_of_reaches_chop hreach⟩
  · rintro ⟨C, hC, hreach⟩
    refine ⟨C, hC, ?_⟩
    rw [reaches_chop_iff hA]
    rw [mem_certificates] at hC
    exact ⟨hreach, by omega⟩

end LeanDag
