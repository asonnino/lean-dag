import LeanDag.Integration.Retention
import LeanDag.GC.Horizon

/-!
# Re-genesis: restarting a severed chain at the cut

`severed_of_pruned_anchor` showed that a validator whose whole history
fell below a horizon can produce nothing in the truncation: P3′ demands
a self-parent, and it has no block to chain from. The natural repair is
to let it start a fresh chain *at the cut*, with a block carrying no
references at all — and the repair needs no new justification, because
the truncation's base layer is already exactly that.

`chop`'s own validity proof discharges the retained layer with "no
references, nothing to prove": the rebasing puts those blocks at round
`0`, where P1, P3 and P3′ are all guarded by `0 < round` and P2 is
vacuous for an empty reference set. A re-genesis block is therefore
indistinguishable, to the validity rules, from any block the cut
flattened — so it needs no exemption from P3′, and the clause survives
intact.

There is a pleasing symmetry in the non-equivocation obligation. Adding
a genesis block for a validator would normally risk a twin at round
`0`; here the very fact that stranded the validator — its total absence
from the truncation — is what makes the new block unambiguous.

**The condition this carries.** A re-genesis block is valid *in the
truncation* and not in the universe it came from: at round `G > 0` of
the original, a reference-free block violates P3. So it is acceptable
only to validators that have themselves pruned to at least `G`. Report
report §9 keeps horizons per-validator and deliberately reaches no agreement
on the cut, so this is a genuine interaction rather than a detail: a
re-genesis convention needs the *lagging* validators — those retaining
more history — to accept a block their own rules reject. That is the
one thing the construction below cannot supply, and it is recorded in
`integration.md` report §5.7 rather than papered over.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **Re-genesis.** A universe extended with one reference-free block at
round `0`, for a validator that has none.

The hypotheses are exactly what the construction needs and no more: the
identifier must be fresh, and the validator must be absent — which for
a stranded validator is `severed_of_pruned_anchor`. -/
def addGenesis (V : BlockUniverse Validator BlockId Payload) (v : Validator)
    (g : BlockId) (p : Payload) (hg : g ∉ V.ids)
    (hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v) :
    BlockUniverse Validator BlockId Payload where
  ids := insert g V.ids
  block b := if b ∈ V.ids then V.block b else ⟨0, v, ∅, p⟩
  complete := by
    intro i hi j hj
    rcases Finset.mem_insert.mp hi with rfl | ho
    · -- the new block references nothing
      rw [if_neg hg] at hj
      exact absurd hj (Finset.notMem_empty j)
    · rw [if_pos ho] at hj
      exact Finset.mem_insert_of_mem (V.complete i ho j hj)
  valid := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | ho
    · -- round `0` with no references: every clause is vacuous
      rw [if_neg hg]
      refine ⟨?_, ?_, ?_, ?_⟩ <;>
        first
          | (intro j hj; exact absurd hj (Finset.notMem_empty j))
          | (intro hr; exact absurd hr (by simp))
    · rw [if_pos ho]
      have hv := V.valid i ho
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro j hj
        rw [if_pos (V.complete i ho j hj)]
        exact hv.predecessor j hj
      · intro a ha b hb hab
        rw [if_pos (V.complete i ho a ha), if_pos (V.complete i ho b hb)] at hab
        exact hv.distinct_creators a ha b hb hab
      · intro hr
        refine le_trans (hv.quorum hr) (Finset.card_le_card ?_)
        intro c hc
        unfold creators creatorsOf at hc ⊢
        obtain ⟨j, hj, hjc⟩ := Finset.mem_image.mp hc
        refine Finset.mem_image.mpr ⟨j, hj, ?_⟩
        simp only
        rw [if_pos (V.complete i ho j hj)]
        exact hjc
      · intro hr
        obtain ⟨j, hj, hjc⟩ := hv.self_parent hr
        exact ⟨j, hj, by rw [if_pos (V.complete i ho j hj)]; exact hjc⟩
  no_equivocation := by
    intro i hi j hj hic hcc hrr
    rcases Finset.mem_insert.mp hi with rfl | ho <;>
      rcases Finset.mem_insert.mp hj with rfl | ho'
    · rfl
    · -- the new block against an old one: the old author cannot be `v`
      rw [if_neg hg] at hcc
      rw [if_pos ho'] at hcc
      exact absurd hcc.symm (hsev j ho')
    · rw [if_pos ho] at hcc
      rw [if_neg hg] at hcc
      exact absurd hcc (hsev i ho)
    · rw [if_pos ho] at hic hcc hrr
      rw [if_pos ho'] at hcc hrr
      exact V.no_equivocation i ho j ho' hic hcc hrr

variable {V : BlockUniverse Validator BlockId Payload} {v : Validator}
variable {g : BlockId} {p : Payload}

@[simp] theorem addGenesis_block_old {hg : g ∉ V.ids}
    {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v} {b : BlockId} (hb : b ∈ V.ids) :
    (addGenesis V v g p hg hsev).block b = V.block b := if_pos hb

@[simp] theorem addGenesis_block_new {hg : g ∉ V.ids}
    {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v} :
    (addGenesis V v g p hg hsev).block g = ⟨0, v, ∅, p⟩ := if_neg hg

theorem mem_addGenesis {hg : g ∉ V.ids}
    {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v} :
    g ∈ (addGenesis V v g p hg hsev).ids := Finset.mem_insert_self _ _

/-- **The chain restarts.** After re-genesis the stranded validator has
a block at round `0`, so it is no longer severed: `no_blocks_of_no_genesis`
no longer applies to it, and an ordinary Safe Skip anchored on the new
block fills the rounds above.

Stated as the population fact liveness consumes — the validator is back
in the genesis layer, which is the hypothesis P8 asks for at round
`0`. -/
theorem populatedOn_addGenesis {hg : g ∉ V.ids}
    {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v} {T : Finset Validator}
    (hpop : PopulatedOn V T 0) :
    PopulatedOn (addGenesis V v g p hg hsev) (insert v T) 0 := by
  intro w hw
  rcases Finset.mem_insert.mp hw with rfl | hwT
  · exact ⟨g, mem_addGenesis, by rw [addGenesis_block_new], by rw [addGenesis_block_new]⟩
  · obtain ⟨b, hb, hbc, hbr⟩ := hpop w hwT
    exact ⟨b, Finset.mem_insert_of_mem hb,
      by rw [addGenesis_block_old hb]; exact hbc,
      by rw [addGenesis_block_old hb]; exact hbr⟩

/-- Re-genesis is available exactly to a stranded validator: the
absence hypothesis it needs is what `severed_of_pruned_anchor`
supplies. The composite says a validator pruned past its own history
can restart at the cut — the provision report §12 lacks. -/
def addGenesis_of_severed {U : BlockUniverse Validator BlockId Payload}
    {G : ℕ} (sk : SkipMsg U) (hG1 : sk.r0 < G) (hG2 : G ≤ sk.r)
    (g : BlockId) (p : Payload) (hg : g ∉ (chop U G).ids) :
    BlockUniverse Validator BlockId Payload :=
  addGenesis (chop U G) sk.v1 g p hg (severed_of_pruned_anchor sk hG1 hG2)

/-! ## I19 — the exposure condition survives re-genesis

Report report §2.2 credits P3′ to report §8 because the self-parent chain makes a
correct block's cone a complete record of its author's acceptances —
and re-genesis deliberately severs that chain, so the completeness is
locally false after it. The question is whether report §8's *conditions* still
hold, and the answer at the universe level is yes, for a reason worth
stating: **the re-genesis block has no references at all.**

It therefore cannot reference an exposed author (the clause is vacuous
for it), and it enters no other block's cone (nothing reaches it, since
nothing references it). `DoSValid` is untouched in both directions.

This is the sharpest contrast with the fill, whose predicted failure
(report §5.6, I1) comes from precisely the opposite property: `fillBlock`
inserts a self reference and so *enlarges* the cone. Adding a block
with no references is safe for cone-based conditions; adding one with
references is not.
-/

section Exposure

variable {V : BlockUniverse Validator BlockId Payload} {v : Validator}
variable {g : BlockId} {p : Payload}
variable {hg : g ∉ V.ids} {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v}

/-- Reachability is unchanged among old blocks: the new block
references nothing, and nothing references it. -/
theorem reaches_addGenesis {b i : BlockId} (hb : b ∈ V.ids) :
    Reaches (addGenesis V v g p hg hsev) b i ↔ Reaches V b i := by
  constructor
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y _ hstep ih =>
        -- every block reached from an old one is old, so the step is `V`'s
        have hxo : x ∈ V.ids := by
          clear ih hstep
          induction ‹Relation.ReflTransGen _ b x› with
          | refl => exact hb
          | @tail u w _ hs' ih' =>
              unfold RefStep at hs'
              rw [addGenesis_block_old ih'] at hs'
              exact V.complete _ ih' _ hs'
        unfold RefStep at hstep
        rw [addGenesis_block_old hxo] at hstep
        exact ih.tail hstep
  · intro h
    induction h with
    | refl => exact Relation.ReflTransGen.refl
    | @tail x y hr hstep ih =>
        have hxo : x ∈ V.ids := mem_ids_of_reaches hb hr
        refine ih.tail ?_
        unfold RefStep
        rw [addGenesis_block_old hxo]
        exact hstep

/-- Cones are unchanged, so every cone-based condition reads the same. -/
theorem history_addGenesis {b : BlockId} (hb : b ∈ V.ids) :
    history (addGenesis V v g p hg hsev) b = history V b := by
  ext i
  rw [mem_history_iff (Finset.mem_insert_of_mem hb), mem_history_iff hb]
  exact reaches_addGenesis hb

/-- **I19a.** Re-genesis preserves the exposure condition. A block with
no references can neither cite an exposed author nor enlarge anyone
else's cone, so report §8's per-cone bound applies to the extended universe
unchanged. -/
theorem dosValid_addGenesis (hdos : DoSValid V) :
    DoSValid (addGenesis V v g p hg hsev) := by
  intro b hb i hi hexp
  rcases Finset.mem_insert.mp hb with rfl | ho
  · -- the new block references nothing
    rw [addGenesis_block_new] at hi
    exact absurd hi (Finset.notMem_empty i)
  · -- an old block: its cone, and every block in it, reads as before
    rw [addGenesis_block_old ho] at hi
    obtain ⟨x, hx, y, hy, hxy⟩ := hexp
    rw [history_addGenesis ho] at hx hy
    refine hdos b ho i hi ⟨x, hx, y, hy, ?_⟩
    obtain ⟨hne, hxc, hyc, hr⟩ := hxy
    have hxo : x ∈ V.ids := mem_ids_of_reaches ho ((mem_history_iff ho).mp hx)
    have hyo : y ∈ V.ids := mem_ids_of_reaches ho ((mem_history_iff ho).mp hy)
    rw [addGenesis_block_old hxo] at hxc hr
    rw [addGenesis_block_old hyo] at hyc hr
    rw [addGenesis_block_old (V.complete b ho i hi)] at *
    exact ⟨hne, hxc, hyc, hr⟩

end Exposure

/-! ## Convergence: local derivation needs no agreement

The condition of report §5.7 — that a re-genesis block is valid only to
validators who have pruned at least as far — dissolves if the block is
**derived rather than transmitted**. Let each validator synthesise a
genesis for any validator absent from its own retained layer, as a
deterministic function of its own horizon. Nothing is sent, so nothing
can be rejected.

What must then be true is that the derivations *converge*: a validator
holding more history, on truncating further, must arrive at what the
more-truncated validator already had. It does, and cleanly. Its own
derived genesis sits at round `0` and is pruned by any further cut,
leaving exactly the later validator's base — on which the same
derivation produces the same genesis.

So heterogeneous horizons stay compatible with no agreement on the cut,
which is report §9's design constraint, and the re-genesis convention
is a local rule rather than a protocol message. -/

section Convergence

variable {V : BlockUniverse Validator BlockId Payload} {v : Validator}
variable {g : BlockId} {p : Payload} {d : ℕ}

/-- **A derived genesis is pruned by the next cut, without trace.** Any
further truncation removes the round-`0` block and leaves the ordinary
truncation of what lay beneath.

Stated observationally — identifiers, and blocks at those identifiers —
because the two universes differ on the junk outside their identifier
sets, which nothing consults. -/
theorem chop_addGenesis (hd : 0 < d)
    {hg : g ∉ V.ids} {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v} :
    (chop (addGenesis V v g p hg hsev) d).ids = (chop V d).ids
      ∧ ∀ b ∈ (chop V d).ids,
          (chop (addGenesis V v g p hg hsev) d).block b = (chop V d).block b := by
  constructor
  · ext b
    rw [mem_chop_ids, mem_chop_ids]
    constructor
    · rintro ⟨hb, hbr⟩
      rcases Finset.mem_insert.mp hb with rfl | ho
      · rw [addGenesis_block_new] at hbr
        change d ≤ 0 at hbr
        omega
      · rw [addGenesis_block_old ho] at hbr
        exact ⟨ho, hbr⟩
    · rintro ⟨hb, hbr⟩
      exact ⟨Finset.mem_insert_of_mem hb, by rw [addGenesis_block_old hb]; exact hbr⟩
  · intro b hb
    rw [mem_chop_ids] at hb
    simp only [chop_block_eq, chopBlock, addGenesis_block_old hb.1]

/-- **The convergence.** A validator at horizon `G₁`, truncating on to a
later horizon `G₂`, holds exactly the blocks of a validator that cut at
`G₂` directly — its derived genesis having been pruned on the way. Both
then derive the same genesis from the same base, so heterogeneous
horizons need no agreement.

The identifier sets are equal and the blocks agree on them; the two
universes are the same object as far as anything that reads them is
concerned. -/
theorem regenesis_converges {U : BlockUniverse Validator BlockId Payload}
    {G₁ G₂ : ℕ} (hG : G₁ < G₂)
    {hg : g ∉ (chop U G₁).ids}
    {hsev : ∀ b ∈ (chop U G₁).ids, ((chop U G₁).block b).creator ≠ v} :
    (chop (addGenesis (chop U G₁) v g p hg hsev) (G₂ - G₁)).ids
        = (chop U G₂).ids
      ∧ ∀ b ∈ (chop U G₂).ids,
          (chop (addGenesis (chop U G₁) v g p hg hsev) (G₂ - G₁)).block b
            = (chop U G₂).block b := by
  obtain ⟨hids, hblk⟩ := chop_addGenesis (V := chop U G₁) (v := v) (g := g)
    (p := p) (d := G₂ - G₁) (by omega) (hg := hg) (hsev := hsev)
  rw [chop_chop (le_of_lt hG)] at hids hblk
  exact ⟨hids, hblk⟩

end Convergence

/-! ## Re-genesis and Safe Skip compose: the full recovery

The three mechanisms are complementary rather than alternative, and a
long outage uses all of them in order:

1. **bootstrap** to read — report §9.5's attested base gives the
   returning validator a view whose verdicts agree with everyone's
   (`bootstrap_agree`), but not the ability to produce;
2. **re-genesis** to write — a block at the cut, restoring it to the
   genesis layer (`addGenesis`), which is what P3′ was blocking;
3. **Safe Skip** to catch up — one message denoting every block from
   the cut to the current round, which is report §12's mechanism doing
   exactly the job it was built for, at a gap that now begins at the
   horizon rather than at the crash.

The third step needs an anchor, and the re-genesis block is one. The
closure is pleasing: `hsev`, the total absence that licensed
re-genesis, is precisely what discharges `hB1uniq` — a validator with
no other block anywhere cannot have a second block at the anchor's
round. Nothing extra is assumed.

What every party needs, for the fill to denote anything, is the
retained history including the donor's line up to the target block.
That is the standing requirement of a `SkipMsg` (`hline_mem`), and
after garbage collection it is satisfied by exactly the window
everyone keeps. -/

section Recovery

variable {V : BlockUniverse Validator BlockId Payload} {v : Validator}
variable {g : BlockId} {p : Payload}
variable {hg : g ∉ V.ids} {hsev : ∀ b ∈ V.ids, (V.block b).creator ≠ v}

/-- **The re-genesis block is a lawful Safe Skip anchor.** Uniqueness
at its round is immediate from the absence that licensed it. -/
theorem hB1uniq_of_addGenesis :
    ∀ j ∈ (addGenesis V v g p hg hsev).ids,
      ((addGenesis V v g p hg hsev).block j).creator = v →
      ((addGenesis V v g p hg hsev).block j).round
        = ((addGenesis V v g p hg hsev).block g).round → j = g := by
  intro j hj hjc _
  rcases Finset.mem_insert.mp hj with rfl | ho
  · rfl
  · rw [addGenesis_block_old ho] at hjc
    exact absurd hjc (hsev j ho)

/-- **The catch-up fill.** After re-genesis the returning validator
rejoins production with one message: a `SkipMsg` anchored on its new
genesis block, filling every round from the cut to the target.

The donor data is the ordinary requirement — a line of `v2` blocks
from the anchor's round to the target, each citing the one below,
all of them in the retained window that every validator holds. The two
clauses peculiar to recovery come at no cost: `hB1uniq` from
`hB1uniq_of_addGenesis`, and `hgap` from the absence itself, since a
validator with no blocks authored none during the gap either. -/
def recoveryMsg (r : ℕ) (line fresh : ℕ → BlockId) (idx : BlockId → ℕ)
    (v2 : Validator) (hv12 : v ≠ v2)
    (hline_mem : ∀ k, k ≤ r → line k ∈ V.ids)
    (hline_creator : ∀ k, k ≤ r → (V.block (line k)).creator = v2)
    (hline_round : ∀ k, k ≤ r →
      (V.block (line k)).round = ((addGenesis V v g p hg hsev).block g).round + k)
    (hline_chain : ∀ k, 0 < k → k ≤ r → line (k - 1) ∈ (V.block (line k)).refs)
    (hfresh_new : ∀ k, fresh k ∉ (addGenesis V v g p hg hsev).ids)
    (hidx : ∀ k, idx (fresh k) = k) :
    SkipMsg (addGenesis V v g p hg hsev) where
  v1 := v
  B1 := g
  v2 := v2
  r := ((addGenesis V v g p hg hsev).block g).round + r
  line k := line (k - ((addGenesis V v g p hg hsev).block g).round)
  fresh := fresh
  idx := idx
  hB1uniq := hB1uniq_of_addGenesis
  hv12 := hv12
  hB1 := mem_addGenesis
  hB1c := by rw [addGenesis_block_new]
  hline_mem := by
    intro k hk1 hk2
    exact Finset.mem_insert_of_mem (hline_mem _ (by omega))
  hline_creator := by
    intro k hk1 hk2
    rw [addGenesis_block_old (hline_mem _ (by omega))]
    exact hline_creator _ (by omega)
  hline_round := by
    intro k hk1 hk2
    rw [addGenesis_block_old (hline_mem _ (by omega))]
    rw [hline_round _ (by omega)]
    omega
  hline_chain := by
    intro k hk1 hk2
    rw [addGenesis_block_old (hline_mem _ (by omega))]
    have := hline_chain (k - ((addGenesis V v g p hg hsev).block g).round)
      (by omega) (by omega)
    have hidx' : k - ((addGenesis V v g p hg hsev).block g).round - 1
        = k - 1 - ((addGenesis V v g p hg hsev).block g).round := by omega
    rwa [hidx'] at this
  hfresh_new := hfresh_new
  hidx := hidx
  hgap := by
    intro b hb hbc _ _
    rcases Finset.mem_insert.mp hb with rfl | ho
    · rw [addGenesis_block_new] at *
      omega
    · rw [addGenesis_block_old ho] at hbc
      exact absurd hbc (hsev b ho)

end Recovery

end Integration

end LeanDag
