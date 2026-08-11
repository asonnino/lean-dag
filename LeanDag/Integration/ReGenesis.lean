import LeanDag.Integration.Retention

/-!
# Re-genesis: restarting a severed chain at the cut

`severed_of_pruned_anchor` showed that a validator whose whole history
fell below a horizon can produce nothing in the truncation: P3′ demands
a self-parent, and it has no block to chain from. The natural repair is
to let it start a fresh chain *at the cut*, with a block carrying no
references at all — and the repair costs nothing to justify, because
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
§9 keeps horizons per-validator and deliberately reaches no agreement
on the cut, so this is a genuine interaction rather than a detail: a
re-genesis convention needs the *lagging* validators — those retaining
more history — to accept a block their own rules reject. That is the
one thing the construction below cannot supply, and it is recorded in
`integration.md` §5.7 rather than papered over.
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

end Integration

end LeanDag
