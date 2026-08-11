import LeanDag.Integration.Preservation

/-!
# I5 — the fill does not restore coverage, and why that is correct

`integration.md` predicted this cell would come out negative and
proposed exhibiting a counterexample on data. It is in fact refutable
*in general*, which is a better outcome: `not_synchronisedOn_skipFill`
shows coverage fails at every gap round of every fill, on no
hypotheses beyond the ones that make the fill worth doing.

The reason is worth stating carefully, because it is the same fact that
makes Safe Skip **safe**. SS3 (`directSkip_fresh`) turns on the
observation that no old block can reference a fresh identifier — the
old blocks were built before the fill existed — and concludes that a
filled block landing on a leader slot is always directly skipped, so
the mechanism cannot conjure a commit. Coverage asks for the opposite:
that every reliable block at round `n+1` reference every reliable block
at round `n`. At a gap round the fill supplies a reliable block that
the round above provably does not reference. **One fact, two
consequences**: the fill cannot manufacture a commit, and the fill
cannot manufacture coverage.

This is not a defect, and it does not weaken report §12. Safe Skip's claim is
that it restores *production* (`PopulatedOn`, SS2) — the hypothesis
liveness actually consumes — and it makes no claim about coverage.
Coverage is restored the ordinary way, by the network, once the
recovered validator is building again: `synchronisedOn_skipFill_above`
gives it for every round past the fill.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- Above the fill every block is an old one: the fresh identifiers
occupy gap rounds only. -/
theorem mem_ids_of_round_gt (sk : SkipMsg U) {b : BlockId}
    (hb : b ∈ sk.skipFill.ids) (hround : sk.r < (sk.skipFill.block b).round) :
    b ∈ U.ids := by
  rcases Finset.mem_union.mp hb with ho | hf
  · exact ho
  · obtain ⟨k, hk1, hk2, rfl⟩ := sk.mem_freshIds.mp hf
    rw [sk.skipFill_block_fresh] at hround
    simp only [SkipMsg.fillBlock] at hround
    omega

/-- **I5, refuted.** The fill does not restore coverage. If the
recovering validator is counted reliable — which is exactly what SS2
does — then at any gap round `k` above the coverage round, an old
reliable block at `k+1` fails to reference the filled block at `k`,
because no old block references a fresh identifier.

The hypotheses are the situation SS2 creates, not a contrived one:
`hv1` puts `v1` in the reliable set, `hk` places the gap round in the
covered range, and `hb` asks only that some reliable validator built
at the round above — which `PopulatedOn` supplies. -/
theorem not_synchronisedOn_skipFill (sk : SkipMsg U) {T : Finset Validator}
    {R k : ℕ} (hv1 : sk.v1 ∈ T) (hk1 : sk.r0 < k) (hk2 : k ≤ sk.r) (hk : R ≤ k)
    {b : BlockId} (hb : b ∈ U.ids) (hbround : (U.block b).round = k + 1)
    (hbc : (U.block b).creator ∈ T) :
    ¬ SynchronisedOn sk.skipFill T R := by
  intro hs
  -- the filled block is a reliable block at round `k`
  have hfresh_mem : sk.fresh k ∈ sk.skipFill.ids :=
    Finset.mem_union_right _ (sk.mem_freshIds.mpr ⟨k, hk1, hk2, rfl⟩)
  have hfresh_round : (sk.skipFill.block (sk.fresh k)).round = k := by
    rw [sk.skipFill_block_fresh]; rfl
  have hfresh_creator : (sk.skipFill.block (sk.fresh k)).creator = sk.v1 := by
    rw [sk.skipFill_block_fresh]; rfl
  -- coverage would force the old block above to reference it
  have := hs k hk b (sk.ids_subset_skipFill hb)
    (by rw [sk.skipFill_block_old hb]; exact hbround)
    (by rw [sk.skipFill_block_old hb]; exact hbc)
    (sk.fresh k) hfresh_mem hfresh_round (by rw [hfresh_creator]; exact hv1)
  -- but an old block's references are old identifiers
  rw [sk.skipFill_block_old hb] at this
  exact sk.hfresh_new k (U.complete b hb _ this)

/-- **The refutation is narrow: it is about counting the recovering
validator reliable during the gap it slept through.** Exclude it from
the reliable set and coverage is untouched — the fill's blocks are its
alone, so the clause never quantifies over them.

Together with `not_synchronisedOn_skipFill` and
`synchronisedOn_skipFill_above` this is the whole picture. Coverage
fails only where it should: over a set that includes the recovering
validator, at rounds during which it was absent. It holds for every
other set, and for every set above the fill. -/
theorem synchronisedOn_skipFill_of_notMem (sk : SkipMsg U) {T : Finset Validator}
    {R : ℕ} (hs : SynchronisedOn U T R) (hv1 : sk.v1 ∉ T) :
    SynchronisedOn sk.skipFill T R := by
  intro n hn b hb hbround hbc a ha haround hac
  have hbo : b ∈ U.ids := by
    rcases Finset.mem_union.mp hb with ho | hf
    · exact ho
    · obtain ⟨k, _, _, rfl⟩ := sk.mem_freshIds.mp hf
      rw [sk.skipFill_block_fresh] at hbc
      exact absurd hbc (by simpa [SkipMsg.fillBlock] using hv1)
  have hao : a ∈ U.ids := by
    rcases Finset.mem_union.mp ha with ho | hf
    · exact ho
    · obtain ⟨k, _, _, rfl⟩ := sk.mem_freshIds.mp hf
      rw [sk.skipFill_block_fresh] at hac
      exact absurd hac (by simpa [SkipMsg.fillBlock] using hv1)
  rw [sk.skipFill_block_old hbo] at hbround hbc ⊢
  rw [sk.skipFill_block_old hao] at haround hac
  exact hs n hn b hbo hbround hbc a hao haround hac


/-- **I5, positively.** Coverage holds *strictly* above the fill: past
the target round every block is old, references are preserved, and the
original condition applies unchanged. This is the form a liveness
argument after recovery consumes — the recovered validator is building
its own blocks again, and the network covers them in the ordinary way.

The strictness is not slack in the proof. At `n = sk.r` the lower
block may still be the last filled one, and
`not_synchronisedOn_skipFill` refutes coverage there; `sk.r < R'` is
exactly the first round at which every block in play is old. -/
theorem synchronisedOn_skipFill_above (sk : SkipMsg U) {T : Finset Validator}
    {R R' : ℕ} (hs : SynchronisedOn U T R) (hR : R ≤ R') (hR' : sk.r < R') :
    SynchronisedOn sk.skipFill T R' := by
  intro n hn b hb hbround hbc a ha haround hac
  -- both blocks sit above the fill, hence are old
  have hbo : b ∈ U.ids := mem_ids_of_round_gt sk hb (by omega)
  have hao : a ∈ U.ids := mem_ids_of_round_gt sk ha (by omega)
  rw [sk.skipFill_block_old hbo] at hbround hbc ⊢
  rw [sk.skipFill_block_old hao] at haround hac
  exact hs n (by omega) b hbo hbround hbc a hao haround hac

end Integration

end LeanDag
