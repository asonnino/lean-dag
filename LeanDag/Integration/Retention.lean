import LeanDag.Integration.Preservation

/-!
# I7 — anchor retention: how long may a validator be down?

The composition I16 left open, in the order I16 showed is not free:
truncate first, then fill. It has a concrete operational reading.

> A validator crashed at round `r0` and is recovering at round `r`.
> Meanwhile the network garbage-collected below `G`. Can it still
> Safe Skip?

The answer is *iff the anchor survived the cut*. `SkipMsg` requires
`B1 ∈ U.ids`, and `chop` retains `B1` exactly when `G ≤ r0` — so the
garbage-collection horizon must not have passed the round at which the
validator crashed. **The garbage-collection lag is therefore a bound on
the maximum cheaply-recoverable outage**: a validator down longer than
the lag finds its anchor pruned and must bootstrap by report §9.5's
attested base instead of rejoining with one message.

Both directions are proved: `anchor_pruned` (the constraint is real)
and `chopMsg` (it is the only constraint — below the horizon everything
rebases). This is the third of the arc's placement conditions, joining
epoch alignment and horizon-stability from report §13's side.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload} {G : ℕ}

/-! ## I7a — retention is necessary -/

/-- **I7a.** A horizon past the crash round prunes the anchor, and a
pruned anchor cannot be used: every `SkipMsg` over the truncation must
name a different one. This is the constraint, stated sharply. -/
theorem anchor_pruned (sk : SkipMsg U) (hG : (U.block sk.B1).round < G)
    (sk' : SkipMsg (chop U G)) : sk'.B1 ≠ sk.B1 := by
  intro h
  have := sk'.hB1
  rw [h, mem_chop_ids] at this
  omega

/-! ## I7b — retention is sufficient

Below the horizon everything rebases. The construction is the original
message with every round shifted by `−G`: the target round, the donor
line, the fresh identifiers and their decoder. Each field pays the
truncated-subtraction wrinkle of report §9, and each pays it the same
way — the retention hypothesis `G ≤ r0` puts every round in play at or
above the cut, where the subtraction is faithful. -/

/-- **I7b.** With the anchor retained, a Safe Skip message over the
original universe induces one over the truncation: same validators,
same anchor, every round rebased by `−G`. A validator that pruned can
still rejoin with one message. -/
def chopMsg (sk : SkipMsg U) (hG : G ≤ (U.block sk.B1).round)
    (hGr : G ≤ sk.r) : SkipMsg (chop U G) where
  v1 := sk.v1
  B1 := sk.B1
  v2 := sk.v2
  r := sk.r - G
  line k := sk.line (G + k)
  fresh k := sk.fresh (G + k)
  idx b := sk.idx b - G
  hB1uniq := by
    intro j hj hjc hjr
    rw [mem_chop_ids] at hj
    simp only [chop_block_eq, chopBlock_creator] at hjc
    simp only [chop_block_eq, chopBlock_round] at hjr
    exact sk.hB1uniq j hj.1 hjc (by omega)
  hv12 := sk.hv12
  hB1 := mem_chop_ids.mpr ⟨sk.hB1, hG⟩
  hB1c := by simp only [chop_block_eq, chopBlock_creator]; exact sk.hB1c
  hline_mem := by
    intro k hk1 hk2
    simp only [chop_block_eq, chopBlock_round] at hk1
    have hlm := sk.hline_mem (G + k) (by omega) (by omega)
    have hlr := sk.hline_round (G + k) (by omega) (by omega)
    exact mem_chop_ids.mpr ⟨hlm, by omega⟩
  hline_creator := by
    intro k hk1 hk2
    simp only [chop_block_eq, chopBlock_round] at hk1
    simp only [chop_block_eq, chopBlock_creator]
    exact sk.hline_creator (G + k) (by omega) (by omega)
  hline_round := by
    intro k hk1 hk2
    simp only [chop_block_eq, chopBlock_round] at hk1 ⊢
    rw [sk.hline_round (G + k) (by omega) (by omega)]
    omega
  hline_chain := by
    intro k hk1 hk2
    simp only [chop_block_eq, chopBlock_round] at hk1
    -- the line block sits strictly above the cut, so its references survive
    have hlm := sk.hline_mem (G + k) (by omega) (by omega)
    have hlr := sk.hline_round (G + k) (by omega) (by omega)
    have hgt : G < (U.block (sk.line (G + k))).round := by omega
    rw [chop_block_eq, chopBlock_refs_of_lt hgt]
    have := sk.hline_chain (G + k) (by omega) (by omega)
    have hidx : G + k - 1 = G + (k - 1) := by omega
    rwa [hidx] at this
  hfresh_new := by
    intro k
    rw [mem_chop_ids]
    intro h
    exact sk.hfresh_new (G + k) h.1
  hidx := by
    intro k
    rw [sk.hidx (G + k)]
    omega
  hgap := by
    intro b hb hbc hb1 hb2
    rw [mem_chop_ids] at hb
    simp only [chop_block_eq, chopBlock_creator] at hbc
    simp only [chop_block_eq, chopBlock_round] at hb1 hb2
    exact sk.hgap b hb.1 hbc (by omega) (by omega)

/-- The induced message keeps the anchor and the recovering validator,
and its gap is the original's shifted — the statements a caller needs
to connect the two. -/
@[simp] theorem chopMsg_v1 (sk : SkipMsg U) (hG : G ≤ (U.block sk.B1).round)
    (hGr : G ≤ sk.r) :
    (chopMsg sk hG hGr).v1 = sk.v1 := rfl

@[simp] theorem chopMsg_B1 (sk : SkipMsg U) (hG : G ≤ (U.block sk.B1).round)
    (hGr : G ≤ sk.r) :
    (chopMsg sk hG hGr).B1 = sk.B1 := rfl

@[simp] theorem chopMsg_r (sk : SkipMsg U) (hG : G ≤ (U.block sk.B1).round)
    (hGr : G ≤ sk.r) :
    (chopMsg sk hG hGr).r = sk.r - G := rfl

/-- The rebased crash round: the truncation sees the gap starting `G`
lower, as it sees every round. -/
theorem chopMsg_r0 (sk : SkipMsg U) (hG : G ≤ (U.block sk.B1).round)
    (hGr : G ≤ sk.r) : (chopMsg sk hG hGr).r0 = sk.r0 - G := by
  simp only [SkipMsg.r0, chopMsg_B1, chop_block_eq, chopBlock_round]

/-! ## The deployment reading

§9 keeps a validator's horizon trailing its current round by a lag `Λ`
(`card_retained_le` is stated at that lag). Composing that with the
retention condition turns I7 into a statement an operator can act on. -/

/-- **The lag bounds the recoverable outage.** With the horizon trailing
the recovery round by `Λ`, the anchor survives exactly when the outage
did not exceed `Λ`.

So the two mechanisms are coupled by one inequality: *garbage collection
at lag `Λ` supports Safe Skip recovery from outages of up to `Λ` rounds,
and no more.* Beyond it the validator's last block has been pruned and
it must bootstrap by report §9.5's attested base — which is why the two
routes exist, and where the boundary between them falls. -/
theorem outage_bounded_by_lag (sk : SkipMsg U) {Λ : ℕ}
    (hlag : G + Λ = sk.r) (hr : sk.r0 ≤ sk.r) :
    G ≤ sk.r0 ↔ sk.r - sk.r0 ≤ Λ := by
  unfold SkipMsg.r0 at *
  omega

end Integration

end LeanDag
