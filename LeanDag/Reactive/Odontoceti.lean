import LeanDag.Reactive.Basic
import LeanDag.Odontoceti.Liveness

/-!
# Reactive Odontoceti

The two-round rule, run reactively. Odontoceti has no certificate stage —
its direct commit counts *supporters* at the round above the leader — so
the vote stage of `ReactiveCore` is the entire reactive protocol: a
validator waits at `r + 1` only until it holds the leader's block, with
the timeout as the fallback, and no further wait exists to react out of.

That makes the two-round protocol the natural home of the reactive
discipline. Under Mysticeti a fast slot still crosses two reactive exits;
here it crosses one, and the latency of a fast slot is a single
delivery plus processing (`ReactiveCore.built_succ_le_of_fast`).

As with the Mysticeti file, the commit rule is consumed as found — in
particular `Odontoceti.Decided` with its canonicity premise — and the
`Faults5` committee is required only where the rule requires it, not by
the schedule.
-/

namespace LeanDag

namespace Odontoceti

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults5 Validator]
variable {BlockId : Type*} [LinearOrder BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {D N R : ℕ} {k : ℕ} {L : BlockId}

/-- **The reactive direct commit (Odontoceti).** Every reliable
validator votes (`ReactiveCore.votes`), a vote is a support, and `T` is
a quorum of supporters. -/
theorem reactive_directCommit (rc : ReactiveCore U T N)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn rc.built T R D N) (hgst : rc.gst ≤ R)
    (hto : ∀ n, R ≤ n → D + rc.delay ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    DirectCommit U L (S.slotRound k) := by
  have hvotes := rc.votes hT hD hgst hto hR hN hlead hL
  refine le_trans hcard (le_trans (Finset.card_le_card ?_)
    (le_of_eq rfl))
  intro v hv
  rw [mem_supporters]
  exact ⟨rc.blk v (S.slotRound k + 1), rc.blk_mem v hv _ hN,
    rc.blk_round v hv _ hN, hvotes v hv,
    rc.blk_creator v hv _ hN⟩

/-- **Reactive liveness (Odontoceti).** A reliable-led slot past GST is
committed by every view — the conclusion of the two-round
`decided_of_leader_mem`, from the single reactive wait clause. One
delivery separates a fast leader from its commit. -/
theorem reactive_decided (rc : ReactiveCore U T N)
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn rc.built T R D N) (hgst : rc.gst ≤ R)
    (hto : ∀ n, R ≤ n → D + rc.delay ≤ rc.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 1 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  refine ⟨rc.blk (S.leader k) (S.slotRound k), ?_, ?_⟩
  · exact ⟨rc.blk_mem _ hlead _ (by omega), rc.blk_round _ hlead _ (by omega),
      rc.blk_creator _ hlead _ (by omega)⟩
  · have hL : IsLeaderBlock U k (rc.blk (S.leader k) (S.slotRound k)) :=
      ⟨rc.blk_mem _ hlead _ (by omega), rc.blk_round _ hlead _ (by omega),
        rc.blk_creator _ hlead _ (by omega)⟩
    exact Decided.directCommit hL
      (directCommitIn_full
        (reactive_directCommit rc hT hcard hD hgst hto hR hN hlead hL))

end Odontoceti

end LeanDag
