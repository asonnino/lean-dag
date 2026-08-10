import LeanDag.Reactive.Basic

/-!
# Reactive Mysticeti

The three-round rule, run reactively. The vote stage is `ReactiveCore`'s;
this file adds the certificate stage — a validator that voted waits at
round `r + 2` only until it can certify, with the timeout as the fallback
(`cert_or_wait`) — and derives the direct commit.

The commit rule itself is untouched: `DirectCommit`, `Certifies`,
`Decided` and the whole safety development are consumed as found. What
changes is only where the liveness hypotheses come from. The reference
coverage of the main line (`SynchronisedOn`) is deliberately *not*
available here — a reactive builder omits whatever had not arrived when
its exit condition was met — and it is not needed: the exit conditions
are chosen so that exactly the references the commit rule counts are
present, early exit or fallback alike.

`reactive_decided` is the liveness statement, mirroring the shape of
`decided_of_leader_mem`: a reliable-led slot past GST is committed, with
the population hypotheses supplied by `blk` and the coverage hypothesis
replaced by the two reactive wait clauses.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {D N R : ℕ} {k : ℕ} {L : BlockId}

/-- The reactive three-round schedule: `ReactiveCore`'s vote stage,
plus the certificate wait. -/
structure ReactiveM (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends ReactiveCore U T N where
  /-- **The certificate wait.** At two rounds above a reliable leader,
  either the block already certifies (the reactive exit — its references
  carry a quorum of votes), or its builder waited the full timeout and
  references every reliable vote it holds (the fallback). -/
  cert_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 2 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    Certifies U (blk v (S.slotRound k + 2)) L ∨
      (built v (S.slotRound k + 1) + timeout (S.slotRound k + 1)
          ≤ built v (S.slotRound k + 2) ∧
        ∀ u ∈ T, blk u (S.slotRound k + 1) ∈ holds v (built v (S.slotRound k + 2)) →
          L ∈ (U.block (blk u (S.slotRound k + 1))).refs →
          blk u (S.slotRound k + 1) ∈ (U.block (blk v (S.slotRound k + 2))).refs)

namespace ReactiveM

variable (rm : ReactiveM U T N)

/-- **Every reliable validator certifies.** In the reactive exit the
block certifies by construction. In the fallback, every reliable vote has
arrived — each voter holds its own vote when it builds, convergence
carries it across, and drift plus the full timeout place the arrival
before the fallback build — so the block references all of `T`'s votes,
and `T` is a quorum of distinct authors. -/
theorem certifies (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn rm.built T R D N) (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → D + rm.delay ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    ∀ v ∈ T, Certifies U (rm.blk v (S.slotRound k + 2)) L := by
  intro v hv
  rcases rm.cert_or_wait v hv k hN hlead L hL with hcert | ⟨hwait, hincl⟩
  · exact hcert
  · -- the fallback block references every reliable vote; count them
    have hvotes := rm.toReactiveCore.votes hT hD hgst hto hR (by omega) hlead hL
    have hrefs : ∀ u ∈ T,
        rm.blk u (S.slotRound k + 1) ∈ (U.block (rm.blk v (S.slotRound k + 2))).refs := by
      intro u hu
      refine hincl u hu ?_ (hvotes u hu)
      -- the vote arrives before the fallback build
      have hown := rm.holds_own u hu (S.slotRound k + 1) (by omega)
      have hgstu : rm.gst ≤ rm.built u (S.slotRound k + 1) :=
        le_trans (le_trans hgst (by omega)) (rm.le_built hu _)
      have hconv := rm.converges v hv u hu _ hgstu hown
      refine rm.holds_mono v _ _ ?_ hconv
      have hdrift := hD v hv u hu (S.slotRound k + 1) (by omega) (by omega)
      have := hto (S.slotRound k + 1) (by omega)
      omega
    -- `T ⊆` the vote authors, and `T` is a quorum
    refine le_trans hcard (Finset.card_le_card ?_)
    intro u hu
    refine mem_creatorsOf.mpr ⟨rm.blk u (S.slotRound k + 1), ?_, ?_⟩
    · exact Finset.mem_filter.mpr ⟨hrefs u hu, hvotes u hu⟩
    · exact rm.blk_creator u hu _ (by omega)

/-- **The reactive direct commit.** Every reliable validator's
round-`(r+2)` block certifies, and `T` is a quorum of certificate
authors. -/
theorem directCommit (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn rm.built T R D N) (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → D + rm.delay ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    DirectCommit U L (S.slotRound k) := by
  have hcerts := rm.certifies hT hcard hD hgst hto hR hN hlead hL
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  refine mem_creatorsOf.mpr ⟨rm.blk v (S.slotRound k + 2), ?_, ?_⟩
  · refine Finset.mem_filter.mpr ⟨?_, hcerts v hv⟩
    exact mem_blocksAt.mpr ⟨rm.blk_mem v hv _ (by omega), rm.blk_round v hv _ (by omega)⟩
  · exact rm.blk_creator v hv _ (by omega)

/-- **Reactive liveness (Mysticeti).** A reliable-led slot past GST is
committed by every view — the conclusion of `decided_of_leader_mem`,
with reference coverage replaced by the two reactive wait clauses. The
leader block is the one the schedule names, so its existence is not a
hypothesis. -/
theorem decided (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn rm.built T R D N) (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → D + rm.delay ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  refine ⟨rm.blk (S.leader k) (S.slotRound k), ?_, ?_⟩
  · exact ⟨rm.blk_mem _ hlead _ (by omega), rm.blk_round _ hlead _ (by omega),
      rm.blk_creator _ hlead _ (by omega)⟩
  · have hL : IsLeaderBlock U k (rm.blk (S.leader k) (S.slotRound k)) :=
      ⟨rm.blk_mem _ hlead _ (by omega), rm.blk_round _ hlead _ (by omega),
        rm.blk_creator _ hlead _ (by omega)⟩
    exact Decided.directCommit hL
      (directCommitIn_full (rm.directCommit hT hcard hD hgst hto hR hN hlead hL))

end ReactiveM

end LeanDag
