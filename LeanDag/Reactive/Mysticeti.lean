import LeanDag.Reactive.Basic

/-!
# Reactive Mysticeti

The three-round rule, run reactively. The vote stage is `ReactivePace`'s;
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
present, early exit and fallback alike.

`reactive_decided` is the liveness statement, mirroring the shape of
`decided_of_leader_mem`: a reliable-led slot past GST is committed, with
the population hypotheses supplied by the trunk's derived production
(`PaceCore.populatedOn`) and the coverage hypothesis replaced by the two
reactive wait clauses.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {D N R : ℕ} {k : ℕ} {L : BlockId}

/-- The reactive three-round schedule: `ReactivePace`'s vote stage,
plus the certificate wait, stated over any `T`-authored block. -/
structure ReactiveM (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends ReactivePace U T N where
  /-- **The certificate wait.** At two rounds above a reliable leader,
  any `T`-authored block either already certifies (the reactive exit —
  its references carry a quorum of votes), or its builder waited the
  full timeout and references every reliable vote it holds (the
  fallback). -/
  cert_or_wait : ∀ v ∈ T, ∀ k : ℕ, S.slotRound k + 2 ≤ N → S.leader k ∈ T →
    ∀ L, IsLeaderBlock U k L →
    ∀ c ∈ U.ids, (U.block c).creator = v → (U.block c).round = S.slotRound k + 2 →
    Certifies U c L ∨
      (built v (S.slotRound k + 1) + timeout (S.slotRound k + 1)
          ≤ built v (S.slotRound k + 2) ∧
        ∀ b ∈ U.ids, (U.block b).creator ∈ T →
          (U.block b).round = S.slotRound k + 1 →
          b ∈ holds v (built v (S.slotRound k + 2)) →
          L ∈ (U.block b).refs → b ∈ (U.block c).refs)

namespace ReactiveM

variable (rm : ReactiveM U T N)

/-- **Every reliable certificate block certifies.** In the reactive exit
the block certifies by construction. In the fallback, every reliable vote
has arrived — each voter holds its own vote when it builds, convergence
carries it across, and drift plus the full timeout place the arrival
before the fallback build — so the block references all of `T`'s votes,
and `T` is a quorum of distinct authors.

The vote blocks themselves come from the trunk's derived production
(`PaceCore.populatedOn`): nothing here assumes a block exists. -/
theorem certifies (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn rm.built T R D N) (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → D + rm.delay ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    ∀ v ∈ T, ∀ c ∈ U.ids, (U.block c).creator = v →
      (U.block c).round = S.slotRound k + 2 → Certifies U c L := by
  intro v hv c hc hcc hcr
  rcases rm.cert_or_wait v hv k hN hlead L hL c hc hcc hcr with hcert | ⟨hwait, hincl⟩
  · exact hcert
  · -- the fallback block references every reliable vote; count them
    have hvotes := rm.toReactivePace.votes hT hD hgst hto hR (by omega) hlead hL
    -- each `u ∈ T` has a vote block, by derived production
    have hpop := rm.toPaceCore.populatedOn hcard (S.slotRound k + 1) (by omega)
    refine le_trans hcard (Finset.card_le_card ?_)
    intro u hu
    obtain ⟨b, hb, hbc, hbr⟩ := hpop u hu
    have hvote : L ∈ (U.block b).refs := hvotes u hu b hb hbc hbr
    have harrive : b ∈ rm.holds v (rm.built v (S.slotRound k + 2)) := by
      have hown := rm.holds_own u hu (S.slotRound k + 1) (by omega) b hb hbc hbr
      have htopu : S.slotRound k + 1 ≤ rm.top u := by
        have := rm.le_top_of_built u hu b hb hbc
        omega
      have hgstu : rm.gst ≤ rm.built u (S.slotRound k + 1) :=
        le_trans (le_trans hgst (by omega)) (rm.le_built hu _ htopu)
      have hconv := rm.converges v hv u hu _ hgstu hown
      refine rm.holds_mono v _ _ ?_ hconv
      have hdrift := hD v hv u hu (S.slotRound k + 1) (by omega) (by omega)
      have := hto (S.slotRound k + 1) (by omega)
      omega
    refine mem_creatorsOf.mpr ⟨b, ?_, hbc⟩
    exact Finset.mem_filter.mpr ⟨hincl b hb (hbc ▸ hu) hbr harrive hvote, hvote⟩

/-- **The reactive direct commit.** Every reliable validator's
round-`(r+2)` block certifies, and `T` is a quorum of certificate
authors — with the certificate blocks supplied by derived production. -/
theorem directCommit (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn rm.built T R D N) (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → D + rm.delay ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) (hL : IsLeaderBlock U k L) :
    DirectCommit U L (S.slotRound k) := by
  have hcerts := rm.certifies hT hcard hD hgst hto hR hN hlead hL
  have hpop := rm.toPaceCore.populatedOn hcard (S.slotRound k + 2) (by omega)
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨c, hc, hcc, hcr⟩ := hpop v hv
  refine mem_creatorsOf.mpr ⟨c, ?_, hcc⟩
  refine Finset.mem_filter.mpr ⟨mem_blocksAt.mpr ⟨hc, hcr⟩, ?_⟩
  exact hcerts v hv c hc hcc hcr

/-- **Reactive liveness (Mysticeti).** A reliable-led slot past GST is
committed by every view — the conclusion of `decided_of_leader_mem`,
with reference coverage replaced by the two reactive wait clauses and
the leader block supplied by derived production. -/
theorem decided (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hD : DriftOn rm.built T R D N) (hgst : rm.gst ≤ R)
    (hto : ∀ n, R ≤ n → D + rm.delay ≤ rm.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLmem, hLc, hLr⟩ :=
    rm.toPaceCore.populatedOn hcard (S.slotRound k) (by omega) (S.leader k) hlead
  have hL : IsLeaderBlock U k L := ⟨hLmem, hLr, hLc⟩
  exact ⟨L, hL, Decided.directCommit hL
    (directCommitIn_full (rm.directCommit hT hcard hD hgst hto hR hN hlead hL))⟩

end ReactiveM

end LeanDag
