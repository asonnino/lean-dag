import LeanDag.FinWhale.Decision
import LeanDag.ViewPace

/-!
# FinWhale — liveness: an honest leader is committed

Lemmas 16 to 21. The paper reaches them through a timing argument: round
synchronisation within `∆` (Lemma 16) and delivery before the round
timeout expires (Lemma 17), out of the pacemaker's conditions and the
`2∆` timeout. Those two lemmas say, in the end, that after GST every
correct validator's block references every correct block of the round
below, and that is a condition on the DAG rather than on the clock.

This file takes that condition from the development's own pacing line
rather than assuming it. A `ViewPace` (report §6.9) carries view
convergence — a validator's holdings reach every other within `delay`
past GST — and the pacemaker's progress and catch-up rules. From those,
`ViewPace.driftOn_of_catchup` derives the drift bound `delay + proc`
with no hypothesis about the starting spread, and
`ViewPace.synchronisedOn_of_converges` wins the race between drift and
the timeout to give reference coverage from any round past GST. Both are
the core's, used read-only; `synchronised_of_viewPace` below is the
bridge to a FinWhale DAG, and the rest of the file is counting.

**Why the bridge is a hypothesis about two structures rather than a
coercion.** `ViewPace` is stated over a `BlockUniverse`, whose validity
rule carries the self-parent clause; `FinWhale.ValidHere` does not, since
no result of the safety arc reads it. The paper's block structure has it
— "every block includes an edge that references the previous block
created by the same validator" — so a FinWhale execution satisfies both
rules, and the bridge asks only that the two structures describe the same
blocks.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-! ## Lemmas 16 and 17, derived -/

/-- **Production, from the pacing line.** Every correct validator authors
a block at every round below the horizon. This is the pacemaker's
progress rule, not a timing argument: `PaceCore.populatedOn` reads a
round a validator reached as a round it built in. -/
theorem populated_of_viewPace {U : BlockUniverse Validator BlockId Payload} {N : ℕ}
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block) :
    ∀ r ≤ N, PopulatedFrom D.block D.ids (Correct : Finset Validator) r := by
  intro r hr
  rw [hids, hblk]
  exact vp.populatedOn card_correct r hr

/-- **Lemmas 16 and 17, in the form the rest of the argument uses.** From
any round past GST, once the timeout clears `2∆ + proc`, every correct
block references every correct block of the round below.

The two ingredients are the core's: view convergence supplies the
drift bound (`ViewPace.driftOn_of_catchup`), and the race against the
timeout supplies coverage (`ViewPace.synchronisedOn_of_converges`).
Neither is assumed here. -/
theorem synchronised_of_viewPace {U : BlockUniverse Validator BlockId Payload} {N R : ℕ}
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) :
    SynchronisedFrom D.block D.ids (Correct : Finset Validator) R := by
  rw [hids, hblk]
  exact vp.synchronisedOn_of_converges card_correct hgst hbackoff

/-! ## Lemma 18 — the honest leader is voted for -/

/-- **Lemma 18.** Past the coverage round, every correct block of round
`r + 1` references the correct leader's block of round `r`, which is to
say votes for it. The paper argues this through the three block-creation
conditions; coverage is what all three establish. -/
theorem lemma18 {R r : ℕ}
    (hsync : SynchronisedFrom D.block D.ids (Correct : Finset Validator) R) (hR : R ≤ r)
    {l b : BlockId} (hl : l ∈ D.ids) (hlr : (D.block l).round = r)
    (hlc : (D.block l).creator ∈ (Correct : Finset Validator))
    (hb : b ∈ D.ids) (hbr : (D.block b).round = r + 1)
    (hbc : (D.block b).creator ∈ (Correct : Finset Validator)) :
    l ∈ (D.block b).refs :=
  hsync r hR b hb hbr hbc l hl hlr hlc

/-- Every correct validator is a voter for a correct leader's block: it
has a round-`(r+1)` block, and that block references the leader's. -/
theorem correct_subset_voters {R r : ℕ}
    (hsync : SynchronisedFrom D.block D.ids (Correct : Finset Validator) R) (hR : R ≤ r)
    (hpop : PopulatedFrom D.block D.ids (Correct : Finset Validator) (r + 1))
    {l : BlockId} (hl : l ∈ D.ids) (hlr : (D.block l).round = r)
    (hlc : (D.block l).creator ∈ (Correct : Finset Validator)) :
    (Correct : Finset Validator) ⊆ voters D l := by
  intro v hv
  obtain ⟨b, hb, hbc, hbr⟩ := hpop v hv
  refine mem_creatorsOf.2 ⟨b, ?_, hbc⟩
  simp only [blocksAt, Finset.mem_filter]
  exact ⟨⟨hb, by rw [hbr, hlr]⟩,
    lemma18 hsync hR hl hlr hlc hb hbr (by rw [hbc]; exact hv)⟩

/-! ## Lemma 19 — every correct block two rounds up certifies -/

/-- **Lemma 19.** A correct round-`(r+2)` block references a quorum of
blocks voting for the correct leader of round `r`, which is exactly an
SP-certificate.

Coverage supplies the parents — every correct round-`(r+1)` block is one
— and Lemma 18 supplies their votes. The paper's parent-selection
argument is what coverage replaces: a correct leader does not equivocate,
so no correct parent is dropped by the leader clause. -/
theorem lemma19 {R r : ℕ}
    (hsync : SynchronisedFrom D.block D.ids (Correct : Finset Validator) R) (hR : R ≤ r)
    (hpop1 : PopulatedFrom D.block D.ids (Correct : Finset Validator) (r + 1))
    {l : BlockId} (hl : l ∈ D.ids) (hlr : (D.block l).round = r)
    (hlc : (D.block l).creator ∈ (Correct : Finset Validator))
    {b : BlockId} (hb : b ∈ D.ids) (hbr : (D.block b).round = r + 2)
    (hbc : (D.block b).creator ∈ (Correct : Finset Validator)) :
    SPCertificate D b l := by
  have hsub : (Correct : Finset Validator) ⊆ parentsVoting D b l := by
    intro v hv
    obtain ⟨q, hq, hqc, hqr⟩ := hpop1 v hv
    refine mem_creatorsOf.2 ⟨q, ?_, hqc⟩
    simp only [Finset.mem_filter]
    exact ⟨hsync (r + 1) (by omega) b hb (by rw [hbr]) hbc q hq hqr
        (by rw [hqc]; exact hv),
      lemma18 hsync hR hl hlr hlc hq hqr (by rw [hqc]; exact hv)⟩
  exact le_trans (le_trans spQuorum_le_quorumCard card_correct) (Finset.card_le_card hsub)

/-! ## Lemma 20 and Theorem 21 — the commit -/

/-- **Lemma 20.** A correct leader's block is committed by the slow path,
at every `p` in range: the correct validators number `n − f ≥ 2f + p`,
each has a round-`(r+2)` block, and each of those is an SP-certificate. -/
theorem lemma20 {R r : ℕ}
    (hsync : SynchronisedFrom D.block D.ids (Correct : Finset Validator) R) (hR : R ≤ r)
    (hpop1 : PopulatedFrom D.block D.ids (Correct : Finset Validator) (r + 1))
    (hpop2 : PopulatedFrom D.block D.ids (Correct : Finset Validator) (r + 2))
    {l : BlockId} (hl : l ∈ D.ids) (hlr : (D.block l).round = r)
    (hlc : (D.block l).creator ∈ (Correct : Finset Validator)) :
    SPCommit D l := by
  refine ⟨(Correct : Finset Validator),
    le_trans spQuorum_le_quorumCard card_correct, fun v hv => ?_⟩
  obtain ⟨b, hb, hbc, hbr⟩ := hpop2 v hv
  refine ⟨b, ?_, hbc, lemma19 hsync hR hpop1 hl hlr hlc hb hbr (by rw [hbc]; exact hv)⟩
  simp only [blocksAt, Finset.mem_filter]
  exact ⟨hb, by rw [hbr, hlr]⟩

/-- **Theorem 21 (Fast Termination).** Where at most `p` validators are
actually Byzantine, the correct validators number `n − p`, and their
votes alone are a fast commit — two rounds after the leader's block. -/
theorem theorem21 {R r : ℕ}
    (hsync : SynchronisedFrom D.block D.ids (Correct : Finset Validator) R) (hR : R ≤ r)
    (hpop1 : PopulatedFrom D.block D.ids (Correct : Finset Validator) (r + 1))
    (hfew : F.byzantine.card ≤ P.p)
    {l : BlockId} (hl : l ∈ D.ids) (hlr : (D.block l).round = r)
    (hlc : (D.block l).creator ∈ (Correct : Finset Validator)) :
    FastCommit D l := by
  have hcard : fastCard Validator ≤ (Correct : Finset Validator).card := by
    have := card_correct_add_byzantine (Validator := Validator)
    simp only [fastCard]; omega
  exact le_trans hcard
    (Finset.card_le_card (correct_subset_voters hsync hR hpop1 hl hlr hlc))

/-- **The direct commit, from the pacing line alone.** Nothing here is a
timing hypothesis: `vp` carries view convergence and the pacemaker's
rules, `hgst` places the round past GST, and `hbackoff` is the timeout
discipline the core's race consumes. -/
theorem directCommit_of_viewPace {U : BlockUniverse Validator BlockId Payload} {N R r : ℕ}
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hR : R ≤ r) (hrN : r + 2 ≤ N)
    {l : BlockId} (hl : l ∈ D.ids) (hlr : (D.block l).round = r)
    (hlc : (D.block l).creator ∈ (Correct : Finset Validator)) :
    DirectCommit D l :=
  Or.inr (lemma20 (synchronised_of_viewPace vp hids hblk hgst hbackoff) hR
    (populated_of_viewPace vp hids hblk (r + 1) (by omega))
    (populated_of_viewPace vp hids hblk (r + 2) (by omega)) hl hlr hlc)

end FinWhale

end LeanDag
