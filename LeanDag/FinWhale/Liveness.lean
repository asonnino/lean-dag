import LeanDag.FinWhale.Decision
import LeanDag.ViewPace

/-!
# FinWhale — the bridge to the development's pacing line

A `ViewPace` (report §6.9) carries view convergence and the pacemaker's
progress and catch-up rules, and from them the core derives production
and reference coverage: `ViewPace.populatedOn` and
`ViewPace.synchronisedOn_of_converges`, the latter through the drift
bound `ViewPace.driftOn_of_catchup`. This file carries both to a FinWhale
DAG.

**What this is not.** It is not the route FinWhale's liveness runs on.
Coverage is obtained from `ViewPace.waits`, a waiting *floor* — a validator
never builds before the timeout expires — and FinWhale's pacemaker builds
on C1 or C3 long before that. Its liveness is established in
`Creation.lean`, from the block-creation conditions themselves, and the
argument the floor would have supplied appears there as the C2 case.

What the bridge is for is compatibility, in the sense
`LeanDagTest/Routes.lean` gives the word: a FinWhale DAG can be fed from
the development's main line, and the two conditions the feature arcs
consume are available over it.

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

/-- **Coverage, from the pacing line.** From any round past GST, once the
timeout clears `2∆ + proc`, every correct block references every correct
block of the round below. View convergence supplies the drift bound and
the race against the timeout supplies coverage; neither is assumed here.

A reactive builder has no such property, which is why FinWhale's liveness
does not run on it. -/
theorem synchronised_of_viewPace {U : BlockUniverse Validator BlockId Payload} {N R : ℕ}
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n) :
    SynchronisedFrom D.block D.ids (Correct : Finset Validator) R := by
  rw [hids, hblk]
  exact vp.synchronisedOn_of_converges card_correct hgst hbackoff

end FinWhale

end LeanDag
