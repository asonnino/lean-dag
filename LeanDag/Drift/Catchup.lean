import LeanDag.ViewSync

/-!
# Catch-up: eliminating the start spread from the wait threshold

The wait threshold of the quantitative results is `D₀ + Δ`, where `D₀`
bounds the spread between validators' round-`0` entries. `D₀` is the one
quantity in the development set by *deployment* rather than by the
network or the specification (report §4.5), and it enters the threshold
permanently, because under `waits` and `prompt` drift is **preserved,
not contracted** — every clock advances by the same timeout, and
`ugrowSkew` keeps its spread for ever
(`ugrowSkew_spread_constant`). The intuition that the spread shrinks as
the protocol reaches synchrony is therefore false of the protocol as
modelled; a mechanism must supply it.

`catchup` is that mechanism, and it is the rule real pacemakers run: a
validator that *sees evidence of a round* — any block of it — enters
that round within a processing bound, rather than sitting out its own
timeout. One clause, and drift contracts without reference to its
starting value:

* `drift_collapse` — at any round whose builds all lie past GST, the
  spread is at most `Δ + proc`, **whatever it was before**. The laggard
  cannot stay behind: the earliest builder's block reaches it within
  `Δ`, and catch-up converts the sighting into entry within `proc`.
* `decided_of_catchup` — the commit threshold becomes `2Δ + proc`, a
  constant of the network and the implementation. `D₀` does not appear;
  the deployment residue of report §4.5 is discharged.

`CatchupSync` extends `ViewSync`, so every result of the timed
development applies to it unchanged. The two regimes coexist without
tension: `catchup` binds a validator only when evidence has actually
reached it, so before GST — when the network may deliver nothing — an
arbitrary spread is admitted, and the clause never conflicts with
`waits`, which the collapse then makes easy to honour.

What catch-up does *not* buy is coverage. A validator that enters a
round by evidence has not waited for the round below to assemble, so
its own block may reference little; the coverage argument still runs
through `waits`, from the collapsed spread onward. Catch-up repairs the
*base* of the drift argument, not the argument.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {D N R : ℕ}

/-- `ViewSync` with the catch-up rule: a validator that holds any block
of a round has built its own block of that round within `proc` of the
sighting. -/
structure CatchupSync (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends ViewSync U T N where
  /-- The processing bound: how long entry may lag evidence. -/
  proc : ℕ
  /-- **Catch-up** (protocol). Seeing a round is entering it: any
  `T`-block of round `n` in hand at time `t` means the holder's own
  round-`n` block was built by `t + proc`. -/
  catchup : ∀ v ∈ T, ∀ u ∈ T, ∀ n ≤ N, ∀ t,
    blk u n ∈ holds v t → built v n ≤ t + proc

namespace CatchupSync

variable (cs : CatchupSync U T N)

omit [DecidableEq BlockId] in
/-- **Drift collapses, from any starting value.** At a round whose
builds all lie past GST, the spread among `T` is at most `Δ + proc`:
the earliest builder holds its own block at once, convergence carries it
to every peer within `Δ`, and catch-up converts the sighting into entry
within `proc`. No hypothesis mentions the previous spread. -/
theorem drift_collapse {n : ℕ} (hn : n ≤ N)
    (hg : ∀ u ∈ T, cs.gst ≤ cs.built u n) :
    ∀ v ∈ T, ∀ w ∈ T, cs.built v n ≤ cs.built w n + (cs.delay + cs.proc) := by
  intro v hv w hw
  have hown := cs.holds_own w hw n hn
  have hconv := cs.converges v hv w hw _ (hg w hw) hown
  have := cs.catchup v hv w hw n hn _ hconv
  omega

/-- The collapsed spread, in the form the timed development consumes:
from any `R` past GST, drift is bounded by `Δ + proc` — with no base
hypothesis, where `driftFrom_of_prompt` required the spread supplied at
its starting round. -/
theorem driftOn_of_catchup (hgst : cs.gst ≤ R) :
    DriftOn cs.built T R (cs.delay + cs.proc) N := by
  intro v hv w hw n hRn hnN
  refine cs.drift_collapse hnN (fun u hu => ?_) w hw v hv
  exact le_trans (le_trans hgst hRn) (Timing.le_built (tm := cs.toTiming) hu n hnN)

/-- **Coverage at a deployment-free threshold.** Reference coverage from
`R` on, once the timeout clears `2Δ + proc` — a constant of the network
and the implementation. The start spread `D₀` of the quantitative
results does not appear. -/
theorem synchronisedOn_of_catchup (hT : T ⊆ (Correct : Finset Validator))
    (hgst : cs.gst ≤ R)
    (hto : ∀ n, R ≤ n → (cs.delay + cs.proc) + cs.delay ≤ cs.timeout n) :
    SynchronisedOn U T R :=
  cs.synchronisedOn_of_converges hT (cs.driftOn_of_catchup hgst) hgst hto

/-- **The commit, with `D₀` eliminated.** A reliable-led slot past GST
is committed by every view once the timeout clears `2Δ + proc`. Where
`decided_of_wait` requires the round-`0` spread as a hypothesis — the
one deployment quantity in the development — this requires nothing about
how the validators started. -/
theorem decided_of_catchup [S : Slots Validator] {k : ℕ}
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hgst : cs.gst ≤ R)
    (hto : ∀ n, R ≤ n → (cs.delay + cs.proc) + cs.delay ≤ cs.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_leader_mem hcard (cs.synchronisedOn_of_catchup hT hgst hto) hR
    (cs.toTiming.populatedOn (by omega))
    (cs.toTiming.populatedOn (by omega))
    (cs.toTiming.populatedOn (by omega)) hlead

end CatchupSync

end LeanDag
