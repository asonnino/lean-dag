import LeanDag.ViewPace

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

`CatchupPace` extends `ViewPace`, so every result of the timed
development applies to it unchanged. The two regimes coexist without
tension: `catchup` binds a validator only when evidence has actually
reached it, so before GST — when the network may deliver nothing — an
arbitrary spread is admitted, and the clause never conflicts with
`waits`, which the collapse then makes easy to honour.

What catch-up does *not* supply is coverage. A validator that enters a
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

/-! ## The rule, over the partial schedule

The clause is stated off `blk`, over any `T`-authored block, and says
one thing more than a total schedule could: seeing a round means
**reaching** it (`n ≤ top v`), which is exactly what a real pacemaker's
catch-up does. The conclusion `built v n ≤ t + proc` then reads off a
round the validator did reach. -/
structure CatchupPace (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) extends ViewPace U T N where
  /-- The processing bound: how long entry may lag evidence. -/
  proc : ℕ
  /-- **Catch-up** (protocol). Seeing a round is entering it: any
  `T`-authored block of round `n` in hand at time `t` means the holder
  reached round `n` and built its own block there by `t + proc`. -/
  catchup : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator ∈ T → (U.block b).round = n →
    ∀ t, b ∈ holds v t → n ≤ top v ∧ built v n ≤ t + proc

namespace CatchupPace

variable (cp : CatchupPace U T N)

omit [DecidableEq BlockId] in
/-- **Drift collapses, from any starting value** — `drift_collapse` over
the partial schedule. `htop` guards the rounds the statement reads;
`driftOn_of_catchup` discharges it from the quorum bound. -/
theorem drift_collapse {n : ℕ} (hn : n ≤ N)
    (htop : ∀ u ∈ T, n ≤ cp.top u)
    (hg : ∀ u ∈ T, cp.gst ≤ cp.built u n) :
    ∀ v ∈ T, ∀ w ∈ T, cp.built v n ≤ cp.built w n + (cp.delay + cp.proc) := by
  intro v hv w hw
  obtain ⟨b, hb, hbc, hbr⟩ := cp.built_of_le_top w hw n (htop w hw)
  have hown := cp.holds_own w hw n hn b hb hbc hbr
  have hconv := cp.converges v hv w hw _ (hg w hw) hown
  have := (cp.catchup v hv n hn b hb (hbc ▸ hw) hbr _ hconv).2
  omega

omit [DecidableEq BlockId] in
/-- The collapsed spread, in the form the development consumes — with no
base hypothesis, where `driftOn_of_prompt` requires the spread supplied
at its starting round. -/
theorem driftOn_of_catchup
    (hcard : (Fintype.card Validator - F.f) ≤ T.card) (hgst : cp.gst ≤ R) :
    DriftOn cp.built T R (cp.delay + cp.proc) N := by
  intro v hv w hw n hRn hnN
  have htop := fun u hu => cp.reached hcard n hnN u hu
  refine cp.drift_collapse hnN htop (fun u hu => ?_) w hw v hv
  exact le_trans (le_trans hgst hRn) (cp.le_built hu n (htop u hu))

omit [DecidableEq BlockId] in
/-- **Coverage at a deployment-free threshold**, from `R` on, once the
timeout clears `2Δ + proc`. The start spread `D₀` does not appear, and —
as everywhere on this route — neither does `T ⊆ Correct`. -/
theorem synchronisedOn_of_catchup
    (hcard : (Fintype.card Validator - F.f) ≤ T.card) (hgst : cp.gst ≤ R)
    (hto : ∀ n, R ≤ n → (cp.delay + cp.proc) + cp.delay ≤ cp.timeout n) :
    SynchronisedOn U T R :=
  cp.synchronisedOn_of_converges (cp.driftOn_of_catchup hcard hgst) hgst hto

/-- **The commit, with `D₀` eliminated**, production derived rather than
read off `blk`: a reliable-led slot past GST is committed once the
timeout clears `2Δ + proc`, from genesis, convergence, the progress rule
and catch-up. -/
theorem decided_of_catchup [S : Slots Validator] {k : ℕ}
    (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hgst : cp.gst ≤ R)
    (hto : ∀ n, R ≤ n → (cp.delay + cp.proc) + cp.delay ≤ cp.timeout n)
    (hR : R ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_leader_mem hcard (cp.synchronisedOn_of_catchup hcard hgst hto) hR
    (cp.populatedOn hcard _ (by omega))
    (cp.populatedOn hcard _ (by omega))
    (cp.populatedOn hcard _ (by omega)) hlead

end CatchupPace

end LeanDag
