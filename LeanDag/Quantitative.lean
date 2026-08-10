import LeanDag.Timing

/-!
# Quantitative liveness — bounds, from rated assumptions

`liveness.md` §8 Q3 and Q4. Everything in `Liveness.lean` and `Timing.lean`
stands unchanged; this file adds nothing to those and removes nothing from
them.

**Why a separate file.** The results below are *strictly stronger* than their
counterparts underneath, and they obtain that strength from *strictly stronger*
hypotheses. Keeping them apart makes the trade legible: a reader sees exactly
which assumption purchases which bound, and the weak-hypothesis theorems stay
available to anyone unwilling to pay.

**What was missing, and why.** Two results below conclude with a bare
existential:

- `exists_synchronisedOn_of_backoff` gives `∃ R, SynchronisedOn U T R`;
- `commits_recur_on` gives `∃ k', k ≤ k' ∧ …`.

Neither says *where*. That is not slack in the proofs — it is forced, because
each hypothesis is itself a bare existential:

- `hub : ∀ m, ∃ n, m ≤ tm.timeout n` — the backoff clears any threshold
  *eventually*, at no stated rate;
- `FairScheduleOn T : ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T` — a `T`-leader
  recurs, with no gap bound.

Under those, **no bound exists at all**. Take `timeout n = ⌊log₂ (n+1)⌋`:
monotone, unbounded, admissible — and it needs `n ≥ 2 ^ (D + delay) - 1` to
clear the threshold, with slower schedules pushing `R` out without limit.
Likewise a schedule naming `T`-leaders at slots `0, 10, 1000, …` is fair with
unbounded gaps. So the fix is not a better proof but a **rated** hypothesis,
and that is all this file supplies:

| Weak | Rated | Buys |
|---|---|---|
| `hub` | `Rated tm.timeout` | an explicit `R` |
| `FairScheduleOn T` | `FairWithin T w` | a slot bound |
| *(none)* | `BoundedSpacing s` | a round bound, and an explicit horizon |

**A hypothesis is dropped, not just added.** `backoff_ge_of_rate` needs no
monotonicity, where `exists_backoff_ge` needs it to propagate a single clearing
round upward. `Rated` implies `hub` (`unbounded_of_rated`), so the rated route
is a strengthening of one assumption and a deletion of another.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {D N : ℕ}

/-! ## Part 1 — a rated backoff pins `R`

`liveness.md` §8 Q3. The threshold `synchronisedOn_of_timing` consumes is
`D + delay ≤ timeout n` for every `n ≥ R`. With a rate the least such `R` is
read off directly, instead of being extracted from an existential that does not
say where it lives. -/

/-- A backoff that grows **at least as fast as the round index**.

Weaker than it may look, and deliberately so: it fixes no shape, and any
schedule dominating the identity qualifies — linear, exponential, or a step
function that jumps early and then plateaus high. What it rules out is exactly
what `hub` permits: growth so slow that clearing a fixed threshold takes
unboundedly many rounds. -/
def Rated (timeout : ℕ → ℕ) : Prop := ∀ n, n ≤ timeout n

/-- **A rated backoff clears any threshold by the threshold itself.**

Contrast `exists_backoff_ge`, which needs `Monotone` to turn one clearing round
into all later ones. Monotonicity is not used here: the bound at `n` comes from
`n` itself, so it cannot lapse afterwards. -/
theorem backoff_ge_of_rate {timeout : ℕ → ℕ} (hrate : Rated timeout) (m : ℕ) :
    ∀ n, m ≤ n → m ≤ timeout n :=
  fun n hn => le_trans hn (hrate n)

/-- Every rated backoff is unbounded, so `Rated` really is a strengthening of
`exists_backoff_ge`'s hypothesis rather than a sideways move. -/
theorem unbounded_of_rated {timeout : ℕ → ℕ} (hrate : Rated timeout) :
    ∀ m, ∃ n, m ≤ timeout n :=
  fun m => ⟨m, hrate m⟩

omit [DecidableEq BlockId] in
/-- **Q3, the synchrony half.** With a rated backoff, coverage holds from an
**explicit** round:

`R = max (max (D + delay) n₀) gst`

and each summand is what it looks like — the threshold the timeout must clear,
the round the drift bound is measured from, and GST. Compare
`exists_synchronisedOn_of_backoff`, which concludes `∃ R` and can say no more.

Nothing else changes: the drift argument and the coverage argument are reused
verbatim, and `Monotone` is gone.

The hypothesis `tm.delay ≤ n₀` is what lets `driftFrom_of_prompt` fire from
`n₀` — it asks that the drift base be measured at a round by which the rate has
already carried the timeout past `delay`. Taking `n₀ := tm.delay` always
satisfies it. -/
theorem synchronisedOn_of_rate (tm : Timing U T N) (hT : T ⊆ (Correct : Finset Validator))
    (hrate : Rated tm.timeout) {n₀ : ℕ} (hn₀ : tm.delay ≤ n₀)
    (hbase : ∀ v ∈ T, ∀ w ∈ T, tm.built w n₀ ≤ tm.built v n₀ + D) :
    SynchronisedOn U T (max (max (D + tm.delay) n₀) tm.gst) := by
  refine Timing.synchronisedOn_of_timing hT
    (Timing.DriftFrom.mono (le_trans (le_max_right (D + tm.delay) n₀) (le_max_left _ _))
      (Timing.driftFrom_of_prompt hbase
        (fun n hn => backoff_ge_of_rate hrate _ n (le_trans hn₀ hn))))
    (le_max_right _ _) ?_
  exact fun n hn =>
    backoff_ge_of_rate hrate _ n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)

/-! ## Part 2 — a rated schedule pins the committing slot

`liveness.md` §8 Q4. `FairScheduleOn` promises a `T`-leader arbitrarily far
out; `FairWithin` promises one inside a fixed window. Round-robin over `3f+1`
validators supplies the latter with window `f + 1`, since the validators
outside `T` may be consecutive in the rotation but there are at most `f` of
them. -/

variable [S : Slots Validator]

/-- The schedule names a `T`-leader **within every window of `w` slots**.

The rated form of `FairScheduleOn`. Note `w` is a property of the schedule
alone — no DAG, no network — which is what keeps L6's quantifier order intact:
the slot is still fixed before any universe is mentioned. -/
def FairWithin (T : Finset Validator) (w : ℕ) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ k' < k + w ∧ S.leader k' ∈ T

omit [Fintype Validator] [DecidableEq Validator] F in
/-- A rated schedule is a fair one, so everything already proved from
`FairScheduleOn` applies to it unchanged. -/
theorem FairWithin.fairScheduleOn {w : ℕ} (h : FairWithin T w) : FairScheduleOn T :=
  fun k => let ⟨k', hk', _, hlead⟩ := h k; ⟨k', hk', hlead⟩

variable {w : ℕ}

/-- **Q4, the schedule half.** L6 with the committing slot **bounded**.

L6 says a committing slot exists beyond any `k`; this says it lies within `w`
slots of `max k R`. Everything else is unchanged — the quantifier order, the
`∀ U D N` inside the existential, the horizon condition — and the DAG-facing
content is `commits_recur_on`'s, reproduced here only because the slot has to
be named by `FairWithin` rather than `FairScheduleOn`.

The starting point is not slack: the slot must clear both the caller's `k` and
the synchrony round `R`. The old statement wrote that as `max k R`, relying on
`3 * k ≤ slotRound k` to make slot `R` sit past round `R`. A monotone schedule
gives no such coincidence — under `m` leaders per round slot `R` is around
round `R / m` — so the slot past round `R` is named explicitly by
`slotAt Validator R`. Under the old schedule `slotAt R ≤ R`, so the bound is
no weaker than it was. -/
theorem commits_recur_within (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card) (fair : FairWithin T w) (R k : ℕ) :
    ∃ k', max k (slotAt Validator R) ≤ k' ∧ k' < max k (slotAt Validator R) + w ∧
      R ≤ S.slotRound k' ∧
      CommitsAt BlockId Payload T R k' := by
  obtain ⟨k', hk', hlt, hlead⟩ := fair (max k (slotAt Validator R))
  have hRk' : R ≤ S.slotRound k' :=
    le_trans (le_slotRound_slotAt (Validator := Validator) R)
      (S.mono (le_trans (le_max_right _ _) hk'))
  refine ⟨k', hk', hlt, hRk', ?_⟩
  intro U N hpop hs hN
  exact decided_of_leader_of_populated hT hcard hs hRk' hpop (by omega) hlead

/-! ### From a slot bound to a round bound

A spacing field on `Slots` would bound slot rounds from **below** (`slotRound k + 3 ≤
slotRound (k+1)`), which is what safety needs — M4's anchor must sit at least
three rounds up. A *latency* claim wants the opposite bound, and nothing in
`Slots` provides it: a schedule may leave arbitrarily large gaps between
consecutive slots and remain perfectly legal.

So the round bound needs its own hypothesis, and it is the mirror image of
`spacing`. -/

/-- Consecutive slots are at most `s` rounds apart — the upper companion to
such a field. Every real schedule has one; the class omits it because no
safety result ever asks. -/
def BoundedSpacing (s : ℕ) : Prop := ∀ k, S.slotRound (k + 1) ≤ S.slotRound k + s

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Bounded spacing accumulates: `d` slots on costs at most `s * d` rounds. -/
theorem slotRound_le_of_boundedSpacing {s : ℕ}
    (hs : BoundedSpacing (Validator := Validator) s) (k d : ℕ) :
    S.slotRound (k + d) ≤ S.slotRound k + s * d := by
  induction d with
  | zero => simp
  | succ d ih =>
      have hstep := hs (k + d)
      have hmul : s * (d + 1) = s * d + s := Nat.mul_succ s d
      calc S.slotRound (k + (d + 1)) = S.slotRound (k + d + 1) := rfl
        _ ≤ S.slotRound (k + d) + s := hstep
        _ ≤ S.slotRound k + s * d + s := by omega
        _ = S.slotRound k + s * (d + 1) := by omega

omit [Fintype Validator] [DecidableEq Validator] F in
/-- A slot bound becomes a round bound. -/
theorem slotRound_le_of_lt {s : ℕ} (hs : BoundedSpacing (Validator := Validator) s)
    {k₀ m k' : ℕ} (hk' : k₀ ≤ k') (hlt : k' < k₀ + m) :
    S.slotRound k' ≤ S.slotRound k₀ + s * m := by
  obtain ⟨d, rfl⟩ : ∃ d, k' = k₀ + d := ⟨k' - k₀, by omega⟩
  have hd : d ≤ m := by omega
  have h1 := slotRound_le_of_boundedSpacing (Validator := Validator) hs k₀ d
  have h2 : s * d ≤ s * m := Nat.mul_le_mul_left s hd
  omega

/-- **Q4 in rounds.** The committing slot's round is bounded, so the horizon a
DAG must reach before it is guaranteed to commit becomes an explicit number
rather than "far enough".

Read the two summands: `slotRound (max k (slotAt R))` is where the search
starts, and `s * w` is the worst-case cost of walking to the next `T`-leader.
The `+ 2` is the certificate round — L4's `r + 2`, unchanged.

At the standard settings — round-robin over `3f+1` so `w = f + 1`, and slots
every three rounds so `s = 3` — this reads `3 * (f + 1)` rounds past the
starting slot, which is the concrete latency figure `liveness.md` §8 Q4 asks
for.

**This bound is blind to multiple leaders.** `BoundedSpacing s` says
consecutive slots are at most `s` rounds apart, and with `m` leaders sharing a
round that is still `s = 1`, not `0` — only one step in `m` advances the
round, which `BoundedSpacing` cannot see. So `s * w` reads `w` rounds for `w`
slots however large `m` is. A bound that improves with `m` needs the schedule
to expose it, which `Slots.uniform` does; this statement is kept because it is
the only one that says anything about an irregular schedule. -/
theorem commits_recur_by_round {s : ℕ} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card) (fair : FairWithin T w)
    (hs : BoundedSpacing (Validator := Validator) s) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ S.slotRound k' ≤ S.slotRound (max k (slotAt Validator R)) + s * w ∧
      R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
        (∀ r ≤ N, Populated U r) → SynchronisedOn U T R →
        S.slotRound (max k (slotAt Validator R)) + s * w + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) := by
  obtain ⟨k', hk, hlt, hRk', hcommit⟩ :=
    commits_recur_within (BlockId := BlockId) (Payload := Payload) hT hcard fair R k
  have hround := slotRound_le_of_lt (Validator := Validator) hs hk hlt
  refine ⟨k', le_trans (le_max_left k _) hk, hround, hRk', ?_⟩
  intro U N hpop hsync hN
  exact hcommit U N hpop hsync (by omega)

/-! ## Part 3 — the wait bound: how long is long enough?

The question Parts 1 and 2 do not answer. They bound *when* coverage starts
and *which slot* commits, both given a backoff that eventually clears
`D + delay`. Neither says what a validator should actually set its timer to.

**The backoff exists only because Δ is unknown.** If a validator knows the
delivery bound and the spread it started with, it does not need a backoff, a
`Rated` hypothesis, `Monotone`, or an existential `R` — it needs a **constant**
timeout of `D₀ + Δ`, and correct leaders commit from GST onward. That is the
content of this part, and it is why the results below assume neither `Rated`
nor anything from Part 1.

**Where `D₀` comes from, and why Obstacle 1 is not in the way.** The drift
bound need not be *derived* from Δ by a compression argument — `Timing` cannot
supply one, since `waits` forbids a lagging validator from catching up faster
than its own timeout, and that is deliberate (an adversary answering instantly
would otherwise fill an early quorum). Instead the bound is taken at **round
`0`**, where it is a statement about how far apart validators *started*, and
`driftFrom_of_prompt` carries it forward unchanged forever. A system whose
validators start together has `D₀ = 0`; one started by a common broadcast has
`D₀ ≤ Δ`, giving the headline `2Δ`. -/

omit [DecidableEq BlockId] S in
/-- `Timing` already asserts a block per `T`-validator per round below the
horizon, so it populates rounds directly — no `Live`, no `DeliversQuorum`, no
L1. This is what lets Part 3's statements mention only timing. -/
theorem Timing.populatedOn (tm : Timing U T N) {n : ℕ} (hn : n ≤ N) :
    PopulatedOn U T n :=
  fun v hv => ⟨tm.blk v n, tm.blk_mem v hv n hn, tm.blk_creator v hv n hn,
    tm.blk_round v hv n hn⟩

variable {D₀ k : ℕ}

/-- **The wait bound.** After GST, a correct leader is committed provided every
`T`-validator waits at least `D₀ + Δ` before building, where `D₀` bounds the
spread at round `0`.

So `Delay(Δ) = D₀ + Δ`, and it is a **constant** — no backoff, no growth
condition, no `∃ R`. The only hypotheses about time are the start spread, the
wait, and that the slot sits past GST.

The chain is three steps, all already proved:
`driftFrom_of_prompt` turns the round-`0` spread into `DriftFrom 0 D₀`;
`synchronisedOn_of_timing` turns that plus the wait into coverage from the
slot's round; and L4 turns coverage plus three populated rounds into a direct
commit. The populated rounds come from `Timing` itself.

`hN` is the horizon condition, and it is L4's `r + 2` — the certificate round.
Nothing here is asymptotic: the DAG must actually reach two rounds past the
leader. -/
theorem directCommit_of_wait (tm : Timing U T N) (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hstart : ∀ v ∈ T, ∀ w ∈ T, tm.built w 0 ≤ tm.built v 0 + D₀)
    (hwait : ∀ n, D₀ + tm.delay ≤ tm.timeout n)
    (hgst : tm.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) := by
  have hsync : SynchronisedOn U T (S.slotRound k) :=
    Timing.synchronisedOn_of_timing hT
      (Timing.DriftFrom.mono (Nat.zero_le _)
        (Timing.driftFrom_of_prompt hstart
          (fun n _ => le_trans (Nat.le_add_left _ _) (hwait n))))
      hgst (fun n _ => hwait n)
  exact directCommit_of_leader_mem hcard hsync (le_refl _)
    (tm.populatedOn (by omega)) (tm.populatedOn (by omega)) (tm.populatedOn (by omega)) hlead

/-- **The wait bound, as a decision.** What the ledger is defined over. -/
theorem decided_of_wait (tm : Timing U T N) (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hstart : ∀ v ∈ T, ∀ w ∈ T, tm.built w 0 ≤ tm.built v 0 + D₀)
    (hwait : ∀ n, D₀ + tm.delay ≤ tm.timeout n)
    (hgst : tm.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLb, hdc⟩ := directCommit_of_wait tm hT hcard hstart hwait hgst hN hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_full hdc)⟩

/-- **`Delay(Δ) = 2Δ`.** The headline case: validators that started within one
delivery bound of each other, waiting two, commit every correct leader after
GST.

`D₀ ≤ Δ` is what a common start signal gives — the signal itself takes at most
Δ to reach everyone. `D₀ = 0` (a synchronised start) would give `Delay(Δ) = Δ`;
the factor of two is the price of not having synchronised clocks. -/
theorem directCommit_of_wait_two_delay (tm : Timing U T N)
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hstart : ∀ v ∈ T, ∀ w ∈ T, tm.built w 0 ≤ tm.built v 0 + tm.delay)
    (hwait : ∀ n, 2 * tm.delay ≤ tm.timeout n)
    (hgst : tm.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) :=
  directCommit_of_wait tm hT hcard hstart (fun n => by have := hwait n; omega) hgst hN hlead

end LeanDag
