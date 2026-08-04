import LeanDag.Timing

/-!
# Quantitative liveness — bounds, from rated assumptions

`liveness.md` §8 Q3 and Q4. Everything in `Liveness.lean` and `Timing.lean`
stands unchanged; this file adds nothing to those and removes nothing from
them.

**Why a separate file.** The results below are *strictly stronger* than their
counterparts underneath, and they buy that strength with *strictly stronger*
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

The `max k R` is not slack: the slot must clear both the caller's starting
point and the synchrony round, and `le_slotRound` is what makes slot `R` sit
past round `R`. -/
theorem commits_recur_within (hT : T ⊆ (Correct : Finset Validator))
    (hcard : 2 * F.f + 1 ≤ T.card) (fair : FairWithin T w) (R k : ℕ) :
    ∃ k', max k R ≤ k' ∧ k' < max k R + w ∧ R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (D : Delivery U) (N : ℕ),
        Live U D N → DeliversQuorum D → SynchronisedOn U T R →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) := by
  have h3 : 3 * R ≤ S.slotRound R := le_slotRound (Validator := Validator) R
  have hkR : R ≤ S.slotRound R := by omega
  obtain ⟨k', hk', hlt, hlead⟩ := fair (max k R)
  have hRk' : R ≤ S.slotRound k' := by
    rcases eq_or_lt_of_le (le_trans (le_max_right k R) hk') with heq | hlow
    · exact heq ▸ hkR
    · exact le_trans hkR
        (by have := slotRound_add_three_le (Validator := Validator) hlow; omega)
  refine ⟨k', hk', hlt, hRk', ?_⟩
  intro U D N H hd hs hN
  exact decided_of_leader_mem hcard hs hRk'
    (PopulatedOn.mono hT (no_stall H hd _ (by omega)))
    (PopulatedOn.mono hT (no_stall H hd _ (by omega)))
    (PopulatedOn.mono hT (no_stall H hd _ (by omega))) hlead

/-! ### From a slot bound to a round bound

`Slots.spacing` bounds slot rounds from **below** (`slotRound k + 3 ≤
slotRound (k+1)`), which is what safety needs — M4's anchor must sit at least
three rounds up. A *latency* claim wants the opposite bound, and nothing in
`Slots` provides it: a schedule may leave arbitrarily large gaps between
consecutive slots and remain perfectly legal.

So the round bound needs its own hypothesis, and it is the mirror image of
`spacing`. -/

/-- Consecutive slots are at most `s` rounds apart — the upper companion to
`Slots.spacing`. Every real schedule has one; the class omits it because no
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

Read the two summands: `slotRound (max k R)` is where the search starts, and
`s * w` is the worst-case cost of walking to the next `T`-leader. The `+ 2` is
the certificate round — L4's `r + 2`, unchanged.

At the standard settings — round-robin over `3f+1` so `w = f + 1`, and slots
every three rounds so `s = 3` — this reads `3 * (f + 1)` rounds past the
starting slot, which is the concrete latency figure `liveness.md` §8 Q4 asks
for. -/
theorem commits_recur_by_round {s : ℕ} (hT : T ⊆ (Correct : Finset Validator))
    (hcard : 2 * F.f + 1 ≤ T.card) (fair : FairWithin T w)
    (hs : BoundedSpacing (Validator := Validator) s) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ S.slotRound k' ≤ S.slotRound (max k R) + s * w ∧
      R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (D : Delivery U) (N : ℕ),
        Live U D N → DeliversQuorum D → SynchronisedOn U T R →
        S.slotRound (max k R) + s * w + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) := by
  obtain ⟨k', hk, hlt, hRk', hcommit⟩ :=
    commits_recur_within (BlockId := BlockId) (Payload := Payload) hT hcard fair R k
  have hround := slotRound_le_of_lt (Validator := Validator) hs hk hlt
  refine ⟨k', le_trans (le_max_left k R) hk, hround, hRk', ?_⟩
  intro U D N H hd hsync hN
  exact hcommit U D N H hd hsync (by omega)

end LeanDag
