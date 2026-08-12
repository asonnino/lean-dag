import LeanDag.ViewSync

/-!
# A build schedule that can be stuck

`ViewGrowth` derives production from the build rule, but pays for it with
`hcross`: no `T`-validator completes the round straddling GST within
`delay` of it. That hypothesis is not about the network and not about the
DAG — it is about the *schedule*, and it is there for one reason.

`Timing.built`, `ViewSync.built` and `ViewGrowth.built` are **total**
functions. Each assigns a build time to every round, whether or not the
validator could build there. A real validator lacking a quorum does not
complete the round; it waits, and its build time lands after the quorum
arrives. The total schedule cannot say that. It admits, alongside the real
executions, schedules in which a validator "builds" round `n+1` at a time
when no quorum is in hand — and there the round is permanently empty, so
at `T.card = n - f` everything above it is empty too. `hcross` is the
clause that excludes those non-executions.

Adding P8's converse to a total schedule does not help, and the reason is
the same: since `built v (n+1)` is a number that exists, *"the build waits
for the quorum"* forces the quorum to be in hand at that time, which is
production asserted rather than derived.

So the repair is to make the schedule partial, which is what this file
does. `top v` is the highest round `v` reached; `built v n` is read only
at `n ≤ top v`, and rounds above `top v` were never built. **Stuck** is
then expressible — it is `top v = n` — and the deadline disappears with
it: a validator advances *whenever* the quorum arrives, not at a time
fixed in advance. That is exactly what `hcross` was compensating for, and
`ViewPace.populatedOn` needs no counterpart to it.

What the partial schedule needs instead is the pacemaker's own rule, that
a validator which *can* advance *does*:

```
advances : v holds a quorum of round-n authors at some time  ⟹  n < top v
```

It is conditional on holding a quorum, so it asserts no production; it is
P8's forward direction restated as advancement rather than as a block at a
predetermined time. Nothing else about timing enters the derivation —
production here uses neither drift, nor the backoff, nor `timeout`, since
with no deadline there is nothing to beat.

```
genesis + converges + advances  ──▶  PopulatedOn, at every round
converges + P7 + P9 + drift     ──▶  SynchronisedOn, from the crossing
```
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {T : Finset Validator} {N : ℕ}

/-- View convergence over a **partial** build schedule.

`top v` is the highest round `v` reached. Its two clauses say that `v`'s
blocks are exactly the rounds `0` through `top v`: `built_of_le_top`
supplies one at each of them, and `le_top_of_built` says there are none
above. Neither is an assumption about the network — the first at `n = 0`
is `Live.genesis`, which a validator satisfies alone, and the rest of it
is the definition of how far the validator got.

Everything else is `ViewGrowth`'s, with the schedule clauses guarded by
`n < top v`, since a round the validator never reached has no build time
worth constraining. -/
structure ViewPace (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (N : ℕ) where
  /-- The highest round `v` reached. Rounds above it were never built. -/
  top : Validator → ℕ
  /-- When `v` built its round-`n` block — read only at `n ≤ top v`. -/
  built : Validator → ℕ → ℕ
  timeout : ℕ → ℕ
  gst : ℕ
  delay : ℕ
  rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ N
  /-- **Every round `v` reached, it built in.** At `n = 0` this is
  `Live.genesis` — a validator produces its genesis block alone, so this
  much needs no network at all. Above `0` it is the reading of `top`: the
  validator got there, which is to say it built there. -/
  built_of_le_top : ∀ v ∈ T, ∀ n ≤ top v,
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = n
  /-- **And no round above it.** Together with the previous clause, `v`'s
  blocks are exactly rounds `0` through `top v`. -/
  le_top_of_built : ∀ v ∈ T, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round ≤ top v
  /-- **P9, the waiting rule** (protocol), over the rounds `v` reached. -/
  waits : ∀ v ∈ T, ∀ n < top v, built v n + timeout n ≤ built v (n + 1)
  timeout_pos : ∀ n, 1 ≤ timeout n
  /-- An upper bound on when round `n` was built, over `T`. Only an upper
  bound is needed here — `latest_mem` belongs to the drift argument, not
  to this one. -/
  latest : ℕ → ℕ
  built_le_latest : ∀ v ∈ T, ∀ n ≤ N, built v n ≤ latest n
  /-- `latest` is *attained*, not merely an upper bound — the clause the
  drift argument consumes. -/
  latest_mem : ∀ n ≤ N, ∃ w ∈ T, latest n ≤ built w n
  /-- **P9, the promptness rule** (protocol), over the rounds `v` reached.
  Kept so that drift remains *derived* here as it is for `Timing`: without
  it `DriftOn` would have to be assumed, which would be a step backwards
  from the total-schedule routes. -/
  prompt : ∀ v ∈ T, ∀ n < top v,
    built v (n + 1) ≤ max (built v n + timeout n) (latest n + delay)
  holds : Validator → ℕ → Finset BlockId
  /-- A validator holds every block it authored, from the time it built it. -/
  holds_own : ∀ v ∈ T, ∀ n ≤ N, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n → b ∈ holds v (built v n)
  holds_mono : ∀ v, ∀ s t, s ≤ t → holds v s ⊆ holds v t
  /-- **N2, as view convergence** (network). -/
  converges : ∀ v ∈ T, ∀ w ∈ T, ∀ t, gst ≤ t → holds w t ⊆ holds v (t + delay)
  /-- **P7, referencing** (protocol), over any block the validator authors. -/
  references : ∀ v ∈ T, ∀ n < N, ∀ c ∈ U.ids,
    (U.block c).creator = v → (U.block c).round = n + 1 →
    ∀ a ∈ holds v (built v (n + 1)), (U.block a).round = n →
    a ∈ (U.block c).refs
  /-- **P8, as the pacemaker's progress rule** (protocol). A validator that
  holds a quorum of distinct round-`n` authors — *at any time whatever* —
  gets past round `n`.

  This is the clause a total schedule cannot carry honestly. There, the
  quorum had to be in hand at the one time `built v (n+1)` names, so the
  rule either missed it (and the round stayed empty for ever) or, stated as
  a converse, forced the quorum to exist. Here there is no such time: the
  hypothesis is that `v` ever holds a quorum, and the conclusion is that it
  advances. It asserts no production, since it says nothing until a quorum
  is in hand. -/
  advances : ∀ v ∈ T, ∀ n < N, ∀ t,
    (Fintype.card Validator - F.f) ≤
      (creatorsOf U.block ((holds v t).filter fun b => (U.block b).round = n)).card →
    n < top v

namespace ViewPace

variable (vp : ViewPace U T N)

omit [DecidableEq BlockId] in
/-- **The separation, on this route** — V1's content over the partial
schedule. The fused clause the `Timing` layer carried as its network row
(*a `T`-block built after GST and early enough is referenced*) is
derivable from `converges` and `references` alone: the block is in its
author's hands when built (`holds_own`), reaches the builder within
`delay` (`converges`), is still there when the builder acts
(`holds_mono`), and is therefore referenced (`references`). No counting,
no drift, no waiting rule — those enter only when the *hypothesis*
`built … + delay ≤ built … (n+1)` must itself be discharged, which is
the race the drift argument wins.

This is where report §4.3's claim that the network's whole contribution
is one sentence about views is discharged on the route the development
keeps: `converges` mentions no blocks, rounds or references, and the
step from views to references is the protocol's clause P7. -/
theorem covers_of_converges {n : ℕ} (hn : n < N)
    {c : BlockId} (hc : c ∈ U.ids) (hcT : (U.block c).creator ∈ T)
    (hcr : (U.block c).round = n + 1)
    {a : BlockId} (ha : a ∈ U.ids) (haT : (U.block a).creator ∈ T)
    (har : (U.block a).round = n)
    (hgst : vp.gst ≤ vp.built ((U.block a).creator) n)
    (hearly : vp.built ((U.block a).creator) n + vp.delay ≤
      vp.built ((U.block c).creator) (n + 1)) :
    a ∈ (U.block c).refs := by
  refine vp.references _ hcT n hn c hc rfl hcr a ?_ har
  refine vp.holds_mono _ _ _ hearly ?_
  exact vp.converges _ hcT _ haT _ hgst
    (vp.holds_own _ haT n (by omega) a ha rfl har)

omit [DecidableEq BlockId] in
/-- Rounds advance real time, over the rounds a validator reached. -/
theorem le_built {v : Validator} (hv : v ∈ T) : ∀ n ≤ vp.top v, n ≤ vp.built v n := by
  intro n
  induction n with
  | zero => intro _; omega
  | succ n ih =>
      intro hn
      have hw := vp.waits v hv n (by omega)
      have := vp.timeout_pos n
      have := ih (by omega)
      omega

omit [DecidableEq BlockId] in
/-- **Production, with no deadline to beat.** Every round below the horizon
is populated, from genesis, view convergence and the progress rule — and
from nothing else. No drift, no backoff, no `timeout`, and no counterpart
to `ViewGrowth`'s `hcross`.

The step is the familiar one with the deadline removed. Each `w ∈ T`
reached round `n` (induction hypothesis), so it has a block there and holds
it from `built w n`; `holds_mono` carries that forward to
`max (latest n) gst`, a single time serving every `w` at once; `converges`
puts all of them in `v`'s hands by `max (latest n) gst + delay`. That is a
quorum of distinct authors, so `advances` fires and `v` is past round `n` —
whereupon `built_of_le_top` supplies its round-`n+1` block.

**Where `hcross` went.** In `ViewGrowth` the quorum had to arrive by
`built v (n+1)`, a time fixed before the run, and `hcross` was what made
the straddling round late enough to make it. Here the arrival time is not
compared with anything: `advances` takes the quorum at whatever time it
appears. A schedule that raced ahead of the network pre-GST is not excluded
by hypothesis — it is not expressible, because a validator that never held
a quorum at round `n` never reached round `n+1`. -/
theorem reached (vp : ViewPace U T N)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card) :
    ∀ n ≤ N, ∀ v ∈ T, n ≤ vp.top v := by
  intro n
  induction n with
  | zero => intro _ v _; omega
  | succ n ih =>
      intro hn v hv
      -- every `w ∈ T` reached round `n`, so has a block there
      refine Nat.succ_le_of_lt (vp.advances v hv n (by omega)
        (max (vp.latest n) vp.gst + vp.delay) (le_trans hcard (Finset.card_le_card ?_)))
      intro w hw
      obtain ⟨b, hb, hbc, hbr⟩ := vp.built_of_le_top w hw n (ih (by omega) w hw)
      refine mem_creatorsOf.mpr ⟨b, Finset.mem_filter.mpr ⟨?_, hbr⟩, hbc⟩
      -- it holds it when built, hence at the common time `max (latest n) gst`
      have hown := vp.holds_own w hw n (by omega) b hb hbc hbr
      have hle : vp.built w n ≤ max (vp.latest n) vp.gst :=
        le_trans (vp.built_le_latest w hw n (by omega)) (le_max_left _ _)
      exact vp.converges v hv w hw _ (le_max_right _ _) (vp.holds_mono w _ _ hle hown)

omit [DecidableEq BlockId] in
/-- **Production**, read off `reached`: a round a validator got to is a round
it built in. -/
theorem populatedOn (vp : ViewPace U T N)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card) :
    ∀ n ≤ N, PopulatedOn U T n :=
  fun n hn v hv => vp.built_of_le_top v hv n (vp.reached hcard n hn v hv)

omit [DecidableEq BlockId] in
/-- **Drift is derived here too.** `Timing.driftFrom_of_prompt`'s argument
over a partial schedule: the same two-case split on `prompt`'s `max`, with
the round guards discharged by `reached` rather than by the horizon.

Keeping this is what stops the partial schedule being a step backwards. On
the total-schedule routes drift is a consequence of promptness, not an
assumption, and it stays one: what is asked of the implementation is a
common start spread and a backoff clearing `delay`. -/
theorem driftOn_of_prompt (vp : ViewPace U T N)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card) {n₀ D : ℕ}
    (hbase : ∀ v ∈ T, ∀ w ∈ T, vp.built w n₀ ≤ vp.built v n₀ + D)
    (hto : ∀ n, n₀ ≤ n → vp.delay ≤ vp.timeout n) :
    DriftOn vp.built T n₀ D N := by
  have key : ∀ n, n₀ ≤ n → n ≤ N →
      ∀ v ∈ T, ∀ w ∈ T, vp.built w n ≤ vp.built v n + D := by
    intro n
    induction n with
    | zero => intro h0 _ v hv w hw; exact (Nat.le_zero.mp h0) ▸ hbase v hv w hw
    | succ n ih =>
        intro hn hN v hv w hw
        rcases Nat.eq_or_lt_of_le hn with heq | hlt
        · exact heq ▸ hbase v hv w hw
        · have hn₀ : n₀ ≤ n := by omega
          -- both validators reached round `n+1`, so the schedule clauses apply
          have htw : n < vp.top w := by have := vp.reached hcard (n + 1) hN w hw; omega
          have htv : n < vp.top v := by have := vp.reached hcard (n + 1) hN v hv; omega
          have hprompt := vp.prompt w hw n htw
          have hwait := vp.waits v hv n htv
          have hdel := hto n hn₀
          rcases le_total (vp.built w n + vp.timeout n) (vp.latest n + vp.delay) with hc | hc
          · obtain ⟨x, hx, hxle⟩ := vp.latest_mem n (by omega)
            have hxv := ih hn₀ (by omega) v hv x hx
            have hmax : max (vp.built w n + vp.timeout n) (vp.latest n + vp.delay)
                = vp.latest n + vp.delay := max_eq_right hc
            omega
          · have hwv := ih hn₀ (by omega) v hv w hw
            have hmax : max (vp.built w n + vp.timeout n) (vp.latest n + vp.delay)
                = vp.built w n + vp.timeout n := max_eq_left hc
            omega
  exact fun v hv w hw n hn hN => key n hn hN v hv w hw

omit [DecidableEq BlockId] in
/-- **Reference coverage**, exactly `ViewGrowth`'s argument over the partial
schedule. The guards come out of `le_top_of_built`: a block at round `n+1`
authored by `v` puts `n + 1 ≤ top v`, so `waits` and `le_built` apply where
they are used, and the straddling case cannot arise — coverage is claimed
only from `R`, and `gst ≤ R ≤ n ≤ built w n`.

As in `ViewGrowth`, this needs neither production, nor the quorum bound,
nor `T ⊆ Correct`: `references` and `holds_own` are stated over any block a
validator authored, so there is nothing to identify by non-equivocation. -/
theorem synchronisedOn_of_converges {R D : ℕ}
    (hD : DriftOn vp.built T R D N) (hgst : vp.gst ≤ R)
    (hbackoff : ∀ n, R ≤ n → D + vp.delay ≤ vp.timeout n) :
    SynchronisedOn U T R := by
  intro n hn b hb hbr hbc a ha har hac
  have hnN : n < N := by have := vp.rounds_le b hb; omega
  have htopb : n + 1 ≤ vp.top ((U.block b).creator) :=
    hbr ▸ vp.le_top_of_built _ hbc b hb rfl
  have htopa : n ≤ vp.top ((U.block a).creator) :=
    har ▸ vp.le_top_of_built _ hac a ha rfl
  have hle := vp.le_built hac n htopa
  -- the race, won: drift, the wait and the backoff place the arrival first
  have hdrift := hD _ hbc _ hac n hn (by omega)
  have hwait := vp.waits _ hbc n (by omega)
  have hto := hbackoff n hn
  exact vp.covers_of_converges hnN hb hbc hbr ha hac har (by omega) (by omega)

section Liveness

variable [S : Slots Validator]

/-- **The liveness spine over a partial schedule.** The conclusion of V15
and V16 with the seed at round `0`, where it is genesis, and **no `hcross`**:
the schedule hypothesis is gone, not weakened.

What remains divides cleanly. The network contributes `converges` and
`vp.gst ≤ R`. The protocol contributes `built_of_le_top` at round `0`
(genesis), `advances` (the pacemaker does not stall), `references` (P7) and
`waits` (P9); drift and the backoff are needed only for coverage, and
`driftFrom_of_prompt`'s argument discharges the first from promptness as
before. Production needs none of them. -/
theorem commits_recur_via_pace (hT : T ⊆ (Correct : Finset Validator))
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (fair : FairScheduleOn T) (R k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (N D : ℕ)
        (vp : ViewPace U T N),
        DriftOn vp.built T R D N → vp.gst ≤ R →
        (∀ n, R ≤ n → D + vp.delay ≤ vp.timeout n) →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) := by
  obtain ⟨k', hk, hR, hcommit⟩ :=
    commits_recur_on (BlockId := BlockId) (Payload := Payload) hT hcard fair R k
  refine ⟨k', hk, hR, fun U N D vp hD hgst hbackoff hN => ?_⟩
  exact hcommit U N
    (fun r _ hr => vp.populatedOn hcard r hr)
    (vp.synchronisedOn_of_converges hD hgst hbackoff)
    hN

end Liveness

/-! ## The quantitative arc, on this route

Report §6.10's results, over the partial schedule. `Rated`, `FairWithin`
and `BoundedSpacing` are properties of the timeout and the schedule alone
and carry over verbatim; what needs restating is everything that took a
`Timing` — the explicit coverage round, and the wait bound.

One question had to be settled first (`liveness-routes.md` §9): what a
wait bound means when a validator can be stuck. The answer is `reached`:
with `T` a quorum and the progress rule, no `T`-validator is stuck below
the horizon — as a *theorem*, where the total schedule had it as the
shape of a field. The bounds then read exactly as they did. -/

section Quantitative

omit [DecidableEq BlockId] in
/-- Drift from a later round is implied by drift from an earlier one. -/
theorem _root_.LeanDag.DriftOn.mono {built : Validator → ℕ → ℕ}
    {n₀ n₁ D : ℕ} (h : n₀ ≤ n₁) (hd : DriftOn built T n₀ D N) :
    DriftOn built T n₁ D N :=
  fun v hv w hw n hn hN => hd v hv w hw n (le_trans h hn) hN

omit [DecidableEq BlockId] in
/-- **Q3 on this route** — coverage from an explicit round, under a rated
backoff: `R = max (max (D + delay) n₀) gst`, each summand what it looks
like. `Timing.synchronisedOn_of_rate` with the structure swapped and
`T ⊆ Correct` gone. -/
theorem synchronisedOn_of_rate (vp : ViewPace U T N)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hrate : Rated vp.timeout) {n₀ D : ℕ} (hn₀ : vp.delay ≤ n₀)
    (hbase : ∀ v ∈ T, ∀ w ∈ T, vp.built w n₀ ≤ vp.built v n₀ + D) :
    SynchronisedOn U T (max (max (D + vp.delay) n₀) vp.gst) := by
  refine vp.synchronisedOn_of_converges
    (DriftOn.mono (le_trans (le_max_right (D + vp.delay) n₀) (le_max_left _ _))
      (vp.driftOn_of_prompt hcard hbase
        (fun n hn => backoff_ge_of_rate hrate _ n (le_trans hn₀ hn))))
    (le_max_right _ _) ?_
  exact fun n hn =>
    backoff_ge_of_rate hrate _ n (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn)

variable [S : Slots Validator] {D₀ k : ℕ}

/-- **The wait bound** (Q2 headline, report §6.10): a validator that knows
the delivery bound and its start spread needs no backoff — a constant
timeout of `D₀ + Δ` commits every reliable-led slot past GST. Production
here is derived, so unlike `directCommit_of_wait` over `Timing` nothing
asserts blocks above round `0`, and `T ⊆ Correct` is not consumed. -/
theorem directCommit_of_wait (vp : ViewPace U T N)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hstart : ∀ v ∈ T, ∀ w ∈ T, vp.built w 0 ≤ vp.built v 0 + D₀)
    (hwait : ∀ n, D₀ + vp.delay ≤ vp.timeout n)
    (hgst : vp.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) := by
  have hsync : SynchronisedOn U T (S.slotRound k) :=
    vp.synchronisedOn_of_converges
      (DriftOn.mono (Nat.zero_le _)
        (vp.driftOn_of_prompt hcard hstart
          (fun n _ => le_trans (Nat.le_add_left _ _) (hwait n))))
      hgst (fun n _ => hwait n)
  exact directCommit_of_leader_mem hcard hsync (le_refl _)
    (vp.populatedOn hcard _ (by omega)) (vp.populatedOn hcard _ (by omega))
    (vp.populatedOn hcard _ (by omega)) hlead

/-- **The wait bound, as a decision.** -/
theorem decided_of_wait (vp : ViewPace U T N)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hstart : ∀ v ∈ T, ∀ w ∈ T, vp.built w 0 ≤ vp.built v 0 + D₀)
    (hwait : ∀ n, D₀ + vp.delay ≤ vp.timeout n)
    (hgst : vp.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLb, hdc⟩ := vp.directCommit_of_wait hcard hstart hwait hgst hN hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_full hdc)⟩

/-- **`Delay(Δ) = 2Δ`** — the headline case, over the partial schedule. -/
theorem directCommit_of_wait_two_delay (vp : ViewPace U T N)
    (hcard : (Fintype.card Validator - F.f) ≤ T.card)
    (hstart : ∀ v ∈ T, ∀ w ∈ T, vp.built w 0 ≤ vp.built v 0 + vp.delay)
    (hwait : ∀ n, 2 * vp.delay ≤ vp.timeout n)
    (hgst : vp.gst ≤ S.slotRound k) (hN : S.slotRound k + 2 ≤ N)
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) :=
  vp.directCommit_of_wait hcard hstart (fun n => by have := hwait n; omega) hgst hN hlead

end Quantitative

end ViewPace

end LeanDag
