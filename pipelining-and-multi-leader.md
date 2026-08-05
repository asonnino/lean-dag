# lean-dag — Pipelining and multiple leaders

Design notes for extending the safety and liveness results from the
single-leader, three-round-spaced commit rule now in `spec.md` and
`liveness.md` to the **pipelined, multi-leader** Mysticeti-C rule actually
deployed. Things graduate into `spec.md` once they settle.

> **Status.** **P0–P6 are implemented and the full build is clean** — stages
> 1–7 of §11. The claim of §6.3, that the agreement induction survives the
> premise change, held exactly as predicted: `decided_unique` needed the extra
> constructor argument threaded and one hypothesis swapped per trichotomy
> branch, and no counting was redone.
>
> **P7 is resolved, and was false as stated.** "After `R`, every slot is
> decided" fails under pipelining, with a concrete counterexample (§9.5). What
> holds and is proved is the conditional L8, `decided_of_committed_above`: given
> one committed slot, every slot below it is decided — provided every later slot
> may anchor an earlier one, which is exactly the old three-round spacing and
> exactly what pipelining destroys. The refutation itself is machine-checked as
> L9, `notMem_stuck_of_decided`; what is *not* yet built is a concrete universe
> satisfying its two DAG-level hypotheses. This is the substantive finding of the
> exercise; Q1 is reformulated accordingly and `P8` (the general `Schedule`
> flattening) remains. See §14 for what implementation changed.
>
> §3 is the schedule layer — how a reader writes a schedule down and how the
> present one is recovered (P0, P8). §5–§8 are the safety half (P1–P3).
> §9–§10 are the liveness half (P4–P7), where the one genuinely new theorem
> lives. §11 stages the nine obligations, names the files each touches, and
> lists the witnesses. §12 is what has to be decided first — only Q1 is
> genuinely open — and §13 what is settled.

**The thesis in one paragraph.** The development is already parametric in the
leader schedule: `Slots` is a class, and every safety theorem takes it as an
instance. Pipelining and multiple leaders per round are, between them, exactly
one weakening of one field of that class — `spacing : ∀ k, slotRound k + 3 ≤
slotRound (k+1)` becomes `Monotone slotRound`. Everything that breaks, breaks
because it consumed that field. There are five such places, and only two
consume it directly. The repair is to stop *deriving* the three-round separation
between a slot and its anchor and start *requiring* it, as a premise on the
indirect constructors — which is what the deployed protocol does anyway. The
substantial claim of this document is that the agreement induction survives
that change, and §6.3 gives the reason.

## 1. What the existing development already gives

Worth listing, because most of what follows is assembled from it rather than
built. None of these mentions `Slots`:

| | |
|---|---|
| **T1** `eq_of_creator_eq` | a correct author has one block per round |
| **T0′** `exists_common_mem_of_quorums` | two reference quorums share a block by a correct author |
| `ValidWrt.distinct_creators` | one block never references two blocks by one author |
| **T2, T3, T3c** | causal history; quorum-backed blocks are unavoidable |
| **M1** `not_directCommit_of_directSkip` | commit and skip are exclusive |
| **M2** `exists_certificate_reaches_of_directCommit` | from round `r+3` on, a certificate is in reach |
| **M3** `certificates_eq_empty_of_directSkip` | a skipped block has no certificate anywhere |
| **M5′** `eq_of_certificates_nonempty` | at most one certifiable block per (round, author) |
| **L0** `card_authorsAt_of_lt` | the DAG is dense below its frontier |
| **L2, L3** `decided_mono`, `decided_full` | decisions are monotone in the view and propagate |

The three-round structure of the *commit pattern* — proposal at `r`, votes at
`r+1`, certificates at `r+2`, unavoidability from `r+3` — is baked into
`certificates`, `Certifies` and M2, and **none of it changes**. Pipelining does
not shorten the pattern; it overlaps successive copies of it. This is worth
saying plainly because it is the usual confusion: pipelining buys recurrence,
not depth. A slot is still decided three rounds after its proposal.

The reason the overlap costs nothing is §3 of the report: *every role is
assigned by the reader of the DAG, not by its writer*. A round-`(r+2)` block is
already permitted to be a certificate for the slot at `r`, a vote for the slot
at `r+1`, and a proposal for the slot at `r+2`, because nothing in `Block` or
`ValidWrt` records which of these it is. Uncertified-DAG modelling pays for
itself here: the single most conspicuous feature of pipelining requires no
change to the model at all.

## 2. The protocol, as specified

From Mysticeti-C (Babel, Chursin, Danezis, Kokoris-Kogias, Sonnino,
arXiv:2310.14821), Algorithms 1–3. Parameters: `waveLength` (3), `roundOffset`,
`numOfProposers` (the paper's Section VII sets it to 2).

- `ProposerRound(w) = w·waveLength + roundOffset`, `DecisionRound(w) =
  w·waveLength + waveLength − 1 + roundOffset`. With `waveLength = 3` a slot
  proposed at round `r` has voting round `r+1` and decision round `r+2`.
- `SkippedProposer`: `≥ 2f+1` blocks at `r+1` with no parent by the leader.
  This is `DirectSkip` with `blames` at `r+1`.
- `SupportedProposer`: `≥ 2f+1` blocks at `r+2` each of which is a certificate,
  where `IsCert(b, L)` counts `≥ 2f+1` of `b`'s parents voting for `L`. This is
  `DirectCommit` over `certificates U L r`.
- `TryDecide` walks slots downward from the highest round to the last committed
  round, and within a round over proposer offsets, prepending — so the
  `sequence` it builds is in increasing (round, proposer) order.
- `CertifiedLink(A, L)`: some `b` at the decision round is a certificate for `L`
  with a path from `b` up to `A`. This is exactly `CertifiedIn U A L r`.

The clause that matters is the anchor filter in `TryIndirectDecide`:

```
r_decision ← c.DecisionRound(w)                  -- = r + 2
anchors    ← [s ∈ sequence  s.t.  r_decision < s.round]
for a in anchors:
    if a = ⊥            then return ⊥
    if a = Commit(A)    then return CertifiedLink(A, L) ? Commit(L) : Skip
return ⊥
```

`r_decision < s.round` is `slotRound k + 3 ≤ slotRound s`. **The deployed
protocol does not anchor on the nearest later slot. It anchors on the nearest
later slot that is at least three rounds ahead**, walking past nearer ones
whatever they decided, and stalling only on an undecided *eligible* slot. Under
`+3` spacing every later slot is eligible and the two readings coincide, which
is why the present development can get away with `k < j`. Under pipelining they
come apart, and the difference is not cosmetic: slots `k+1` and `k+2` sit at
rounds `r+1` and `r+2`, and a block at those rounds *cannot* reach a
round-`(r+2)` certificate, so anchoring on them would turn every direct commit
into somebody else's indirect skip. Agreement would fail on the first
pipelined commit.

## 3. The two generalisations are one weakening

### 3.1 The class

Keep slots indexed by `ℕ`, as the linearisation of (round, proposer offset)
that `TryDecide` already builds. Then:

- **Pipelining** is `slotRound (k+1) = slotRound k + 1`.
- **Multiple leaders** is `slotRound (k+1) = slotRound k` for the slots sharing
  a round.

Both are instances of `Monotone slotRound`. The proposed class:

```lean
class Slots (Validator : Type*) where
  slotRound : ℕ → ℕ
  leader    : ℕ → Validator
  mono      : Monotone slotRound
  unbounded : ∀ n, ∃ k, n ≤ slotRound k
  keyed     : Function.Injective (fun k => (slotRound k, leader k))
```

Three remarks.

`mono` replaces `spacing`. The present schedule is the instance
`slotRound k = 3k`, so nothing already proved is lost; §11 keeps it as a
witness.

`unbounded` is new **as a field** but not as a fact: today it is the theorem
`le_slotRound : 3 * k ≤ S.slotRound k`, derived from `spacing`. Under `mono`
alone it is underivable — a schedule that parks every slot at round 7 is
monotone — and liveness needs it (§9.2), so it becomes an assumption. It is
implied by pipelining and by any bounded-spacing schedule.

`keyed` is new as a fact. `IsLeaderBlock` identifies a slot's candidates by
`(round, creator)`, so two distinct slots with the same round and the same
leader have literally the same candidate set: one block, committed at two
slots, delivered twice by `commitSeq`. Today this cannot arise, because
`spacing` makes `slotRound` injective on its own. Under multiple leaders it is
a real obligation on the leader-election function — the requirement that the
`numOfProposers` proposers of a round be distinct validators. Round-robin and
HammerHead both satisfy it; nothing in the model would notice if a schedule did
not. §3.2 moves it somewhere it is checkable rather than assumed.

### 3.2 P8 — the schedule layer: what a user actually writes

`Slots` is the right *interface* — every theorem downstream indexes slots by
`ℕ` and should keep doing so — but it is the wrong thing to ask a reader to
write down. Nobody thinks of a leader schedule as a pair of functions out of
`ℕ` with three side conditions; they think of it as *which validators propose
in which round*. So put a second layer above it, and let `Slots` be derived:

```lean
/-- A leader schedule, as the protocol states it. -/
structure Schedule (Validator : Type*) where
  leaders : ℕ → List Validator
  nodup   : ∀ n, (leaders n).Nodup
  cofinal : ∀ n, ∃ m, n ≤ m ∧ leaders m ≠ []
```

**A `List`, not a `Finset`.** The obvious reading of "a set of (round,
validators)" is `ℕ → Finset Validator`, and it is not quite enough: when a
round has several leaders their slots are committed in a definite order, and
that order is visible in the ledger — `TryDecide` iterates proposer offsets and
`commitSeq` reads slots in order, so two validators disagreeing about the order
within a round would deliver different sequences. A `Finset` would force a
`LinearOrder` on `Validator` to recover it, which is an assumption the schedule
can simply supply instead. Empty lists are allowed and are exactly how "a
leader every third round" is said.

The two side conditions are the two new facts of §3.1, relocated to where they
are checkable:

- `nodup` gives `keyed`. Two slots sharing a round and a leader would be two
  positions in one list holding the same validator.
- `cofinal` gives `unbounded`. Without it the flattening below is finite and
  `slotRound` is not total.

`mono` needs no condition: it holds by construction.

Slot `k` is then the `k`-th entry of `leaders 0 ++ leaders 1 ++ ⋯`. Writing
`count n = Σ_{i<n} (leaders i).length` for the slots strictly below round `n`,
the derivation is

```lean
def Schedule.toSlots (sch : Schedule Validator) : Slots Validator
-- slotRound k = the least n with k < count (n+1)      (Nat.find, via cofinal)
-- leader    k = (sch.leaders (slotRound k)).get (k - count (slotRound k))
```

with the characterisation lemma that every concrete instance will want:

```lean
theorem slotRound_eq_iff : sch.toSlots.slotRound k = n ↔ count sch n ≤ k ∧ k < count sch (n+1)
```

### 3.3 P0 — recovering the present development, and the schedules worth having

Every schedule anyone deploys is *uniform*: `m` leaders in every `p`-th round.
That case has a closed form and needs none of the flattening machinery, so it
is worth a constructor of its own —

```lean
def Slots.uniform (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (elect : ℕ → Validator)
    (hblock : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂) :
    Slots Validator where
  slotRound k := p * (k / m)
  leader    k := elect k
```

`mono` is monotonicity of `k / m`; `unbounded` holds since
`slotRound (m * n) = p * n ≥ n`; `keyed` is `hblock` — equal slot rounds force
`k₁ / m = k₂ / m` because `p > 0`, and then equal leaders force `k₁ = k₂`.
`hblock` says only that the `m` proposers of a round are distinct, and
round-robin `elect k = k % (3f+1)` with `m ≤ 3f+1` satisfies it.

| | `p` | `m` | `slotRound k` | |
|---|---|---|---|---|
| present development | 3 | 1 | `3k` | `spacing` holds with equality |
| pipelined, one leader | 1 | 1 | `k` | |
| pipelined, `m` leaders | 1 | `m` | `k / m` | the deployed rule |
| slow multi-leader | 3 | `m` | `3 * (k / m)` | |

The first row is the conservativity check the whole exercise turns on, and it
is a two-line proof: `Slots.uniform 3 1 _ _ rr` has `slotRound k = 3 * (k / 1)
= 3 * k`, so `slotRound k + 3 ≤ slotRound (k + 1)` by `omega`. Every theorem
proved against the generalised class therefore specialises to the current one
with no reproof, and `LeanDagTest` can keep its existing instances by
rebuilding them through `uniform`.

So there are two entry points and they do not compete: `Slots.uniform` for the
regular schedules, which is everything above plus every witness in §11, and
`Schedule.toSlots` for genuinely irregular ones. The general layer is what
makes the claim *"an arbitrary assignment of validators to rounds works"* a
theorem rather than a family of examples; the uniform layer is what makes the
examples cheap. §11 stages them in that order — uniform first, because nothing
else waits on the flattening.

## 4. Where the three rounds are load-bearing

Every occurrence, from a full sweep of the source:

| Site | Uses | Verdict |
|---|---|---|
| `Mysticeti.slotRound_add_three_le` | `spacing` | **deleted**; it is exactly the fact that stops being true |
| `Mysticeti.certifiedIn_of_directCommitIn` | the above | **premise change**: takes the separation instead of deriving it |
| `Liveness.le_slotRound` | `spacing` | **replaced** by `Slots.unbounded` |
| `Liveness.commits_recur_on` | `le_slotRound`, `slotRound_add_three_le` | **reproved** against `unbounded` and `mono` |
| `Quantitative.commits_recur_within` | the same two | **reproved**, and the bound improves (§10) |

That is the whole inventory. `BoundedSpacing`, which bounds slot rounds from
*above*, still compiles: under pipelining it holds with `s = 1`, and with `m`
leaders per round it *also* holds with `s = 1` and not with `s = 0`, since
consecutive slots either share a round or advance it by one. That it cannot
distinguish those two cases is the reason §10 replaces it rather than reusing
it.

Nothing in `Block`, `BlockDag`, `CausalHistory`, `Support`, `Persistence`,
`CommonCore` or `Timing` mentions `Slots` at all.

## 5. The repair: eligible anchors

```lean
/-- The round at which slot `k`'s direct rules are settled: its certificates
live here. Algorithm 2's `DecisionRound`. -/
def decisionRound (k : ℕ) : ℕ := S.slotRound k + 2

/-- `j` may anchor `k`: its proposal is past `k`'s decision round, so a block
at `j`'s round can reach a certificate for `k`'s. Algorithm 3's
`r_decision < s.round`. -/
def Eligible (k j : ℕ) : Prop := decisionRound k < S.slotRound j

instance : DecidablePred fun p : ℕ × ℕ => Eligible p.1 p.2 := …
```

Stated through `decisionRound` rather than as a bare `+ 3` so that the
wavelength generalisation of Q2 is a change to one definition. It unfolds to
`S.slotRound k + 3 ≤ S.slotRound j`, which is what the proofs consume.

Two small lemmas the constructors and the witnesses want:

```lean
theorem lt_of_eligible (h : Eligible k j) : k < j          -- from `mono`
theorem eligible_of_lt (h : k < j) : Eligible k j          -- under the OLD spacing only
```

The first makes the `k < j` premise below strictly redundant. It is kept
anyway, because `decided_unique` recurses on it and `lt_trichotomy` consumes it
directly; deriving it at each of the four use sites would be noise. The second
is the conservativity statement for the decision relation: under `+3` spacing
eligibility is implied by lateness, so the revised `Decided` has exactly the
old constructors available and no derivation is lost. Worth proving for the
`uniform 3 1` instance as the companion to §3.3's `slotRound k = 3 * k`.

Also under `mono` the eligible slots above `k` are **upward-closed**: there is
a first one, and the intermediate premise below says "every slot from that one
up to the anchor was skipped".

The revised relation, with the changes marked:

```lean
inductive Decided (U) (V : View …) : ℕ → Option BlockId → Prop
  | directCommit  … unchanged …
  | directSkip    … unchanged …
  | indirectCommit {k j A L} :
      k < j → Eligible k j →                                    -- NEW
      Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible k i → Decided U V i none) → -- RESTRICTED
      IsLeaderBlock U k L → CertifiedIn U A L (S.slotRound k) →
      Decided U V k (some L)
  | indirectSkip {k j A} :
      k < j → Eligible k j →                                    -- NEW
      Decided U V j (some A) →
      (∀ i, k < i → i < j → Eligible k i → Decided U V i none) → -- RESTRICTED
      (∀ L, IsLeaderBlock U k L → ¬ CertifiedIn U A L (S.slotRound k)) →
      Decided U V k none
```

The recursive occurrences stay **strictly positive**: `Eligible k i` is a
predicate on two naturals and does not mention `Decided`, so guarding
`Decided U V i none` behind it leaves the definition acceptable to Lean's
positivity check, which was the reason the intermediate premise was stated
positively in the first place.

Both edits are forced, and for opposite reasons.

Adding `Eligible k j` is forced **by safety**: without it the engine lemma has
no round hypothesis and agreement fails, as §2 describes.

Restricting the intermediate quantifier to eligible `i` is forced **by
liveness**: `Decided V i none` for the ineligible `i ∈ {k+1, k+2}` is not
something a validator can wait for — those slots are commonly *committed*, and
under the unrestricted premise slot `k` would then never be decidable at all.
The claim that this restriction is nonetheless safe is §6.3, and it is the one
claim in this document that is not routine.

## 6. Safety: the obligations

### 6.1 Unchanged (no proof work)

M1, M2, M3, M5′ and M5 are stated at the round level over `certificates U L r`
and never mention `Slots`. So is **M4 in both halves**:
`certifiedIn_of_directCommit` already takes `r + 3 ≤ (U.block A).round` as an
explicit hypothesis rather than deriving it from the schedule, and
`not_certifiedIn_of_directSkip` needs no round hypothesis at all — which is
precisely why the repair of §5 is a premise change and not a reproof. Their
combination `indirect_agrees_with_direct` is likewise untouched.

`directCommit_of_directCommitIn`, `directSkip_of_directSkipIn`,
`certifiedIn_iff_of_view`, `not_directSkipIn_of_directCommitIn`,
`eq_of_directCommitIn`, `not_certifiedIn_of_directSkipIn`,
`certificates_nonempty_of_*` and `eq_of_hasCertificate` likewise. Expect all of
these to compile against the new class untouched.

### 6.2 P1 — the engine, re-premised

```lean
theorem certifiedIn_of_directCommitIn
    (h : DirectCommitIn U V L (S.slotRound k))
    (hA : A ∈ U.ids) (hAr : (U.block A).round = S.slotRound j)
    (helig : Eligible k j) :                    -- was (hkj : k < j)
    CertifiedIn U A L (S.slotRound k)
```

The body loses its appeal to `slotRound_add_three_le` and feeds `helig` to
`certifiedIn_of_directCommit` directly. Strictly a simplification. Every call
site is inside `decided_unique`, and each has an `Eligible` premise in hand
from the constructor it just destructured.

### 6.3 P2 — agreement (M6), and why the induction survives

This is the load-bearing claim. `decided_unique` is a structural induction over
sixteen constructor pairings; fifteen close on Stage A and are unaffected. The
real case is *indirect commit at `k` with anchor `j`* against *indirect skip at
`k` with anchor `j₂`*, settled by `lt_trichotomy j j₂`:

- `j < j₂`. The current proof invokes the other validator's intermediate
  premise at `j`, `hmid₂ j hkj hlt : Decided V₂ j none`, and contradicts it with
  the IH against `hj : Decided V₁ j (some A)`. Under the restriction, `hmid₂`
  now demands a third argument, `Eligible k j` — **which is precisely the new
  premise carried by V₁'s own derivation**. It is available, verbatim, with no
  transport.
- `j = j₂`. Unchanged: the IH identifies the anchor blocks and `hcert` meets
  `hnone₂`.
- `j > j₂`. Symmetric, using V₁'s intermediate premise and V₂'s eligibility.

The reason this works, and the design constraint it imposes: **`Eligible` is a
predicate on the pair `(k, j)` alone.** Both derivations concern the same slot
`k`, so V₁'s notion of which slots may anchor `k` is identical to V₂'s, and
each validator's eligibility premise is exactly the side condition the other's
intermediate premise requires. Had eligibility been made view-relative — "an
anchor I can see far enough ahead", say, or anything indexed by the decider —
the two would not match and the induction would have nothing to stand on. This
is the same discipline that forced `CertifiedIn` to be universe-level (report
§3.3), arriving from a different direction.

The direct-commit-against-indirect-skip case is P1's call site and closes the
same way, taking `helig` from the `indirectSkip` constructor instead of from
`hkj`.

`decided_agree`, `eq_of_decided_commit` and `not_decided_skip_of_decided_commit`
are corollaries and follow.

### 6.4 P3 — well-formedness of the schedule

`keyed` is consumed nowhere in the safety proofs directly; its job is to make
`IsLeaderBlock` slot-faithful, which the *ledger* results need (§8). State it,
and prove the one lemma:

```lean
theorem slot_eq_of_isLeaderBlock (h₁ : IsLeaderBlock U k₁ L) (h₂ : IsLeaderBlock U k₂ L) :
    k₁ = k₂
```

## 7. Multiple leaders, specifically

Three things could have gone wrong here and, on inspection, do not.

**Certificate uniqueness across co-round slots.** M5′ concludes `L₁ = L₂` from
`(U.block L₁).creator = (U.block L₂).creator`, and its proof runs through
`ValidWrt.distinct_creators`: a common correct voter's single round-`(r+1)`
block references both candidates, which distinctness forbids unless they
coincide. Two slots in the *same round with different leaders* have different
creators, so M5′ simply does not apply to them and does not need to — they are
different slots and may both commit. Two candidates for the *same* slot have
the same creator by `IsLeaderBlock`, which is the hypothesis M5′ wants. The
proof is indifferent to how many slots share a round.

This is also where the model's `L ∈ (U.block q).refs` vote rule earns its keep.
The paper implements votes through `SupportedBlock`, a depth-first traversal
returning the *first* block for the slot encountered, precisely so that its
Lemma 4 (a correct validator never supports two proposals for one slot) holds.
`ValidWrt.distinct_creators` discharges the same obligation structurally, one
layer down, and does so per-author rather than per-slot — which is what makes
it insensitive to the number of leaders in a round.

**Skip counting.** `DirectSkip U L r` counts round-`(r+1)` blocks omitting `L`,
per candidate block. Candidates for different co-round slots are counted
independently; a voter that references leader 0's block but not leader 1's
blames the latter and not the former. No change.

**Self-anchoring.** A slot cannot anchor itself, nor can a co-round slot anchor
it: `Eligible k j` needs a strict three-round gap, which co-round slots fail by
construction. Under the old `k < j` premise a co-round slot *would* have
qualified — another way to see that `k < j` was never the right condition, only
an adequate proxy under `+3` spacing.

## 8. The ledger and total order

`commitSeq`, `ledgerSet`, `OutputAt` and their four theorems are stated over
`g : ℕ → Option BlockId` and the slot order on `ℕ`. They are already agnostic
to how slots map onto rounds, so they should carry over unchanged — **given**
that the linearisation of (round, proposer) into `ℕ` is fixed and identical for
all validators, which it is, being a function of the public schedule.

Two things to record rather than prove:

`keyed` (P3) is what stops a block appearing twice in `commitSeq` at two slots.
Without it `outputAt_unique` still holds — `OutputAt` takes the *first* slot —
but the delivered sequence would repeat a block, which is a total-order defect
the current statements do not see. Worth a witness in §11 to make the failure
concrete, and worth noting in `spec.md` that `keyed` is what excludes it.

The within-commit ordering problem is unchanged and unchanged in character:
committing a leader releases its whole causal history, and the blocks inside
one flush are still unordered for want of a `LinearOrder` on ids (report §5.6).
Multiple leaders per round make the flushes more frequent and smaller. They do
not make this problem harder or easier.

## 9. Liveness

### 9.1 Unchanged

L0 (density), L2 (monotonicity), L3 (propagation), L7 (`Synchronised` from
delivery), the `Delivery` layer and all of `Timing` are round-level and
slot-free. L4 (`directCommit_of_leader_mem`) and L5 (an absent leader is
skipped) are stated at a single slot and consume its three rounds being
populated and synchronised; they do not consume `spacing`. Expect these to
compile untouched.

### 9.2 P4 — commits recur

`commits_recur_on` needs, for a given slot `k` and synchrony round `R`, a later
slot whose round is at least `R` and whose leader lies in `T`. Today it gets
past `R` via `le_slotRound : 3 * k ≤ slotRound k`. Reproving it against
`Slots.unbounded` and `mono` is mechanical: `unbounded` supplies a slot at
round `≥ R`, `mono` makes every later slot at least that late, and
`FairScheduleOn T` supplies a leader in `T` beyond it. `FairScheduleOn` itself
is a condition on `leader` and needs no change.

### 9.3 P5 — the wait bound

`commits_recur_within` combines `FairWithin T w` with `BoundedSpacing s`.
`FairWithin` is a condition on `leader` alone and survives verbatim. The only
change is in `commits_recur_within`'s two appeals to `le_slotRound` and
`slotRound_add_three_le`, which go the way P4's do.

`commits_recur_by_round`, which is where `BoundedSpacing` is consumed, is a
different matter: §10 shows the bound it produces is blind to multiple leaders,
so it should be **restated against `Slots.uniform`** rather than reproved
against `BoundedSpacing`. Keep the `BoundedSpacing` version too — it is the
only thing that says anything at all about an irregular schedule — but stop
quoting it as the headline.

### 9.4 P6 — no ineligible-anchor starvation

New, and small. Under the restricted intermediate premise, a validator deciding
`k` must find its anchor among eligible slots. Show that eligible slots above
any `k` exist:

```lean
theorem exists_eligible (k : ℕ) : ∃ j, Eligible k j
```

Immediate from `unbounded` at `slotRound k + 3`. Trivial, but it is the fact
that stops the restriction of §5 from being vacuously unsatisfiable, and it is
where `unbounded` pays for itself a second time.

### 9.5 P7 — no undecided slot below a commit (**resolved: false as stated**)

**The development proves that commits *recur*, not that every slot is
*decided*.** The ledger is the sequence read off in slot order up to the first
undecided slot, so one permanently undecided slot withholds delivery of
everything above it however many commits recur beyond. The paper keeps this
deliberately ("Mysticeti-C applies some backpressure through undecided slots,
to preserve safety").

Earlier drafts of this section proposed proving that after `R` every slot is
decided, and flagged as Q1 the worry that the downward induction might need an
extra hypothesis. **It needs more than that: the statement is false under
pipelining, and the counterexample is concrete.** What is true, and is now
proved, is the conditional statement L8 below. The distinction is the most
substantive thing this exercise turned up, so it is worth setting out
carefully.

#### What is true: L8

```lean
theorem decided_of_committed_above
    (helig : ∀ a b : ℕ, a < b → Eligible Validator a b)
    (hn : Decided U V n (some A)) :
    ∀ i, i ≤ n → ∃ v, Decided U V i v
```

Given one committed slot, *every* slot below it is decided — no synchrony, no
timing, no fairness. Pure decision-relation combinatorics, which is why it is
worth isolating. The proof takes the **nearest** committed slot above `i` (by
`Nat.find`, classically, since `Decided` is a Prop) and reads the intermediate
premise off the induction hypothesis: an intermediate slot is decided by
induction, and cannot be decided `some` without contradicting nearestness, so
it is decided `none`. It never consults the direct rules — where the direct rule
commits, M2 puts the certificate in reach of the anchor anyway, and M6
guarantees agreement regardless.

`all_decided_below_of_spacing` composes it with L6: under the old three-round
spacing, for every `k` there is an `n ≥ k` such that a sufficiently grown
synchronous DAG decides every slot up to `n`.

#### Why the hypothesis cannot be dropped

`helig` — every later slot is an eligible anchor — is exactly the old spacing
condition (`eligible_of_lt_of_spacing`), and exactly what pipelining destroys.
The counterexample, at `f = 1`, `n = 4`:

Let the schedule be pipelined, and let every slot between the `T`-led ones be
led by a Byzantine validator that publishes its candidate to exactly one
correct validator before that validator builds its next block. Then the
candidate collects two votes — one short of the three a certificate needs — and
two blames, one short of a skip. So the slot is undecided **directly and
permanently**: rounds `r+1` and `r+2` are fixed sets of blocks, so neither
count ever grows.

This is consistent with every hypothesis in the model, and the reason is worth
stating plainly: `SynchronisedOn` (`Liveness.lean:280`) requires a `T`-block to
reference the previous round's blocks **whose creators are also in `T`**. A
Byzantine-authored candidate is not covered by it at all, so synchrony does not
force correct validators to vote for it.

Now take `j` a committed slot and consider slot `j - 1`. It cannot anchor on
`j`: under pipelining `j` sits one round on, inside `j-1`'s decision round. So
it must anchor on the next committed slot `j'`, and its intermediate range then
contains `j' - 1`, which for the same reason must anchor beyond `j'`, whose
range contains `j'' - 1`, and so on. Every `Decided` derivation is a finite
tree, so a chain of strictly smaller sub-derivations that never bottoms out is
no derivation at all: **slot `j - 1` is undecided permanently.**

Under the old spacing the same construction collapses, because `j` *is*
eligible for `j - 1` and the intermediate range is empty. That is the whole
difference, and it is why L8 is stated conditionally rather than dropped.

#### The descent argument, machine-checked: L9

The paragraph above is a proof by hand, and in a development whose point is
machine-checked claims that is the weakest link in it. So the structural half is
now a theorem:

```lean
theorem notMem_stuck_of_decided {X : Set ℕ}
    (hcert : ∀ i ∈ X, ∀ L, IsLeaderBlock U i L → certificates U L (S.slotRound i) = ∅)
    (hskip : ∀ i ∈ X, ∃ L, IsLeaderBlock U i L ∧ ¬ DirectSkipIn U V L (S.slotRound i))
    (hregress : ∀ i ∈ X, ∀ j, Eligible Validator i j → (∃ A, Decided U V j (some A)) →
      ∃ i', i' ∈ X ∧ i < i' ∧ i' < j ∧ Eligible Validator i i')
    (h : Decided U V i v) : i ∉ X
```

`X` is a *stuck* set. Induction on the derivation: direct commit and indirect
commit both produce a certificate and die on `hcert`; direct skip dies on
`hskip`; and indirect skip hands back a strictly smaller sub-derivation at a
slot which `hregress` places back inside `X`. Derivations are finite trees, so
the descent cannot continue — the hand-written appeal to well-foundedness is
now structural induction.

Note what each hypothesis encodes. `hcert` is the half-published candidate: no
certificate anywhere, so nothing can commit the slot by either route. `hskip`
requires a candidate to *exist* and not be skippable — a slot whose leader
published nothing at all is skipped vacuously, so the counterexample genuinely
needs a leader that speaks to some correct validators and not enough of them.
`hregress` is the pipelining-specific clause.

`stuck_empty_below_commit_of_spacing` then composes L8 with L9 to show the two
are consistent and that neither is vacuous: under the old spacing a stuck set
has **no** member at or below a committed slot, however the DAG is arranged. So
L9 is not the observation that its hypotheses are unsatisfiable — it is that
they are unsatisfiable *under `helig`*, and satisfiable without it. The
witnesses in `LeanDagTest/Pipelined.lean` close the loop on `hregress`
arithmetically: under `slotRound k = k` an eligible anchor beyond `i + 3` always
leaves an eligible intermediate, and under `slotRound k = 3k` the anchor `i + 1`
leaves none.

**What is still not checked.** L9 takes `hcert` and `hskip` as hypotheses; no
concrete universe satisfying them is exhibited. That needs a DAG in which a
Byzantine leader's candidate collects exactly `2f` votes and `2f` blames — one
short of each threshold — which is a `LeanDagTest` model of the size of `U7`, not
a lemma. Until it exists, the claim "pipelining loses this guarantee" rests on
the structural theorem plus an unformalised satisfiability argument, and should
be reported that way.

#### What this means

Two readings, and the honest position is that the model does not distinguish
them yet.

*The model is too weak.* `SynchronisedOn` is weaker than the eventual-DAG-
synchrony of `liveness.md`'s opening notes, which say that anything one correct
validator holds, all eventually hold — with no clause about who authored it.
Strengthening it to cover every round-`n` block in `U` would kill the
counterexample. But it cannot be strengthened naively: `ValidWrt.distinct_creators`
forbids one block referencing two blocks by the same author, so demanding that
a block reference *every* round-`n` block in `U` is unsatisfiable as soon as a
leader equivocates. The satisfiable form is "reference *some* round-`n` block by
every author that has one", and under that a leader may still split correct
validators between two equivocating candidates, leaving the slot undecided. So
this route needs care, and probably needs the paper's `SupportedBlock`
traversal rather than `L ∈ refs`.

*The protocol really is more fragile under pipelining.* This is also what the
paper says, in §III-C: undecided slots increase "when some proposer slots are
slow or equivocate", delaying execution, mitigated by choosing well-performing
leaders rather than by any change to the rule. The counterexample is an
adversary that controls delivery precisely and forever, which is exactly the
regime the paper declines to defend against.

Deciding between these is Q1, restated in §12. Nothing in the safety results
depends on it.

## 10. What the bounds become

The per-slot commit depth is unchanged: proposal at `r`, votes at `r+1`,
certificates at `r+2`, unavoidable from `r+3`. Pipelining does not touch this
and cannot; it is the width of the commit pattern.

What improves is recurrence. `commits_recur_by_round` bounds the committing
slot's round by `slotRound (max k R) + s·w + 2`, for `BoundedSpacing s` and
`FairWithin T w`: `s·w` rounds to walk to the next `T`-leader, `+2` for the
certificate round. At the standard settings — round-robin over `3f+1` so
`w = f+1`, slots every three rounds so `s = 3` — that is `3(f+1) + 2`.

Pipelining alone takes `s` from 3 to 1, so the walk cost falls to `f+1`
rounds. Multiple leaders, however, **do not improve this bound as stated**, and
this is worth being precise about rather than asserting a factor of `m`.
`BoundedSpacing s` says `slotRound (k+1) ≤ slotRound k + s`, and under `m`
leaders per round consecutive slots either stay in the round or advance it by
one — so `s` is still `1`, not `0`, and `s·w` still reads `w` rounds for `w`
slots. The bound is loose by exactly the factor of interest: only one step in
`m` actually advances the round, and `BoundedSpacing` cannot see that.

What is wanted is `slotRound (k + w) ≤ slotRound k + p * ⌈w/m⌉`, which needs the
schedule to expose `m` — and `Slots.uniform` (§3.3) does, in closed form, so
this is a computation rather than a new hypothesis. Restating the quantitative
results against `uniform` in place of `BoundedSpacing` takes the walk cost to
`p * ⌈w/m⌉` and the headline from `3(f+1)` to `⌈(f+1)/m⌉`. Left against the
bare class, the layer would accept multiple leaders and report no improvement,
which is worse than not modelling them at all; see Q4.

Independently of the bound, the ledger advances by up to `m` slots per round
rather than one slot per three.

Two cautions to state in the report rather than prove:

The improvement is in *recurrence*, not *latency*. A given transaction still
waits three rounds from the block carrying it to the commit of a leader
referencing it. Pipelining shortens the wait for a leader, not the wait after
one.

The improvement is not free under attack. More slots means more slots left
undecided by the direct rules when leaders are slow or equivocating, and the
backpressure of §9.5 applies to all of them. The paper says as much (Section
III-C) and mitigates it by keeping `numOfProposers` small — 2, not `n`. The
model should be able to *express* that trade-off, which means P7's bound needs
to depend on `m`; it should not try to resolve it.

## 11. Staging and witnesses

Ordered so that nothing is proved twice and every stage builds. The obligations
are numbered **P0–P8** and each appears in exactly one stage.

1. **Generalise the class** (§3.1) and add `decisionRound`, `Eligible`,
   `lt_of_eligible` and the `Decidable` instance (§5). Do **not** touch
   `LeanDagTest` yet — see stage 2 for why.
2. **P0 — `Slots.uniform`** (§3.3), with `mono`/`unbounded`/`keyed` proved once
   generically, plus the conservativity pair
   `(uniform 3 1 …).slotRound k = 3 * k` and `eligible_of_lt` for it.
   Then rebuild the three existing instances — the anonymous one in
   `LeanDagTest/Model.lean`, the one in `LeanDagTest/Quantitative.lean`, and
   `fairSlots` in `LeanDagTest/Growth.lean`, each currently discharging
   `spacing _ := by omega` — through it. Note
   `LeanDagTest/Quantitative.lean:92` also *comments* on `Slots.spacing` and
   will need rewording. This ordering is not cosmetic: the old `spacing` field was a `∀ k`
   statement that `by omega` discharged instance-locally, whereas `unbounded`
   and `keyed` are existentials and injectivity statements that `omega` will
   not touch. Proving them once inside `uniform` means no instance ever faces
   them; doing stage 1 and stage 2 in the other order means writing them three
   times by hand and then deleting them.
3. **P1 — the engine** (§6.2). One line changes.
4. **Revise `Decided`** (§5). Exactly three proofs touch the indirect
   constructors, and it is worth having the list before starting, because two
   of them match positionally and will fail with an arity error rather than
   anything informative:
   - `decided_mono` **builds** them —
     `Decided.indirectCommit hkj ihj ihmid hL hcert` gains the `Eligible`
     argument and a re-typed `ihmid`.
   - `isLeaderBlock_of_decided` **destructures** them —
     `| indirectCommit _ _ _ hL _` gains an underscore.
   - `decided_unique` does both; it is stage 5.

   Everything else that mentions `Decided` uses only `directCommit` and
   `directSkip`, which are unchanged: `decided_none_of_leader_absent`,
   `decided_of_leader_mem`, and the one call in `Quantitative.lean`.
   `decided_full` goes through `decided_mono` and should not change.
5. **P2 — agreement** (§6.3). The claim is that only the two trichotomy cases
   change, and only by supplying `helig` to `hmid₂`. If that is right, this
   stage is short; it is the stage that validates the whole approach, so it
   should come before any liveness work. **If P2 fails, stop** — nothing after
   it is worth doing until the anchor rule is re-thought.
6. **P3 — schedule faithfulness** and the ledger check (§6.4, §8).
7. **P4, P5, P6** (§9.2–§9.4). Mechanical against `unbounded`.
8. **P7 — no undecided slot below a commit** (§9.5). Landed as the conditional
   L8, `decided_of_committed_above`, plus `all_decided_below_of_spacing`. The
   unconditional form is false; see §9.5 and Q1.
9. **P8 — `Schedule` and `Schedule.toSlots`** (§3.2). Last, and separable:
   nothing above needs it, since `uniform` covers every witness and every
   deployed schedule. Its value is generality — it is what turns "arbitrary
   validators per round" from a family of examples into a theorem. Budget for
   the index arithmetic (partial sums, `Nat.find`, the characterisation lemma)
   rather than for anything conceptual.

Stages 1–7 are believed routine; the risk is concentrated in stage 5 (which
validates the design) and stage 8 (which is open). *In the event stages 1–8 all
landed, stage 5 exactly as predicted and stage 8 by refuting its own statement —
see §14.*

**Witnesses.** `LeanDagTest/` should carry, at minimum:

- A **pipelined** instance, `Slots.uniform 1 1 rr`, with a concrete
  four-validator DAG in which slot `k` is directly committed while slots `k+1`
  and `k+2` are also committed — and a `decide`-checked demonstration that
  anchoring `k` on `k+1` would give the wrong answer. This is the
  counterexample that justifies `Eligible`, and it belongs in the development,
  not only in this document.
- A **multi-leader** instance, `Slots.uniform 1 2 rr`, with two co-round slots
  both committed, exercising §7.
- A **`nodup`-violating** schedule, to show the duplicate delivery of §8
  concretely. It cannot be a `Schedule`, which is the point; write the raw
  `slotRound`/`leader` pair and a computed `commitSeq` with a repeated element,
  and note which field of `Schedule` excludes it.
- The existing `+3` instance rebuilt as `Slots.uniform 3 1 rr`, so the
  generalisation is visibly conservative.
- An **irregular** schedule, once stage 9 lands: leaders at rounds 0, 1, 5, 6,
  6, 9 say, with `decide`-checked `slotRound` and `leader` values against
  `slotRound_eq_iff`. This is the witness that the general layer is usable and
  not merely definable.

Figure 4 of the paper is a ready-made witness for the first of these and its
example commit sequence (`L1a, L1c, L1d, L2a`) is a ready-made expected value.

**Where the edits land.** Every file the work touches, and nothing else:

| File | Change | Stage |
|---|---|---|
| `LeanDag/Mysticeti.lean` | `Slots` fields; delete `slotRound_add_three_le`; add `decisionRound`, `Eligible`, `lt_of_eligible`; re-premise `certifiedIn_of_directCommitIn`; revise `Decided`; fix `decided_unique` | 1, 3, 4, 5 |
| `LeanDag/Schedule.lean` *(new)* | `Slots.uniform` and its three field proofs; later `Schedule`, `toSlots`, `slotRound_eq_iff` | 2, 9 |
| `LeanDag/Liveness.lean` | drop `le_slotRound`; reprove `commits_recur_on`; add `exists_eligible`; P7 | 7, 8 |
| `LeanDag/Quantitative.lean` | reprove `commits_recur_within`; add the `uniform` bound beside `commits_recur_by_round` | 7 |
| `LeanDag.lean` | import the new module | 2 |
| `LeanDagTest/{Model,Quantitative,Growth}.lean` | instances rebuilt through `uniform` | 2 |
| `LeanDagTest/Pipelined.lean` *(new)* | the witnesses above | 2, 5, 6, 9 |
| `spec.md` | `Eligible`, `keyed`, and what the schedule layer assumes | as each lands |
| `report-outline.md` | §3.4 (the slot schedule), §3.5 (`Decided`), §6.10 (the bounds), §9 (drop or requalify the limitation) | last |

`LeanDag/{Block,BlockDag,CausalHistory,Support,Persistence,CommonCore,Timing}.lean`
are untouched — none of them mentions `Slots` (§4).

Two mechanical notes for whoever starts. `Slots` is a `class` with
`variable [S : Slots Validator]` and a scattering of `omit S in` on the
slot-free lemmas; adding fields changes neither. And the new `Eligible` needs
its `Decidable` instance declared explicitly, as `IsLeaderBlock`,
`DirectCommitIn` and `DirectSkipIn` all do, or the `decide`-checked witnesses
will not elaborate.

## 12. Open questions

**Q1. ~~Does P7 need a new hypothesis?~~ Should `SynchronisedOn` cover
Byzantine-authored blocks?** *Reformulated by §9.5.* The original question
presupposed that "every slot after `R` is decided" was true and only needed the
right induction. It is false under pipelining, and L8 isolates precisely the
hypothesis that fails. What remains open is whether that reflects a gap in the
model or in the protocol.

`SynchronisedOn U T R` covers only round-`n` blocks whose creator is in `T`,
which is weaker than the eventual DAG synchrony `liveness.md` opens with. The
candidate repair — a `T`-block references *some* round-`n` block by every author
that has one in `U` — is satisfiable where the naive "references every round-`n`
block" is not, because `ValidWrt.distinct_creators` forbids referencing two
blocks by one author. Under the repair an absent leader is still skipped and a
publishing leader is still committed, so the counterexample of §9.5 dies; but an
*equivocating* leader can still split correct validators between two candidates,
and closing that needs the paper's `SupportedBlock` traversal in place of
`L ∈ refs` — a change to the vote rule, not to the synchrony assumption.

So the decision is: strengthen synchrony and adopt DFS support (a real
extension, and the only route to an unconditional L8), or leave L8 conditional
and record that pipelining trades this guarantee away. Recommend the latter for
now — it is what the paper's own §III-C says — and treat the former as the next
piece of work.

**Q2. Should `Eligible` be `slotRound k + 3 ≤ slotRound j`, or
`+ waveLength`?** The paper parameterises `waveLength`, defaulting to 3, and
notes that a longer wavelength raises the chance of a certificate pattern under
asynchrony at the cost of latency. The whole development hard-codes 3 through
`certificates` (round `r+2`) and M2 (round `r+3`), so generalising the
wavelength is a much larger change than this one and should not be smuggled in.
*Deferred, not open, and §5 pays the one-line insurance premium*: `Eligible` is
stated as `decisionRound k < slotRound j`, so a later wavelength parameter is a
change to `decisionRound` and to `certificates`, not a search for the numeral
`3` across the development. Whoever generalises the wavelength should expect
M2's `r+3` to be the hard part, not this.

**Q3. ~~Is the linearisation of slots worth making explicit?~~** *Answered by
§3.2.* The question was whether to re-index slots as `ℕ × Fin m` in order to
make `keyed` a theorem rather than an assumption, at the cost of re-indexing
`commitSeq`, `ledgerSet`, `OutputAt` and all of `Liveness`. The schedule layer
gets the benefit without the cost: `Slots` keeps its `ℕ` index so no downstream
statement moves, and `keyed` becomes a theorem about `Schedule.nodup` one layer
up. What remains of the question is only *which* per-round container to use,
and that is settled — a `List`, because the within-round order is visible in
the ledger (§3.2).

**Q4. Does `numOfProposers` belong in the model?** It has to, if the
quantitative layer is to say anything true about multiple leaders: §10 shows
`BoundedSpacing` reports no improvement from them, because `s` stays at `1`
however many slots share a round. *Mostly answered by §3.3*: `Slots.uniform`
already carries `p` and `m`, and from the closed form `slotRound k = p * (k/m)`
the wanted bound

```lean
slotRound (k + w) ≤ slotRound k + p * ((w + m - 1) / m)
```

is a direct computation, needing no new field and no `BoundedSpacing`. So the
quantitative results should be restated against `uniform` rather than against
the bare class. What is *not* answered: whether the general `Schedule` of §3.2
deserves a quantitative treatment at all. An irregular schedule has no `m` to
quote, and the honest bound for it is in terms of `count`. Recommend leaving
the quantitative layer uniform-only and saying so, rather than weakening the
bounds to cover schedules nobody runs.

**Q5. What happens to the horizon?** `liveness.md` adopts a horizon `N` because
`Live` was unsatisfiable without one. The horizon is stated in rounds and is
unaffected as such; what changes is that `3m` times as many slots now sit below
it, and P7's statement (§9.5) needs `slotRound k + reach w ≤ N`, whose `reach`
is exactly the unknown of Q1. So Q5 is not independent — answering Q1 answers
it. Recorded separately only because the horizon is where the answer will be
felt.

## 13. Settled

**The commit pattern does not change.** Three rounds, `certificates` at `r+2`,
M2 tight at `r+3`. Pipelining overlaps waves; it does not shorten them (§1).

**Roles need no modelling work.** A block being a proposal, a vote and a
certificate at once is already expressible, because roles are reader-assigned
and `Block` records none of them (§1).

**The deployed rule anchors on eligible slots, not on the next slot.** Confirmed
against Algorithm 3, line 22: `anchors ← [s ∈ sequence s.t. r_decision <
s.round]` (§2). The present `k < j` premise is a proxy that happens to be
correct under `+3` spacing.

**Pipelining and multi-leader are one weakening.** `spacing` becomes `mono`;
five sites consume it, only two of them directly — `slotRound_add_three_le` and
`le_slotRound`, with the other three routing through those (§3, §4).

**M4 already takes its round hypothesis explicitly.**
`certifiedIn_of_directCommit` asks for `r + 3 ≤ (U.block A).round` and derives
nothing from the schedule, and the skip half asks for nothing at all. That is
why the repair is a premise change rather than a reproof: the safety core was
already written against the round separation, and only the *slot* layer above
it assumed the schedule would supply it (§6.1).

**`Eligible` must depend on `(k, j)` only.** This is what lets each validator's
eligibility premise discharge the other's intermediate premise in the agreement
induction. A view-relative eligibility would break M6 (§6.3).

**Restricting the intermediate quantifier is required, and safe.** Required
because slots `k+1`, `k+2` are routinely committed and waiting for them to be
skipped would deadlock; safe because the trichotomy argument only ever compares
eligible anchors (§5, §6.3).

**M5′ is indifferent to co-round slots.** It runs through
`ValidWrt.distinct_creators`, which is per-author, and so does the work the
paper's `SupportedBlock` traversal does (§7).

**The ledger layer is slot-order-generic** and needs `keyed` — and only
`keyed` — to stay faithful under multiple leaders (§8).

**A schedule is a per-round *sequence* of validators, not a set.** When a round
has several leaders their slots are committed in a definite order and that
order reaches the ledger, so `ℕ → List Validator` is the primitive and a
`Finset` would have to buy the order back with a `LinearOrder` on `Validator`
(§3.2).

**The schedule is a layer above `Slots`, not a replacement for it.** `Slots`
stays `ℕ`-indexed, so no downstream statement is re-indexed; `Schedule` sits
above it and `keyed`/`unbounded` become theorems about `nodup`/`cofinal`
(§3.2). This is what Q3 was asking for and it costs nothing.

**One constructor covers every deployed schedule.** `Slots.uniform p m` gives
`slotRound k = p * (k / m)`; `p = 3, m = 1` is the present development with
`spacing` recovered by `omega`, `p = 1` is pipelining, `m > 1` is multiple
leaders (§3.3). The general flattening is needed only for irregular schedules
and can come last.

**Commits recurring is not the ledger advancing.** L6 gives recurrence; the
ledger stops at the first undecided slot. L8 (`decided_of_committed_above`)
closes the gap, but only under the hypothesis that later slots may anchor
earlier ones (§9.5).

**Pipelining trades away "no undecided slot below a commit".** Under the old
spacing the nearest committed slot above any slot is an admissible anchor for
it, and the downward induction terminates. Under pipelining the slot below an
anchor must reach past it, and the dependency never bottoms out — so the
guarantee is genuinely lost, not merely harder to prove (§9.5). Safety is
untouched.

**`SynchronisedOn` does not constrain Byzantine-authored blocks.** It covers
round-`n` blocks whose creator is in `T` only, which is what lets the
counterexample of §9.5 exist. Whether that is a defect of the model or a
faithful account of the protocol is Q1 — the one genuinely open question left.

---

## 14. What implementation changed

P0–P6 are in. Recorded here rather than folded into the sections above, so
that the predictions of §§3–11 stay legible as predictions.

**Held as written.**

- **P2, the load-bearing claim (§6.3).** `decided_unique` needed exactly what
  §6.3 said: the extra `Eligible` argument threaded through eight constructor
  patterns, and `hmid₂ j hkj hlt` gaining a fourth argument discharged by the
  deciding validator's own eligibility premise. No counting was redone, and
  the fifteen easy pairings were untouched.
- **The affected-proof inventory (§11, stage 4).** `decided_mono`,
  `isLeaderBlock_of_decided` and `decided_unique`, and nothing else. The review
  pass that caught `isLeaderBlock_of_decided` earned its place: it fails with a
  bare arity error.
- **P1 (§6.2)** lost a line, as predicted; `certifiedIn_of_directCommit`
  already took `r + 3 ≤ round A` explicitly, so nothing beneath the slot layer
  moved.

**Two things the doc did not foresee.**

1. **`commits_recur_within`'s statement had to change, not just its proof.**
   §9.3 predicted only that its appeals to `le_slotRound` would go the way
   P4's did. But the statement itself quantified over `max k R` — mixing a
   slot index and a round index in one `max` — which is only meaningful when
   `slotRound R ≥ R`, exactly the coincidence `spacing` supplied. Under a
   monotone schedule the first slot at or after round `R` has to be *named*, so
   `Liveness.slotAt` was added (`Nat.find` on `unbounded`) and both
   `commits_recur_within` and `commits_recur_by_round` now read
   `max k (slotAt Validator R)`. Under the old schedule `slotAt R ≤ R`, so no
   bound weakened. Callers see a changed statement; `LeanDagTest/Quantitative`
   needed `slotAt_zero` to keep computing `3k + 8`.

2. **Stage ordering mattered more than §11 claimed, for a second reason.**
   §11 argued `uniform` must precede the test instances because `unbounded` and
   `keyed` resist `omega`. True, but the sharper point is that building
   instances through `uniform` puts `k / m` where a literal round used to be,
   so `rfl` proofs of `slotRound k = 3 * k` stop working — `k / 1` is not
   definitionally `k`. Three test lemmas moved from `rfl` to `simp`. Anyone
   adding a schedule should expect the same and reach for a `@[simp]` closed
   form immediately.

**Also landed.** `P3` came with `slot_eq_of_decided_commit`, the shape the
ledger actually wants: a committed block belongs to one slot. `LeanDagTest/`
gained `Pipelined.lean`, whose point is the two `decide`-checked facts that
justify the whole exercise — under `uniformSingle 1`, `¬ Eligible 0 1` and
`¬ Eligible 0 2`; under `uniform 1 2`, `¬ Eligible 0 1` for a *co-round* slot,
with slot `6` the first that qualifies. Both would have passed the old `k < j`
premise. The axiom audit covers all ten new or reproved results.

**The one prediction that was wrong, and it was the important one.** §9.5
originally proposed P7 — after `R`, every slot is decided — and treated the
difficulty as arithmetic: how much eligibility slack to add to the `w`-slot
walk. Working the induction revealed that no amount of slack suffices, because
the dependency does not terminate: the slot below any anchor needs a later
anchor, whose own lower neighbour needs a later one still. The statement is
false, and §9.5 now carries the counterexample.

What replaced it is better than what was asked for. `decided_of_committed_above`
(L8) needs no synchrony, no timing and no fairness — only one committed slot and
the hypothesis that later slots may anchor earlier ones. Isolating that
hypothesis is what makes the failure legible: it is precisely
`eligible_of_lt_of_spacing`, precisely what pipelining destroys, and
`Pipelined.lean` now witnesses both sides — `¬ (∀ a b, a < b → Eligible a b)`
under `uniformSingle 1`, and `a < b ↔ Eligible a b` under `uniformSingle 3`.

Had P7 been proved as originally stated, it would have been proved against a
synchrony assumption too weak to support it, and the gap would have been hidden
inside a true-looking theorem. The lesson for the remaining work is §12 Q1: the
next real step is not more anchor arithmetic but deciding whether
`SynchronisedOn` should cover Byzantine-authored blocks at all.

**The refutation is now checked, not argued.** L9 (`notMem_stuck_of_decided`)
turns the descent argument of §9.5 into structural induction on the `Decided`
derivation, and `stuck_empty_below_commit_of_spacing` composes it with L8 to
show that neither result is vacuous: a stuck set is impossible below a commit
under three-round spacing, and the arithmetic that makes one possible under
pipelining is witnessed in `Pipelined.lean`. Both compiled first try, which is
some evidence the hand argument was right rather than lucky.

What remains unformalised is narrower than before and worth stating precisely:
L9 assumes `hcert` and `hskip`, and no concrete universe satisfying them is
built. That is a `U7`-sized model in which a Byzantine leader's candidate
gathers exactly `2f` votes and `2f` blames, and it is the last step between "the
descent argument is valid" and "the counterexample exists".
