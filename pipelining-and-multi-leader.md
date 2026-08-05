# lean-dag — Pipelining and multiple leaders

Design notes for extending the safety and liveness results from the
single-leader, three-round-spaced commit rule now in `spec.md` and
`liveness.md` to the **pipelined, multi-leader** Mysticeti-C rule actually
deployed. Things graduate into `spec.md` once they settle.

> **Status.** Nothing here is implemented. §5–§8 are the safety half; the
> argument is worked out on paper and the claim is that the existing proofs
> survive a *premise* change with no new counting. §9–§10 are the liveness
> half, which is where the genuinely new theorem lives (P7). §12 lists what
> has to be decided first, §13 what is already settled.

**The thesis in one paragraph.** The development is already parametric in the
leader schedule: `Slots` is a class, and every safety theorem takes it as an
instance. Pipelining and multiple leaders per round are, between them, exactly
one weakening of one field of that class — `spacing : ∀ k, slotRound k + 3 ≤
slotRound (k+1)` becomes `Monotone slotRound`. Everything that breaks, breaks
because it consumed that field. There are five such places, and four of them
are one lemma. The repair is to stop *deriving* the three-round separation
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
not.

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
*above*, is untouched and becomes more useful, not less: under pipelining it
holds with `s = 1` and under multiple leaders with `s = 0`.

Nothing in `Block`, `BlockDag`, `CausalHistory`, `Support`, `Persistence`,
`CommonCore` or `Timing` mentions `Slots` at all.

## 5. The repair: eligible anchors

```lean
/-- `j` may anchor `k`: later, and far enough ahead that a block at `j`'s
round can reach a certificate for `k`'s. -/
def Eligible (k j : ℕ) : Prop := S.slotRound k + 3 ≤ S.slotRound j
```

Under `mono`, `Eligible k j → k < j`, so the separate `k < j` premise becomes
redundant; it is worth keeping in the constructors anyway, because it is what
the induction in `decided_unique` recurses on and Lean will want it
syntactically. Also under `mono` the eligible slots above `k` are
**upward-closed**: there is a first one, and the intermediate premise below
says "every slot from that one up to the anchor was skipped".

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
and never mention `Slots`. `directCommit_of_directCommitIn`,
`directSkip_of_directSkipIn`, `certifiedIn_iff_of_view`,
`not_directSkipIn_of_directCommitIn`, `eq_of_directCommitIn`,
`not_certifiedIn_of_directSkipIn`, `certificates_nonempty_of_*` and
`eq_of_hasCertificate` likewise. Expect these to compile against the new class
untouched.

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

`commits_recur_within` combines `FairWithin T w` with `BoundedSpacing s`. Both
survive; only the arithmetic changes, and it changes in the right direction
(§10).

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

### 9.5 P7 — every slot is eventually decided

**This is the real liveness work, and it is not specific to pipelining — it is
simply invisible today.** The development proves that commits *recur*
(`commits_recur_on`), not that every slot is *decided*. Yet the ledger is the
sequence read off in slot order up to the first undecided slot: one permanently
undecided slot stalls delivery of everything above it, however many commits
recur beyond. The paper is explicit that this is the design ("Mysticeti-C
applies some backpressure through undecided slots, to preserve safety").

Under `+3` spacing this gap is easy to overlook, because slots are scarce.
Under pipelining there are three times as many slots per round, and with `m`
leaders, `3m` times as many — so `3m` times as many opportunities for a slot
with a Byzantine or partitioned leader to sit undecided. The obligation should
be discharged now rather than inherited.

The statement to aim for, after the synchrony round `R`:

```
for every slot k with slotRound k ≥ R, ∃ v, Decided U (View.full U) k v
```

The shape of the argument: take the least slot `j > k` whose leader lies in
`T`; L4 directly commits it, and by `FairWithin` it is at most `w` slots away.
Every slot strictly between `k` and `j` has a leader outside `T`; each is
either directly skipped (L5, when the leader published nothing anyone
referenced) or must itself be resolved indirectly against `j`. So the induction
runs *downward* from `j`, is bounded by `w`, and needs at each step that the
eligible intermediates below `j` are already decided — which the downward
order supplies. The awkward case is the leader that is neither absent nor
timely: it publishes to some correct validators and not enough, so neither the
direct commit nor the direct skip fires. That slot is decided only by the
indirect rule, and only once `j` is committed — which is exactly what the
induction gives, provided `j` is eligible for it. Since `j` may be as close as
one round above such a slot under pipelining, **the induction must skip over
ineligible slots and pick a further anchor**, and the bound is therefore `w`
slots *plus* the eligibility slack, not `w`. Getting that arithmetic right is
the substance of P7.

I do not claim this is routine. It is the one item here that could turn out to
need a hypothesis the model does not currently have — see §12.

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

What is wanted is `slotRound (k + w) ≤ slotRound k + ⌈w/m⌉`, which needs the
schedule to expose `m`. That is Q4, and §10 is the reason to answer it: without
`perRound`, the quantitative layer will accept multiple leaders and report no
improvement, which is worse than not modelling them. With it, the walk cost
becomes `⌈w/m⌉` and the headline falls from `3(f+1)` to `⌈(f+1)/m⌉`.

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

Ordered so that nothing is proved twice and every stage builds.

1. **Generalise the class** (§3) and add `Eligible`. Keep `slotRound k = 3k`
   as an instance and check that `LeanDagTest/Model.lean` and
   `LeanDagTest/Quantitative.lean` still discharge their `Slots` instances,
   now via `mono`, `unbounded`, `keyed` instead of `spacing`. Nothing should
   break; if something does, it is unlisted in §4 and worth knowing.
2. **P1**, the engine (§6.2). One line changes.
3. **Revise `Decided`** (§5). The fallout is smaller than it looks: the only
   proof that rebuilds the constructors is `decided_mono`, and only its two
   indirect cases, which currently read
   `Decided.indirectCommit hkj ihj ihmid hL hcert` and will take the extra
   `Eligible` argument and a re-typed `ihmid`. `decided_full` goes through
   `decided_mono` and should not change. `decided_unique` is stage 4.
4. **P2**, agreement (§6.3). The claim is that only the two trichotomy cases
   change, and only by supplying `helig` to `hmid₂`. If that is right, this
   stage is short; it is the stage that validates the whole approach, so it
   should come before any liveness work.
5. **P3** and the ledger check (§6.4, §8).
6. **P4, P5, P6** (§9.2–§9.4). Mechanical against `unbounded`.
7. **P7** (§9.5). The open one.

**Witnesses.** `LeanDagTest/` should carry, at minimum:

- A **pipelined** instance, `slotRound k = k`, `leader` round-robin, with a
  concrete four-validator DAG in which slot `k` is directly committed while
  slots `k+1` and `k+2` are also committed — and a `decide`-checked
  demonstration that anchoring `k` on `k+1` would give the wrong answer. This
  is the counterexample that justifies `Eligible`, and it belongs in the
  development, not only in this document.
- A **multi-leader** instance, `slotRound k = k / m`, `leader k = k % m`, with
  two co-round slots both committed, exercising §7.
- A **`keyed`-violating** schedule, to show the duplicate delivery of §8
  concretely. It need not be an instance of the class; a raw schedule plus a
  computed `commitSeq` with a repeated element is enough.
- The existing `+3` instance, unchanged, so the generalisation is visibly
  conservative.

Figure 4 of the paper is a ready-made witness for the first of these and its
example commit sequence (`L1a, L1c, L1d, L2a`) is a ready-made expected value.

## 12. Open questions

**Q1. Does P7 need a new hypothesis?** The downward induction of §9.5 needs the
anchor `j` to be eligible for every undecided slot below it that it is meant to
resolve. Slots within two rounds below `j` are not eligible for it and need a
*later* anchor — which needs its own leader in `T`. Under `FairWithin T w` the
next such is at most `w` slots on, so the recursion terminates; but the bound
is not simply `w`, and it is not yet clear whether it closes without assuming
something like "two reliable leaders occur within `w` slots" or a lower bound
on the slot spacing. Settle this on paper before writing Lean.

**Q2. Should `Eligible` be `slotRound k + 3 ≤ slotRound j`, or
`+ waveLength`?** The paper parameterises `waveLength`, defaulting to 3, and
notes that a longer wavelength raises the chance of a certificate pattern under
asynchrony at the cost of latency. The whole development hard-codes 3 through
`certificates` (round `r+2`) and M2 (round `r+3`). Generalising the wavelength
is a much larger change than this one and should not be smuggled in; but
`Eligible` should be *stated* so that it reads as "past the decision round",
not as a bare numeral, so the later generalisation is a definition change and
not a search-and-replace.

**Q3. Is the linearisation of slots worth making explicit?** §3 keeps slots as
`ℕ` and lets `slotRound`/`leader` encode the (round, offset) structure. That is
minimal and keeps every ledger theorem. The alternative — slots as
`ℕ × Fin m` with a lexicographic order — is more faithful to the protocol and
would make `keyed` a theorem rather than an assumption, at the cost of
re-indexing `commitSeq`, `ledgerSet`, `OutputAt` and the whole of `Liveness`.
Recommend the minimal encoding, and record `keyed` as the price.

**Q4. Does `numOfProposers` belong in the model?** It has to, if the
quantitative layer is to say anything true about multiple leaders: §10 shows
`BoundedSpacing` reports no improvement from them, because `s` stays at `1`
however many slots share a round. The minimal fix is a field `perRound : ℕ`
with `slotRound (k + perRound) = slotRound k + 1`, consumed by nothing outside
`Quantitative.lean`, plus the lemma `slotRound (k + w) ≤ slotRound k +
(w + perRound - 1) / perRound` to replace `slotRound_le_of_boundedSpacing` at
the one call site. Note this is an *equation*, so it constrains the schedule to
a uniform number of leaders per round; a schedule with a varying count would
need an inequality and a weaker conclusion. Uniform is what deployments do and
is enough.

**Q5. What happens to the horizon?** `liveness.md` adopts a horizon `N` because
`Live` was unsatisfiable without one. The horizon is stated in rounds and the
new slot count per round is `m` times larger; nothing obviously breaks, but the
interaction of the horizon with P7's downward induction has not been checked.

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
five sites consume the old field, four of them in one lemma (§3, §4).

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
