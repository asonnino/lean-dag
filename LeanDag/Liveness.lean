import LeanDag.Mysticeti

/-!
# Liveness — results needing no new primitives

`liveness.md` §6, results **L0**–**L3**.

L0, L2 and L3 assume neither `Live` nor `Synchronised`, which is why they come
first: L0 is pure DAG structure, L2 and L3 are pure view reasoning. Every
modelling decision is deferred until something is already proved. **L1** is
the first result to need a new primitive.

- **L0** — the DAG is dense below its frontier. Validity alone; nothing here
  even mentions correctness. The content is not that the DAG grows but that
  it **cannot grow tall and thin**.
- **L2** — decisions are monotone in the view. A validator never *revises* a
  decision as its view grows.
- **L3** — commit propagation. L2 at the full view, which §4.2 identifies as
  every correct validator's eventual view.
- **L1** — no stall. The first result needing `Live`, and still needing no
  synchrony.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {N : ℕ}

omit [DecidableEq BlockId] in
/-- A round with any author at all has a block. The bridge that lets L0's
induction step back down: a cardinality bound on `authorsAt` is turned into
a witness block, which the next step then references from. -/
theorem exists_mem_of_authorsAt_card_pos {n : ℕ} (h : 0 < (authorsAt U n).card) :
    ∃ i ∈ U.ids, (U.block i).round = n := by
  obtain ⟨v, hv⟩ := Finset.card_pos.mp h
  obtain ⟨i, hi, hir, _⟩ := mem_authorsAt.mp hv
  exact ⟨i, hi, hir⟩

omit [DecidableEq BlockId] in
/-- One step of L0: a block at round `n+1` forces a quorum of authors at
round `n`.

Immediate from validity — the block's references carry `2f+1` distinct
creators, and every one of them holds a round-`n` block. -/
theorem card_authorsAt_of_succ {n : ℕ} {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = n + 1) :
    2 * F.f + 1 ≤ (authorsAt U n).card :=
  le_trans (U.creators_quorum hi (by omega))
    (Finset.card_le_card (creators_refs_subset_authorsAt hi hir))

omit [DecidableEq BlockId] in
/-- **L0 — the DAG is dense below its frontier.** If any block exists at
round `r`, then *every* round `n < r` has at least `2f+1` distinct authors.

Downward induction on the gap `r - n`. The step is where the two lemmas
above meet: the inductive hypothesis gives a quorum of authors one round
higher, that quorum is nonempty so some block sits there, and
`card_authorsAt_of_succ` walks it down one more round.

The induction runs on the gap rather than on `r` itself because the
statement is not about `r`: nothing distinguishes the block's own round, and
generalising over `n` is what lets the step re-enter at `n+1`. -/
theorem card_authorsAt_of_lt {r n : ℕ} (hn : n < r) {i : BlockId}
    (hi : i ∈ U.ids) (hir : (U.block i).round = r) :
    2 * F.f + 1 ≤ (authorsAt U n).card := by
  obtain ⟨d, rfl⟩ : ∃ d, r = n + 1 + d := ⟨r - n - 1, by omega⟩
  clear hn
  induction d generalizing n i with
  | zero => exact card_authorsAt_of_succ hi hir
  | succ d ih =>
      have h1 : 2 * F.f + 1 ≤ (authorsAt U (n + 1)).card :=
        ih (n := n + 1) (i := i) hi (by omega)
      obtain ⟨j, hj, hjr⟩ := exists_mem_of_authorsAt_card_pos (U := U) (n := n + 1)
        (by omega)
      exact card_authorsAt_of_succ hj hjr

/-! ## L1 — no stall

`liveness.md` §3(a), §4.4, §6. The first result here to need a primitive the
static model lacks.

`Correct` means only *does not equivocate* — a purely negative condition,
satisfied by a validator that crashes at round 0 and never speaks again. That
is deliberate: it is what lets every safety result hold for crashed
validators too. But it makes every liveness statement vacuous without a
positive rule, so `Live` supplies one.

**`Live` is an explicit argument, not a class.** `Faults` is a class because
it is *universal* — every theorem in the development carries it, so hiding it
costs nothing. `Live` is not: L0, L2 and L3 do without it and L1 does not.
When an assumption separates the unconditional results from the conditional
ones, hiding it is exactly backwards. For the same reason it is a structure
of its own rather than extra fields on `Faults`: folding it in would give
every safety theorem a liveness hypothesis it does not use, and `Faults`
cannot mention a `BlockUniverse` anyway, since `BlockUniverse`'s own type
requires `Faults`.
-/

omit [DecidableEq BlockId] in
/-- What L4 actually needs of a round: every validator in `T` has a block
there.

Local and finite — no growth, no horizon. Splitting this out is what keeps
the horizon `N` out of L4 entirely, so the only hard proof in the plan is
independent of how `Live` is framed.

**Why a set `T` rather than all of `Correct`.** L4 counts to `2f+1` and never
higher, so it needs a *quorum* of reliable validators, not every one of them.
Demanding all of `Correct` makes the theorem lapse when a single correct
validator misses a single round — a GC pause, a restart — although the
protocol still commits. See `liveness.md` §8 Q2. -/
def PopulatedOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (r : ℕ) : Prop :=
  ∀ v ∈ T, ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r

/-- The all-of-`Correct` case, which is what L1 produces. -/
abbrev Populated (U : BlockUniverse Validator BlockId Payload) (r : ℕ) : Prop :=
  PopulatedOn U (Correct : Finset Validator) r

omit [DecidableEq BlockId] in
/-- Population is **antitone**: a smaller set is easier to populate. This is
what lets L1 keep concluding about all of `Correct` while L4 consumes only a
quorum. -/
theorem PopulatedOn.mono {T T' : Finset Validator} {r : ℕ} (hsub : T ⊆ T')
    (h : PopulatedOn U T' r) : PopulatedOn U T r :=
  fun v hv => h v (hsub hv)

/-! ## The delivery layer

`liveness.md` §8 questions 2 and 8. The model as first written could not say
what a validator *held* — only blocks and refs — so two different things had
to be stated on `refs` and hoped to coincide:

- `builds` said a correct validator builds once *any* quorum has round-`r`
  blocks. But a validator cannot act on blocks it has not received; the real
  rule is a **timeout plus a quorum in its own view**.
- `Synchronised` said correct blocks reference correct blocks, welding a
  protocol rule to a network guarantee.

`held` fixes both. Note what it does **not** contain: a clock. The timeout is
what decides how much lands in `held` beyond the `2f+1` minimum, and having no
time model, that is the only trace it can leave. `builds` therefore asks only
that a quorum be *in view*; waiting longer than that shows up as a larger
`held`, which is what `EventuallyDelivers` then demands after `R`. -/

/-- What each validator had in hand, one round at a time. -/
structure Delivery (U : BlockUniverse Validator BlockId Payload) where
  /-- What `v` held from round `n` when it built its round-`(n+1)` block. -/
  held : Validator → ℕ → Finset BlockId
  /-- Held ids are real blocks of the stated round. Not used by
  `synchronised_of_delivery` below — it is what keeps `Delivery` meaningful,
  since without it `held` could be junk and `includes` would demand blocks
  reference it. -/
  held_spec : ∀ v n, ∀ i ∈ held v n, i ∈ U.ids ∧ (U.block i).round = n
  /-- **The protocol rule.** A correct validator references everything it
  held. Implementable and observable — unlike `Synchronised` itself. -/
  includes : ∀ v ∈ (Correct : Finset Validator), ∀ n, ∀ b ∈ U.ids,
    (U.block b).creator = v → (U.block b).round = n + 1 →
    held v n ⊆ (U.block b).refs

/-- **Asynchrony.** A quorum that exists is eventually held. Stated
conditionally — existence first, holding second — because unconditionally it
would assert the very block production L1 sets out to prove.

No round bound: this is what holds *before* GST too, and it is all L1 needs.
Contrast `EventuallyDelivers`, which demands the *whole* correct round and
only from `R`. -/
def DeliversQuorum (D : Delivery U) : Prop :=
  ∀ n, 2 * F.f + 1 ≤ (authorsAt U n).card →
    ∀ v ∈ (Correct : Finset Validator),
      2 * F.f + 1 ≤ (creatorsOf U.block (D.held v n)).card

/-- The positive protocol behaviour liveness needs. Not derivable from the
DAG structure — `Correct` is a negative condition and these are positive.

**Asynchrony-only.** `builds` asks that a correct validator has a block at
round `r+1` once *some* quorum holds round-`r` blocks; it says nothing about
timing, delivery, or whose blocks are referenced. That is what lets L1 hold
from round 0 with no synchrony at all.

`N` is the **horizon**, and it is not decoration. `U.ids` is a `Finset`, so
without the bound `r < N` these two fields force infinitely many distinct
blocks into a finite set and *no universe satisfies them* — see
`LeanDagTest.Growth`, where the witness is built, and `liveness.md` §4.4,
where the vacuous first draft is recorded.

Note `N` is a **demand** on the DAG, not a bound on it: `Live U N` requires
blocks to exist all the way to round `N`, so a larger `N` is a *stronger*
hypothesis satisfied by *fewer* universes. Coverage of every DAG comes from
quantifying over `N`, never from choosing it large. -/
structure Live (U : BlockUniverse Validator BlockId Payload)
    (D : Delivery U) (N : ℕ) : Prop where
  /-- Every correct validator has a genesis block. -/
  genesis : Populated U 0
  /-- Below the horizon, a correct validator that **holds** a quorum of
  round-`r` blocks has one of its own at `r+1`.

  The quorum is measured against `D.held v r`, not against `authorsAt U r`:
  a validator cannot build on blocks it has not received. -/
  builds : ∀ r < N, ∀ v ∈ (Correct : Finset Validator),
    2 * F.f + 1 ≤ (creatorsOf U.block (D.held v r)).card →
    ∃ b ∈ U.ids, (U.block b).creator = v ∧ (U.block b).round = r + 1

omit [DecidableEq BlockId] in
/-- A populated round carries a quorum of authors — the step that feeds L1's
induction back into `builds`, and the only place `card_correct` is used.

`spec.md` §2 has carried `card_correct` as unused-but-kept-for-liveness since
the system model was written. This is what it was kept for. -/
theorem card_authorsAt_of_populated {r : ℕ} (h : Populated U r) :
    2 * F.f + 1 ≤ (authorsAt U r).card := by
  refine le_trans card_correct (Finset.card_le_card ?_)
  intro w hw
  obtain ⟨b, hb, hbc, hbr⟩ := h w hw
  exact mem_authorsAt.mpr ⟨b, hb, hbr, hbc⟩

omit [DecidableEq BlockId] in
/-- **L1 — no stall.** Under `Live U D N` and `DeliversQuorum D`, every
correct validator has a block
at every round up to the horizon.

Induction on the round. The base is `genesis`. The step goes in two hops now
that `builds` is view-relative: the induction hypothesis makes `Correct` a
subset of `authorsAt U r`, so a quorum *exists*; `DeliversQuorum` turns that
into each correct validator *holding* a quorum; and only then does `builds`
apply.

That second hop is the content of question 2. Without it the theorem would be
claiming validators build on blocks they may never have received.

L1 is the **only** result where the horizon does real work. Its whole job is
to turn the growth assumption into the local `Populated` facts L4 consumes —
which is why L4 itself never mentions `N` (`liveness.md` §4.4). -/
theorem no_stall {D : Delivery U} (H : Live U D N) (hd : DeliversQuorum D) :
    ∀ r ≤ N, Populated U r := by
  intro r
  induction r with
  | zero => intro _; exact H.genesis
  | succ r ih =>
      intro hr v hv
      exact H.builds r (by omega) v hv
        (hd r (card_authorsAt_of_populated (ih (by omega))) v hv)

omit [DecidableEq BlockId] in
/-- L1 in the form L0 consumes: under `Live U D N` **every** round up to the
horizon carries a quorum of authors, not merely every round below some
frontier. -/
theorem card_authorsAt_of_live {D : Delivery U} (H : Live U D N)
    (hd : DeliversQuorum D) {r : ℕ} (hr : r ≤ N) :
    2 * F.f + 1 ≤ (authorsAt U r).card :=
  card_authorsAt_of_populated (no_stall H hd r hr)

omit [DecidableEq BlockId] in
/-- From round `R` on, a correct block references every correct block of the
round below.

`R` is **not** GST: it is the round from which synchrony has fully taken
effect — GST plus however long catch-up ran (`liveness.md` §4.2). It is a
round index, not a clock; there is no Δ here.

**Both quantifiers are restricted to `Correct`, and deliberately.** A
Byzantine validator may publish nothing at all, or publish and reveal to only
some validators, so no assumption about referencing its blocks would be
sound — and none is needed: L4 counts only correct certificates, and there
are `2f+1` correct validators. Getting this wrong in the *strong* direction,
by demanding that all blocks be referenced, would assume Byzantine validators
behave.

**This does not follow from view convergence.** A block's references are
frozen when it is built: a correct validator waits for `2f+1` round-`n`
blocks, and the arrival of the `2f+1`st says nothing about the rest having
arrived. Views converging later does not retroactively enlarge blocks. So
this is an assumption, not a theorem — see `liveness.md` §4.3, and §8
question 8 for how it is meant to be split and derived. -/
def SynchronisedOn (U : BlockUniverse Validator BlockId Payload)
    (T : Finset Validator) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ T →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ T → a ∈ (U.block b).refs

/-- The all-of-`Correct` case. -/
abbrev Synchronised (U : BlockUniverse Validator BlockId Payload) (R : ℕ) : Prop :=
  SynchronisedOn U (Correct : Finset Validator) R

omit [DecidableEq BlockId] in
/-- Coverage is **antitone** too: mutual coverage among a larger set implies
it among any subset. So existing witnesses of `Synchronised` feed the
quorum-relative L4 unchanged. -/
theorem SynchronisedOn.mono {T T' : Finset Validator} {R : ℕ} (hsub : T ⊆ T')
    (h : SynchronisedOn U T' R) : SynchronisedOn U T R :=
  fun n hn b hb hbr hbc a ha har hac => h n hn b hb hbr (hsub hbc) a ha har (hsub hac)

/-! ## L7 — `Synchronised`, derived

`liveness.md` §8 question 8. `Synchronised` welds two unlike things into one
object: a protocol rule and a network guarantee. It cannot be derived from
anything the static model has, because the model is blocks and refs — no
time, no delivery, no record of what a validator *held* when it built.
`Synchronised` is stated on `refs` because `refs` is all there is.

Adding that missing layer splits it. **The gain is not logical** — one
assumption becomes two and nothing turns unconditional, since with no time
model the chain must bottom out at delivery. The gain is that each piece is a
single kind of thing: `includes` is implementable and observable, which is
exactly what §3(b) notes `Synchronised` fails to be, and `EventuallyDelivers`
is pure network.

It also puts the timeout story somewhere real. A timeout governs *when you
build*, i.e. what lands in `held`; it has nothing to do with `refs`, which
§4.3 had to discuss next to a definition structurally unable to express it. -/

/-- **The network assumption**: after `R`, correct blocks reach correct
validators in time to be built on. This is eventual DAG synchrony proper —
pure delivery, no protocol content. -/
def EventuallyDelivers (D : Delivery U) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ v ∈ (Correct : Finset Validator), ∀ a ∈ U.ids,
    (U.block a).round = n → (U.block a).creator ∈ (Correct : Finset Validator) →
    a ∈ D.held v n

omit [DecidableEq BlockId] in
/-- **L7.** `Synchronised` is a theorem, not an assumption: `refs ⊇ held ⊇`
every correct block below.

L4–L6 are untouched — they still take `Synchronised`, which this now supplies
a second way. -/
theorem synchronised_of_delivery (D : Delivery U) (h : EventuallyDelivers D R) :
    Synchronised U R := fun n hn b hb hbr hbc a ha har hac =>
  D.includes _ hbc n b hb rfl hbr (h n hn _ hbc a ha har hac)

/-! ## L2 — decisions are monotone in the view

`liveness.md` §6. If `V ⊆ V'` then every verdict `V` reaches, `V'` reaches
too. Combined with M1 this says a validator **never revises a decision** as
its view grows: the safety results say decisions do not *conflict*, not that
they do not *change*.

**This works only because `CertifiedIn` is universe-level.** The
`indirectSkip` case carries a negative premise — no candidate is certified in
reach of the anchor. Were the indirect check view-relative, that premise
would be *anti*-monotone: growing the view could reveal a certificate and
flip a skip into a commit. C1 defined `CertifiedIn` over `U`, with T6a
showing the view-restricted computation agrees, and that is what keeps the
premise stable under growth. Both indirect cases pass their certificate
premise through untouched below — that is the whole content of the remark.
-/

variable [S : Slots Validator]

omit S in
/-- A larger view can only see more certificates. -/
theorem directCommitIn_mono {V V' : View Validator BlockId Payload U}
    (hsub : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ} (h : DirectCommitIn U V L r) :
    DirectCommitIn U V' L r :=
  le_trans h (Finset.card_le_card (Finset.image_subset_image
    (Finset.inter_subset_inter Finset.Subset.rfl hsub)))

omit S in
/-- A larger view can only see more blame. -/
theorem directSkipIn_mono {V V' : View Validator BlockId Payload U}
    (hsub : V.ids ⊆ V'.ids) {L : BlockId} {r : ℕ} (h : DirectSkipIn U V L r) :
    DirectSkipIn U V' L r :=
  le_trans h (Finset.card_le_card (Finset.image_subset_image
    (Finset.inter_subset_inter Finset.Subset.rfl hsub)))

/-- **L2 — decisions are monotone in the view.** If `V ⊆ V'` then
`Decided U V k v → Decided U V' k v`.

Induction on the derivation. The two direct cases are the monotonicity
lemmas above; the two indirect cases rebuild themselves from the inductive
hypotheses, carrying their `CertifiedIn` premises across unchanged. -/
theorem decided_mono {V V' : View Validator BlockId Payload U}
    (hsub : V.ids ⊆ V'.ids) {k : ℕ} {v : Option BlockId} (h : Decided U V k v) :
    Decided U V' k v := by
  induction h with
  | directCommit hL hdc => exact Decided.directCommit hL (directCommitIn_mono hsub hdc)
  | directSkip hall => exact Decided.directSkip fun L hL => directSkipIn_mono hsub (hall L hL)
  | indirectCommit hkj helig _ _ hL hcert ihj ihmid =>
      exact Decided.indirectCommit hkj helig ihj ihmid hL hcert
  | indirectSkip hkj helig _ _ hnc ihj ihmid =>
      exact Decided.indirectSkip hkj helig ihj ihmid hnc

/-! ## L3 — commit propagation

`liveness.md` §4.2, §6. Eventual DAG synchrony says anything one correct
validator holds, all eventually hold — so the union of the correct
validators' views *is* `U`, and every correct validator's eventual view is
the **full** view.

That is what turns "all correct validators eventually agree" from an appeal
into a theorem: the informal *eventually* is discharged by the framing, and
what remains is L2 instantiated. It also fixes what `U` means — not every
block anyone ever wrote, but every block some correct validator ever held. A
Byzantine block revealed to nobody is simply not in the universe. -/

omit [DecidableEq BlockId] in
/-- Every correct validator's *eventual* view. Downward-closed for free, by
`U.complete`. -/
def View.full (U : BlockUniverse Validator BlockId Payload) :
    View Validator BlockId Payload U where
  ids := U.ids
  subset_ids := Finset.Subset.rfl
  complete := U.complete

/-- **L3 — commit propagation.** Whatever any validator decides on any view,
the same verdict holds on the full view.

Since the full view is every correct validator's eventual view (§4.2), this
*is* "all correct validators eventually reach the same decision". -/
theorem decided_full {V : View Validator BlockId Payload U} {k : ℕ}
    {v : Option BlockId} (h : Decided U V k v) : Decided U (View.full U) k v :=
  decided_mono V.subset_ids h

/-! ## L4 — a correct leader commits

`liveness.md` §6. The one substantive proof in the liveness plan.

**Two layers of coverage, and nothing else.** Every correct round-`(r+1)`
block references `L`, because `L` is correct-authored and honest-to-honest
coverage applies. Every correct round-`(r+2)` block then references all of
*those*, so its votes for `L` come from every correct validator — a quorum —
and it certifies. Since there are `2f+1` correct validators, the certificates
themselves come from a quorum, which is `DirectCommit`.

**Only correct-to-correct coverage is used.** The argument never asks whether
a Byzantine block was produced or seen. That is what lets `Synchronised` stay
restricted to correct authors on both sides — an unavoidable restriction,
since a Byzantine validator may publish nothing, or publish and withhold
(§4.3).

**No horizon, no growth, no limit universe.** The hypotheses are three local
`Populated` facts. L1 supplies them from `Live U N` when `r + 2 ≤ N`, but L4
does not care where they come from — which is exactly why the horizon
question of §4.4 could be settled without touching this proof. -/

variable {L C : BlockId} {R r : ℕ} {k : ℕ} {T : Finset Validator}

omit S in
/-- A correct round-`(r+2)` block certifies any correct round-`r` block, once
round `r+1` is populated and synchrony has taken hold.

This is both layers at once: `q` references `L` by coverage at `n = r`, and
`C` references `q` by coverage at `n = r+1`. -/
theorem certifies_of_synchronisedOn (hcard : 2 * F.f + 1 ≤ T.card)
    (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hpop1 : PopulatedOn U T (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T)
    (hC : C ∈ U.ids) (hCr : (U.block C).round = r + 2)
    (hCc : (U.block C).creator ∈ T) :
    Certifies U C L := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq, hqc, hqr⟩ := hpop1 v hv
  have hqcorrect : (U.block q).creator ∈ T := by rw [hqc]; exact hv
  rw [mem_creatorsOf]
  refine ⟨q, ?_, hqc⟩
  rw [votesIn, Finset.mem_filter]
  exact ⟨hs (r + 1) (by omega) C hC (by omega) hCc q hq hqr hqcorrect,
         hs r hRr q hq hqr hqcorrect L hL hLr hLc⟩

omit S in
/-- **L4, at the round level.** A correct block at round `r` is directly
committed, given coverage from `r` and correct blocks at `r+1` and `r+2`.

Stated without `Slots`: nothing in the argument cares that `L` is a leader
block, only that it is correct-authored — the same separation Stage A makes
for M1–M3. -/
theorem directCommit_of_synchronisedOn (hcard : 2 * F.f + 1 ≤ T.card)
    (hs : SynchronisedOn U T R) (hRr : R ≤ r)
    (hpop1 : PopulatedOn U T (r + 1)) (hpop2 : PopulatedOn U T (r + 2))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r) (hLc : (U.block L).creator ∈ T) :
    DirectCommit U L r := by
  refine le_trans hcard (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨C, hC, hCc, hCr⟩ := hpop2 v hv
  have hCcorrect : (U.block C).creator ∈ T := by rw [hCc]; exact hv
  rw [mem_creatorsOf]
  exact ⟨C, mem_certificates.mpr ⟨hC, hCr,
    certifies_of_synchronisedOn hcard hs hRr hpop1 hL hLr hLc hC hCr hCcorrect⟩, hCc⟩

omit [DecidableEq BlockId] in
/-- A correct leader has a candidate block, once its round is populated.
`Populated` at the leader's own round is needed for nothing else. -/
theorem exists_isLeaderBlock (hpop : PopulatedOn U T (S.slotRound k))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop (S.leader k) hlead
  exact ⟨L, hL, hLr, hLc⟩

/-- **L4.** A slot with a correct leader, whose three rounds are populated and
which sits after synchrony, is directly committed. -/
theorem directCommit_of_leader_mem (hcard : 2 * F.f + 1 ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) := by
  obtain ⟨L, hL, hLr, hLc⟩ := exists_isLeaderBlock hpop0 hlead
  exact ⟨L, ⟨hL, hLr, hLc⟩,
    directCommit_of_synchronisedOn hcard hs hR hpop1 hpop2 hL hLr
      (by rw [hLc]; exact hlead)⟩

/-- **L4 at `T := Correct`.** The original statement, recovered. -/
theorem directCommit_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) :=
  directCommit_of_leader_mem card_correct hs hR hpop0 hpop1 hpop2 hlead

/-! ### From `DirectCommit` to an actual decision

L4 concludes the universe-level rule; the ledger is defined over `Decided`.
The full view closes the gap, since it holds every certificate there is. -/

omit S in
theorem certificatesIn_full : certificatesIn U (View.full U) L r = certificates U L r :=
  Finset.inter_eq_left.mpr fun _ hC => (mem_certificates.mp hC).1

omit S in
theorem directCommitIn_full (h : DirectCommit U L r) :
    DirectCommitIn U (View.full U) L r := by
  rw [DirectCommitIn, certificatesIn_full]
  exact h

/-- **L4, as a decision.** What L6 consumes and L3 propagates. -/
theorem decided_of_leader_mem (hcard : 2 * F.f + 1 ≤ T.card)
    (hs : SynchronisedOn U T R) (hR : R ≤ S.slotRound k)
    (hpop0 : PopulatedOn U T (S.slotRound k))
    (hpop1 : PopulatedOn U T (S.slotRound k + 1))
    (hpop2 : PopulatedOn U T (S.slotRound k + 2))
    (hlead : S.leader k ∈ T) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLb, hdc⟩ :=
    directCommit_of_leader_mem hcard hs hR hpop0 hpop1 hpop2 hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_full hdc)⟩

/-- The same at `T := Correct`. -/
theorem decided_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) :=
  decided_of_leader_mem card_correct hs hR hpop0 hpop1 hpop2 hlead

/-! ## L5 — an absent leader is skipped

`liveness.md` §6. Nearly free, and it vindicates a C1 decision.

`Decided.directSkip` takes the premise `∀ L, IsLeaderBlock U k L → …`. When
the leader published nothing there is no such `L`, so the premise holds
**vacuously** and the case disappears. Choosing the `∀`-over-candidates form
over naming a single candidate block is what buys this: a formulation that
selected "the" leader block would have had nothing to select. -/

/-- L5, in the form the `Decided` constructor wants. -/
theorem decided_none_of_no_candidate {V : View Validator BlockId Payload U}
    (h : ∀ L, ¬ IsLeaderBlock U k L) : Decided U V k none :=
  Decided.directSkip fun L hL => absurd hL (h L)

/-- **L5 — an absent leader is skipped.** If the slot-`k` leader has no block
at its round, every view decides `none`. -/
theorem decided_none_of_leader_absent {V : View Validator BlockId Payload U}
    (h : ∀ b ∈ U.ids, (U.block b).round = S.slotRound k →
      (U.block b).creator ≠ S.leader k) :
    Decided U V k none :=
  decided_none_of_no_candidate fun _ hL => h _ hL.1 hL.2.1 hL.2.2

/-! ## L6 — commits recur

`liveness.md` §6. The statement's **quantifier order is its whole content**.

The tempting form — *given `Live U N`, for every `k` there is a committing
`k' ≥ k` with `slotRound k' + 2 ≤ N`* — is **not provable**. Fairness promises
a correct leader *somewhere* beyond `k`, and that slot may lie past the
horizon, with nothing to let you ask for a nearer one. Fixing `U` and `N`
first therefore caps how far fairness may reach.

Stated as below the problem disappears, because `k'` depends only on the
**schedule**: `FairSchedule` and `slotRound` are properties of the `Slots`
instance, not of any DAG. The slot is named first and the DAG grows to it
second — which is also the correct reading of *"the ledger grows without
bound"*: not that one DAG commits infinitely often (no `Finset` can), but
that no slot is the last one a DAG can be grown far enough to commit. -/

/-- The schedule names a correct leader arbitrarily far out. Without it no
recurrence statement holds: `Slots.leader` is an arbitrary function and could
name Byzantine validators forever, however synchronous the network. -/
def FairScheduleOn (T : Finset Validator) : Prop :=
  ∀ k, ∃ k', k ≤ k' ∧ S.leader k' ∈ T

/-- The all-of-`Correct` case. -/
abbrev FairSchedule : Prop := FairScheduleOn (Correct : Finset Validator)

omit [Fintype Validator] [DecidableEq Validator] F in
/-- Some slot sits at or beyond any given round.

Under the old three-round spacing this was a theorem — slot rounds grew at
least as fast as `3k`. A merely monotone schedule may not grow at all, so it
is now the class field `unbounded`; this is only that field, in the shape L6
wants. L6 genuinely needs it: fairness must be applied at a slot already past
`R`, and nothing else says such a slot exists. -/
theorem exists_slotRound_ge (n : ℕ) : ∃ k, n ≤ S.slotRound k := S.unbounded n

variable (Validator) in
/-- The least slot proposed at or after round `n`.

The old schedule needed no such thing: `3 * k ≤ slotRound k` made slot `n`
itself sit past round `n`, so `n` could be used as its own slot index. That
coincidence is gone — under multiple leaders slot `n` may still be far below
round `n` — so the slot has to be named. -/
def slotAt (n : ℕ) : ℕ := Nat.find (S.unbounded n)

omit [Fintype Validator] [DecidableEq Validator] F in
theorem le_slotRound_slotAt (n : ℕ) : n ≤ S.slotRound (slotAt Validator n) :=
  Nat.find_spec (S.unbounded n)

omit [Fintype Validator] [DecidableEq Validator] F in
@[simp]
theorem slotAt_zero : slotAt Validator 0 = 0 := by
  rw [slotAt, Nat.find_eq_zero]
  omega

omit [Fintype Validator] [DecidableEq Validator] F in
/-- **Every slot has an eligible anchor somewhere.**

The indirect rule may only anchor on a slot past `k`'s decision round, so the
restriction would be worthless if no such slot existed. It is the second job
`unbounded` does, and the reason a schedule that stalls at some round is
excluded: under one, a slot left undecided by the direct rules could never be
settled at all. -/
theorem exists_eligible (k : ℕ) : ∃ j, Eligible Validator k j := by
  obtain ⟨j, hj⟩ := S.unbounded (S.slotRound k + 3)
  exact ⟨j, by rw [eligible_iff]; omega⟩

/-- **L6 — commits recur.** For every slot `k` there is a later slot `k'`
that **every** sufficiently grown synchronous DAG commits.

Note the conclusion quantifies over `U` and `N` *inside* the existential: the
slot is fixed by the schedule alone, and any DAG grown past it commits it. -/
theorem commits_recur_on (hT : T ⊆ (Correct : Finset Validator))
    (hcard : 2 * F.f + 1 ≤ T.card) (fair : FairScheduleOn T) (R : ℕ) (k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (D : Delivery U) (N : ℕ),
        Live U D N → DeliversQuorum D → SynchronisedOn U T R →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) := by
  -- Some slot `k₀` already sits past round `R` (`unbounded`), and every slot
  -- from `k₀` on sits at least as late (`mono`). That is all this needs; the
  -- old proof got the same from `3 * k ≤ slotRound k`, which a pipelined or
  -- multi-leader schedule does not satisfy.
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨k', hk', hlead⟩ := fair (max k k₀)
  have hRk' : R ≤ S.slotRound k' :=
    le_trans hk₀ (S.mono (le_trans (le_max_right k k₀) hk'))
  refine ⟨k', le_trans (le_max_left _ _) hk', hRk', ?_⟩
  intro U D N H hd hs hN
  -- L1 populates all of `Correct`; `T` is a subset, so `.mono` bridges them.
  -- This is the one place `T ⊆ Correct` is genuinely needed: L4 alone cares
  -- only about `T.card`, but its population has to come from somewhere, and
  -- the only source is L1, which knows about correct validators.
  exact decided_of_leader_mem hcard hs hRk'
    (PopulatedOn.mono hT (no_stall H hd _ (by omega)))
    (PopulatedOn.mono hT (no_stall H hd _ (by omega)))
    (PopulatedOn.mono hT (no_stall H hd _ (by omega))) hlead

/-- **L6 at `T := Correct`.** The original statement, recovered. -/
theorem commits_recur (fair : FairSchedule (Validator := Validator)) (R : ℕ) (k : ℕ) :
    ∃ k', k ≤ k' ∧ R ≤ S.slotRound k' ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (D : Delivery U) (N : ℕ),
        Live U D N → DeliversQuorum D → Synchronised U R →
        S.slotRound k' + 2 ≤ N →
        ∃ L, IsLeaderBlock U k' L ∧ Decided U (View.full U) k' (some L) :=
  commits_recur_on Finset.Subset.rfl card_correct fair R k

/-! ## L8 — no undecided slot below a commit

L6 says commits recur. It does **not** say every slot is decided, and the
difference is what the ledger sees: `commitSeq` reads verdicts off in slot
order, so a single permanently undecided slot withholds delivery of everything
above it however many commits recur beyond. The Mysticeti paper calls this
backpressure and keeps it deliberately (§III-C).

The theorem below says the backpressure clears, under one hypothesis:
`helig`, that *every* later slot is an eligible anchor. That hypothesis is
exactly the old three-round spacing (`eligible_of_lt_of_spacing`), and
pipelining does destroy it — under `slotRound k = k` the two slots below any
anchor lie inside its decision round and cannot use it.

**But the conclusion survives pipelining**, and it is worth being precise about
why, because the tempting inference is wrong. It does *not* follow from "slot
`j - 1` cannot anchor on `j`" that `j - 1` must reach the next commit: nothing
strictly between `j - 1` and `j + 2` is *eligible*, so anchoring on `j + 2`
leaves the intermediate premise **vacuous**, and `j + 2` is ordinarily committed
too. `decided_of_first_eligible_commit` below is that argument, and it needs no
induction at all.

So `helig` is a convenience — it buys the nearest-anchor induction cheaply —
rather than the boundary of what is provable. The conclusion fails only when
commits are *isolated*, with no three consecutive: then `j - 1` really must
reach the next committed `j'`, whose own lower neighbour must reach past `j'`,
without end, and since `Decided` derivations are finite trees no derivation
exists. That configuration needs an adversarial *leader schedule* — Byzantine
leaders holding essentially three of every four consecutive slots — and fair
round-robin excludes it, correct validators holding runs of `2f+1 ≥ 3`
consecutive slots each of which commits directly after `R` by L4. L9 below is
the machine-checked form of the isolated-commit obstruction. -/

/-- **The escape.** If `j` is committed and *nothing strictly between `k` and
`j` is eligible to anchor `k`*, then `k` is decided outright: the
intermediate-skip premise is vacuous, so there is no induction and no appeal to
nearestness.

This is the fact that keeps pipelining live, and the one an earlier draft of
these notes missed. Slot `j - 1` sitting immediately below a committed `j`
cannot anchor on `j` — one round on, inside its decision round — but it *can*
anchor on `j + 2`, and neither `j` nor `j + 1` is eligible for it, so the
premise is empty and the slot resolves at once. Under fair leader election
`j + 2` is committed whenever `j` is, correct validators holding runs of
`2f+1 ≥ 3` consecutive slots.

No hypothesis on the schedule, and none on synchrony: like L8 this is pure
decision-relation combinatorics. -/
theorem decided_of_first_eligible_commit {V : View Validator BlockId Payload U}
    {k j : ℕ} {A : BlockId}
    (helig : Eligible Validator k j)
    (hfirst : ∀ i, k < i → i < j → ¬ Eligible Validator k i)
    (hj : Decided U V j (some A)) :
    ∃ v, Decided U V k v := by
  classical
  have hmid : ∀ i, k < i → i < j → Eligible Validator k i → Decided U V i none :=
    fun i h1 h2 h3 => absurd h3 (hfirst i h1 h2)
  by_cases hc : ∃ L, IsLeaderBlock U k L ∧ CertifiedIn U A L (S.slotRound k)
  · obtain ⟨L, hL, hcert⟩ := hc
    exact ⟨some L, Decided.indirectCommit (lt_of_eligible helig) helig hj hmid hL hcert⟩
  · push Not at hc
    exact ⟨none, Decided.indirectSkip (lt_of_eligible helig) helig hj hmid hc⟩

open Classical in
/-- **L8.** Given a committed slot, every slot below it is decided — provided
every later slot may anchor an earlier one.

No synchrony, no timing, no fairness: this is pure decision-relation
combinatorics, which is why it is worth isolating. The work is choosing the
*nearest* committed slot above `i` and reading the intermediate premise off the
induction hypothesis — an intermediate slot is decided by induction, and cannot
be decided `some` without contradicting nearestness, so it is decided `none`.

Note the proof never consults the direct rules. It does not need to: where the
direct rule commits, M2 puts the certificate in reach of the anchor, so the
indirect branch taken here agrees with it — and M6 guarantees as much in any
case. -/
theorem decided_of_committed_above
    (helig : ∀ a b : ℕ, a < b → Eligible Validator a b)
    {V : View Validator BlockId Payload U} {n : ℕ} {A : BlockId}
    (hn : Decided U V n (some A)) :
    ∀ i, i ≤ n → ∃ v, Decided U V i v := by
  classical
  have key : ∀ d i, i ≤ n → n - i ≤ d → ∃ v, Decided U V i v := by
    intro d
    induction d with
    | zero =>
      intro i hi hd
      exact ⟨some A, (by omega : i = n) ▸ hn⟩
    | succ d ih =>
      intro i hi hd
      rcases eq_or_lt_of_le hi with heq | hlt
      · exact ⟨some A, heq ▸ hn⟩
      -- The nearest committed slot strictly above `i`, which exists since `n`
      -- is one. `Nat.find` needs classical decidability: `Decided` is a Prop.
      have hex : ∃ j, i < j ∧ j ≤ n ∧ ∃ A', Decided U V j (some A') :=
        ⟨n, hlt, le_refl _, A, hn⟩
      obtain ⟨hij, hjn, A', hA'⟩ := Nat.find_spec hex
      -- Every slot between is decided by induction, and `none` by nearestness.
      have hmid : ∀ i', i < i' → i' < Nat.find hex →
          Eligible Validator i i' → Decided U V i' none := by
        intro i' h1 h2 _
        have hi'n : i' ≤ n := by omega
        obtain ⟨v, hv⟩ := ih i' hi'n (by omega)
        cases v with
        | none => exact hv
        | some B => exact absurd ⟨h1, hi'n, B, hv⟩ (Nat.find_min hex h2)
      by_cases hc : ∃ L, IsLeaderBlock U i L ∧ CertifiedIn U A' L (S.slotRound i)
      · obtain ⟨L, hL, hcert⟩ := hc
        exact ⟨some L, Decided.indirectCommit hij (helig i _ hij) hA' hmid hL hcert⟩
      · push Not at hc
        exact ⟨none, Decided.indirectSkip hij (helig i _ hij) hA' hmid hc⟩
  intro i hi
  exact key (n - i) i hi (le_refl _)

/-- **L8 under the old three-round spacing.** Combining L6 with L8: for every
slot `k` there is a slot `n ≥ k` such that a sufficiently grown synchronous DAG
decides *every* slot up to `n` — so the ledger does not stall below it.

`hsp` is the field the `Slots` class used to carry. A pipelined or multi-leader
schedule does not satisfy it, and the counterexample above is why this is
stated conditionally rather than dropped. -/
theorem all_decided_below_of_spacing
    (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k + 1))
    (hT : T ⊆ (Correct : Finset Validator)) (hcard : 2 * F.f + 1 ≤ T.card)
    (fair : FairScheduleOn T) (R : ℕ) (k : ℕ) :
    ∃ n, k ≤ n ∧ R ≤ S.slotRound n ∧
      ∀ (U : BlockUniverse Validator BlockId Payload) (D : Delivery U) (N : ℕ),
        Live U D N → DeliversQuorum D → SynchronisedOn U T R →
        S.slotRound n + 2 ≤ N →
        ∀ i, i ≤ n → ∃ v, Decided U (View.full U) i v := by
  obtain ⟨n, hkn, hRn, hcommit⟩ := commits_recur_on (BlockId := BlockId) (Payload := Payload)
    hT hcard fair R k
  refine ⟨n, hkn, hRn, ?_⟩
  intro U D N H hd hs hN
  obtain ⟨L, _, hdec⟩ := hcommit U D N H hd hs hN
  exact decided_of_committed_above (fun _ _ h => eligible_of_lt_of_spacing hsp h) hdec

/-! ## L9 — the obstruction: when slots are stuck for good

L8 clears the backpressure under `helig`. This is the converse direction, and
the reason `helig` is stated as a hypothesis rather than dropped: a set of slots
that is *stuck* stays stuck.

`X` is stuck when three things hold of every slot in it: no candidate has a
certificate anywhere (so neither the direct nor the indirect rule can commit
it), some candidate is not directly skippable (so the direct skip cannot fire
either — a slot with no candidate at all would be skipped vacuously, which is
why a candidate must be assumed to exist), and every *committed eligible* anchor
has another member of `X` eligibly between it and the slot.

**The third clause is about the leader schedule, not about pipelining.** It
requires commits to be *isolated*: with three consecutive commits available the
escape (`decided_of_first_eligible_commit`) gives a vacuous intermediate range
and the clause fails. Under the old three-round spacing it cannot hold at all,
which `stuck_empty_below_commit_of_spacing` below turns into a theorem; under a
pipelined schedule it holds only where Byzantine leaders take essentially three
of every four consecutive slots, which fair round-robin excludes.

So this theorem bounds *when* a stall is possible. It is not a deficiency of
pipelined Mysticeti as deployed. Two things it does not supply: a concrete
universe satisfying the first two clauses — that needs a DAG in which a
Byzantine leader's candidate collects `2f` votes and `2f` blames, one short of
each threshold — and a schedule satisfying the third, which no fair schedule
can. -/

/-- **L9.** Nothing in a stuck set is ever decided, on any view.

Induction on the derivation. Three of the four cases die immediately: a direct
commit and an indirect commit both produce a certificate, and a direct skip
contradicts the unskippable candidate. The fourth, indirect skip, is the
content: its intermediate premise is a *sub-derivation* at some slot which the
regress clause places back inside `X`, so the induction hypothesis applies. A
derivation is a finite tree, so the descent cannot continue for ever — which is
precisely the informal argument, discharged by structural induction rather than
by hand. -/
theorem notMem_stuck_of_decided {V : View Validator BlockId Payload U} {X : Set ℕ}
    (hcert : ∀ i ∈ X, ∀ L, IsLeaderBlock U i L → certificates U L (S.slotRound i) = ∅)
    (hskip : ∀ i ∈ X, ∃ L, IsLeaderBlock U i L ∧ ¬ DirectSkipIn U V L (S.slotRound i))
    (hregress : ∀ i ∈ X, ∀ j, Eligible Validator i j → (∃ A, Decided U V j (some A)) →
      ∃ i', i' ∈ X ∧ i < i' ∧ i' < j ∧ Eligible Validator i i')
    {i : ℕ} {v : Option BlockId} (h : Decided U V i v) : i ∉ X := by
  induction h with
  | @directCommit k L hL hdc =>
    intro hk
    obtain ⟨C, hC⟩ := certificates_nonempty_of_directCommit (directCommit_of_directCommitIn hdc)
    rw [hcert k hk L hL] at hC
    exact absurd hC (Finset.notMem_empty C)
  | @directSkip k hall =>
    intro hk
    obtain ⟨L, hL, hns⟩ := hskip k hk
    exact hns (hall L hL)
  | @indirectCommit k j A L _ _ _ _ hL hcertIn _ _ =>
    intro hk
    obtain ⟨C, hC⟩ := certificates_nonempty_of_certifiedIn hcertIn
    rw [hcert k hk L hL] at hC
    exact absurd hC (Finset.notMem_empty C)
  | @indirectSkip k j A _ helig hj _ _ _ ihmid =>
    intro hk
    obtain ⟨i', hi'X, h1, h2, h3⟩ := hregress k hk j helig ⟨A, hj⟩
    exact ihmid i' h1 h2 h3 hi'X

/-- **L8 and L9 are consistent, and their hypotheses are jointly exhaustive.**

Under the old three-round spacing a stuck set has no member below a committed
slot — so the counterexample of L9 cannot be built there, however the DAG is
arranged. Composing the two results: L8 decides the slot, L9 says a decided
slot is outside `X`.

This is also the check that neither theorem is vacuous. L9 is not the
observation that its hypotheses are unsatisfiable; it is that they are
unsatisfiable *under `helig`*, and satisfiable without it. -/
theorem stuck_empty_below_commit_of_spacing
    (hsp : ∀ k, S.slotRound k + 3 ≤ S.slotRound (k + 1))
    {V : View Validator BlockId Payload U} {X : Set ℕ}
    (hcert : ∀ i ∈ X, ∀ L, IsLeaderBlock U i L → certificates U L (S.slotRound i) = ∅)
    (hskip : ∀ i ∈ X, ∃ L, IsLeaderBlock U i L ∧ ¬ DirectSkipIn U V L (S.slotRound i))
    (hregress : ∀ i ∈ X, ∀ j, Eligible Validator i j → (∃ A, Decided U V j (some A)) →
      ∃ i', i' ∈ X ∧ i < i' ∧ i' < j ∧ Eligible Validator i i')
    {n : ℕ} {A : BlockId} (hn : Decided U V n (some A)) :
    ∀ i, i ≤ n → i ∉ X := by
  intro i hi
  obtain ⟨v, hv⟩ :=
    decided_of_committed_above (fun _ _ h => eligible_of_lt_of_spacing hsp h) hn i hi
  exact notMem_stuck_of_decided hcert hskip hregress hv

end LeanDag
