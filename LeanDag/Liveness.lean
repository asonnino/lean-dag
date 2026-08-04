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
/-- What L4 actually needs of a round: every correct validator has a block
there.

Local and finite — no growth, no horizon. Splitting this out is what keeps
the horizon `N` out of L4 entirely, so the only hard proof in the plan is
independent of how `Live` is framed. -/
def Populated (U : BlockUniverse Validator BlockId Payload) (r : ℕ) : Prop :=
  ∀ v ∈ (Correct : Finset Validator), ∃ b ∈ U.ids,
    (U.block b).creator = v ∧ (U.block b).round = r

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
structure Live (U : BlockUniverse Validator BlockId Payload) (N : ℕ) : Prop where
  /-- Every correct validator has a genesis block. -/
  genesis : Populated U 0
  /-- Below the horizon, a quorum at round `r` yields blocks at `r+1`. -/
  builds : ∀ r < N, 2 * F.f + 1 ≤ (authorsAt U r).card → Populated U (r + 1)

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
/-- **L1 — no stall.** Under `Live U N`, every correct validator has a block
at every round up to the horizon.

Induction on the round. The base is `genesis`; the step observes that "every
correct validator has a round-`r` block" makes `Correct` a subset of
`authorsAt U r`, which is a quorum, and feeds that to `builds`.

L1 is the **only** result where the horizon does real work. Its whole job is
to turn the growth assumption into the local `Populated` facts L4 consumes —
which is why L4 itself never mentions `N` (`liveness.md` §4.4). -/
theorem no_stall (H : Live U N) : ∀ r ≤ N, Populated U r := by
  intro r
  induction r with
  | zero => intro _; exact H.genesis
  | succ r ih =>
      intro hr
      exact H.builds r (by omega) (card_authorsAt_of_populated (ih (by omega)))

omit [DecidableEq BlockId] in
/-- L1 in the form L0 consumes: under `Live U N` **every** round up to the
horizon carries a quorum of authors, not merely every round below some
frontier. -/
theorem card_authorsAt_of_live (H : Live U N) {r : ℕ} (hr : r ≤ N) :
    2 * F.f + 1 ≤ (authorsAt U r).card :=
  card_authorsAt_of_populated (no_stall H r hr)

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
def Synchronised (U : BlockUniverse Validator BlockId Payload) (R : ℕ) : Prop :=
  ∀ n, R ≤ n → ∀ b ∈ U.ids, (U.block b).round = n + 1 →
    (U.block b).creator ∈ (Correct : Finset Validator) →
    ∀ a ∈ U.ids, (U.block a).round = n →
      (U.block a).creator ∈ (Correct : Finset Validator) → a ∈ (U.block b).refs

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
  | indirectCommit hkj _ _ hL hcert ihj ihmid =>
      exact Decided.indirectCommit hkj ihj ihmid hL hcert
  | indirectSkip hkj _ _ hnc ihj ihmid =>
      exact Decided.indirectSkip hkj ihj ihmid hnc

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

variable {L C : BlockId} {R r : ℕ} {k : ℕ}

omit S in
/-- A correct round-`(r+2)` block certifies any correct round-`r` block, once
round `r+1` is populated and synchrony has taken hold.

This is both layers at once: `q` references `L` by coverage at `n = r`, and
`C` references `q` by coverage at `n = r+1`. -/
theorem certifies_of_synchronised (hs : Synchronised U R) (hRr : R ≤ r)
    (hpop1 : Populated U (r + 1))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r)
    (hLc : (U.block L).creator ∈ (Correct : Finset Validator))
    (hC : C ∈ U.ids) (hCr : (U.block C).round = r + 2)
    (hCc : (U.block C).creator ∈ (Correct : Finset Validator)) :
    Certifies U C L := by
  refine le_trans card_correct (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨q, hq, hqc, hqr⟩ := hpop1 v hv
  have hqcorrect : (U.block q).creator ∈ (Correct : Finset Validator) := by rw [hqc]; exact hv
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
theorem directCommit_of_synchronised (hs : Synchronised U R) (hRr : R ≤ r)
    (hpop1 : Populated U (r + 1)) (hpop2 : Populated U (r + 2))
    (hL : L ∈ U.ids) (hLr : (U.block L).round = r)
    (hLc : (U.block L).creator ∈ (Correct : Finset Validator)) :
    DirectCommit U L r := by
  refine le_trans card_correct (Finset.card_le_card ?_)
  intro v hv
  obtain ⟨C, hC, hCc, hCr⟩ := hpop2 v hv
  have hCcorrect : (U.block C).creator ∈ (Correct : Finset Validator) := by rw [hCc]; exact hv
  rw [mem_creatorsOf]
  exact ⟨C, mem_certificates.mpr ⟨hC, hCr,
    certifies_of_synchronised hs hRr hpop1 hL hLr hLc hC hCr hCcorrect⟩, hCc⟩

omit [DecidableEq BlockId] in
/-- A correct leader has a candidate block, once its round is populated.
`Populated` at the leader's own round is needed for nothing else. -/
theorem exists_isLeaderBlock (hpop : Populated U (S.slotRound k))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L := by
  obtain ⟨L, hL, hLc, hLr⟩ := hpop (S.leader k) hlead
  exact ⟨L, hL, hLr, hLc⟩

/-- **L4.** A slot with a correct leader, whose three rounds are populated and
which sits after synchrony, is directly committed. -/
theorem directCommit_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ DirectCommit U L (S.slotRound k) := by
  obtain ⟨L, hL, hLr, hLc⟩ := exists_isLeaderBlock hpop0 hlead
  exact ⟨L, ⟨hL, hLr, hLc⟩,
    directCommit_of_synchronised hs hR hpop1 hpop2 hL hLr (by rw [hLc]; exact hlead)⟩

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
theorem decided_of_correct_leader (hs : Synchronised U R)
    (hR : R ≤ S.slotRound k)
    (hpop0 : Populated U (S.slotRound k))
    (hpop1 : Populated U (S.slotRound k + 1))
    (hpop2 : Populated U (S.slotRound k + 2))
    (hlead : S.leader k ∈ (Correct : Finset Validator)) :
    ∃ L, IsLeaderBlock U k L ∧ Decided U (View.full U) k (some L) := by
  obtain ⟨L, hLb, hdc⟩ :=
    directCommit_of_correct_leader hs hR hpop0 hpop1 hpop2 hlead
  exact ⟨L, hLb, Decided.directCommit hLb (directCommitIn_full hdc)⟩

end LeanDag
