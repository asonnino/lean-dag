import LeanDag.FinWhale.Order
import Mathlib.Data.Finset.Sort
import LeanDag.FinWhale.Rotation

/-!
# FinWhale — every slot is decided, and what follows

Lemma 23 and Theorems 24 and 26. Lemma 12 said two validators never
disagree; these say they eventually agree about *everything*.

**Lemma 23 is a statement about one DAG, not about time.** The paper
reads it as "after GST any undecided slot eventually gets decided", where
eventually means in a later and larger DAG. Written that way it would
contradict the finiteness Lemma 12 consumes — nothing above some `N` is
decided in a DAG that stops. What holds of a single DAG is the content of
the argument: a slot below a committed anchor is decided, and §10's
liveness supplies committed anchors above every round once the leader
schedule names three correct leaders in a row.

So `lemma23` here takes a committed triple above the slot and concludes
that the slot is decided. Growth enters where it belongs, in the
hypothesis: a larger DAG carries a triple further up, and every slot
below it is decided.
-/

namespace LeanDag

namespace FinWhale

variable {BlockId : Type*} [DecidableEq BlockId]

omit [DecidableEq BlockId] in
/-- **Lemma 23.** Every slot below a committed triple is decided.

The paper's argument, with the maximality made explicit: if some slot
below the triple were undecided, take the highest such. Everything above
it up to the triple is decided, so the first non-skipped slot above it is
a commit and serves as its anchor — and a slot with a committed anchor is
decided by the reverse pass.

The triple is what covers the three offsets: the anchor must sit above
`r + 2`, and for `r` within two of the triple's start only its later
members qualify. -/
theorem lemma23 {dc : ℕ → BlockId → Prop} {ds : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed dc ds choose dec) {r a : ℕ} (hra : r < a)
    (htri : ∀ s, a ≤ s → s ≤ a + 2 → dec s ≠ Verdict.undecided ∧ dec s ≠ Verdict.skip) :
    dec r ≠ Verdict.undecided := by
  classical
  intro hru
  -- the highest undecided slot at or below the triple's top
  have hrle : r ≤ a + 2 := by omega
  have hm : dec (Nat.findGreatest (fun s => dec s = Verdict.undecided) (a + 2)) =
      Verdict.undecided :=
    Nat.findGreatest_spec (P := fun s => dec s = Verdict.undecided) hrle hru
  set m := Nat.findGreatest (fun s => dec s = Verdict.undecided) (a + 2) with hmdef
  have hmle : m ≤ a + 2 := Nat.findGreatest_le _
  have hgreat : ∀ n, m < n → n ≤ a + 2 → dec n ≠ Verdict.undecided :=
    fun n h1 h2 => Nat.findGreatest_is_greatest h1 h2
  have hma : m < a := by
    rcases Nat.lt_or_ge m a with h | h
    · exact h
    · exact absurd hm (htri m h hmle).1
  -- one of the triple lies above `m + 2` and is not skipped
  obtain ⟨w, hwle, hwskip⟩ : ∃ w, m + 3 + w ≤ a + 2 ∧ dec (m + 3 + w) ≠ Verdict.skip := by
    rcases Nat.lt_or_ge (m + 2) a with h | h
    · exact ⟨a - (m + 3), by omega,
        by rw [show m + 3 + (a - (m + 3)) = a by omega]; exact (htri a le_rfl (by omega)).2⟩
    · exact ⟨a + 2 - (m + 3), by omega,
        by rw [show m + 3 + (a + 2 - (m + 3)) = a + 2 by omega]
           exact (htri (a + 2) (by omega) le_rfl).2⟩
  have hex : ∃ k, dec (m + 3 + k) ≠ Verdict.skip := ⟨w, hwskip⟩
  -- the first such slot is the anchor of `m`
  have hfind : Nat.find hex ≤ w := Nat.find_le hwskip
  have hanchor : Anchor dec m (m + 3 + Nat.find hex) := by
    refine ⟨by omega, Nat.find_spec hex, ?_⟩
    intro t ht1 ht2
    have hlt : t - (m + 3) < Nat.find hex := by omega
    have hmin := Nat.find_min hex hlt
    rw [show m + 3 + (t - (m + 3)) = t by omega] at hmin
    exact not_not.1 hmin
  have hdec : dec (m + 3 + Nat.find hex) ≠ Verdict.undecided :=
    hgreat _ (by omega) (by omega)
  -- so the anchor is committed, and the reverse pass decides `m`
  by_cases hdcm : ∃ l, dc m l
  · obtain ⟨l, hl⟩ := hdcm
    exact absurd (hwf.direct_commit m l hl) (by rw [hm]; simp)
  · by_cases hdsm : ds m
    · exact absurd (hwf.direct_skip m hdsm) (by rw [hm]; simp)
    · rcases hva : dec (m + 3 + Nat.find hex) with A | - | -
      · have := hwf.indirect_commit m _ A hdcm hdsm hanchor hva
        rw [hm] at this
        rcases hch : choose A m with - | b
        · rw [hch] at this; simp at this
        · rw [hch] at this; simp at this
      · exact absurd hva hanchor.2.1
      · exact absurd hva hdec

/-! ## Committed anchors, from §10's liveness

`lemma23` asks for a committed triple. This is where it comes from: the
rotation names three consecutive correct leaders (Lemma 22), and coverage
commits each of their blocks (Lemma 20).

One hypothesis carries the growth. `hsees` says a validator's view holds
what the universe holds — that a direct commit of the universe is a
direct commit of this validator's view. Read the other way it is the
statement that the certificates have arrived, which is the "eventually"
the paper's Lemma 23 is stated with, and it is the converse of what
`exclusions_of_dag` consumes for safety. -/

section Triple

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {Payload : Type*} {D : Dag Validator BlockId Payload}

/-- **The liveness input, as an interface.** Every correct-led slot past
the coverage round and below the horizon carries a direct commit. Both
pacing disciplines supply this — the full-timeout one through coverage
(`commits_of_synchronised`), the reactive one through its wait clauses
(`FinWhale.Reactive`) — and nothing below cares which. -/
def CommitsCorrectLeaders (D : Dag Validator BlockId Payload) (R N : ℕ) : Prop :=
  ∀ s, R ≤ s → s + 2 ≤ N → D.leader s ∈ (Correct : Finset Validator) →
    ∃ l ∈ slotBlocks D s, ∃ certs : Finset Validator,
      certs ⊆ (Correct : Finset Validator) ∧ spQuorum Validator ≤ certs.card ∧
      ∀ v ∈ certs, ∃ b ∈ blocksAt D ((D.block l).round + 2),
        (D.block b).creator = v ∧ SPCertificate D b l

/-- The commit the interface carries. -/
theorem directCommit_of_commits {R N : ℕ} (h : CommitsCorrectLeaders D R N) {s : ℕ}
    (hR : R ≤ s) (hN : s + 2 ≤ N) (hlead : D.leader s ∈ (Correct : Finset Validator)) :
    ∃ l ∈ slotBlocks D s, DirectCommit D l := by
  obtain ⟨l, hslot, certs, -, hcard, hcertb⟩ := h s hR hN hlead
  exact ⟨l, hslot, Or.inr ⟨certs, hcard, hcertb⟩⟩

/-- **What Lemma 23 consumes**: the deciding validator *sees* a direct
commit at every correct-led slot below the horizon. One clause where
there were two — a commit in the universe, and the view seeing it —
because the second is where a view's holdings enter and the first is
where the schedule does. -/
def SeesCommits (D : Dag Validator BlockId Payload) (dc : ℕ → BlockId → Prop) (R N : ℕ) :
    Prop :=
  ∀ s, R ≤ s → s + 2 ≤ N → D.leader s ∈ (Correct : Finset Validator) →
    ∃ l, l ∈ slotBlocks D s ∧ dc s l

/-- A validator reading the whole universe sees them all. -/
theorem sees_of_commits {R N : ℕ} (h : CommitsCorrectLeaders D R N) :
    SeesCommits D (fun r l => l ∈ slotBlocks D r ∧ DirectCommit D l) R N := by
  intro s hR hN hlead
  obtain ⟨l, hslot, hcom⟩ := directCommit_of_commits h hR hN hlead
  exact ⟨l, hslot, hslot, hcom⟩

/-- **A committed triple above every round.** -/
theorem committed_triple {dc : ℕ → BlockId → Prop} {ds : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed dc ds choose dec) {R N t : ℕ}
    (hsees : SeesCommits D dc R N)
    (hrr : RoundRobin D.leader) (hR : R ≤ t) (hN : t + (3 * F.f + 5) ≤ N) :
    ∃ a, t < a ∧ a + 4 ≤ N ∧
      ∀ s, a ≤ s → s ≤ a + 2 →
        dec s ≠ Verdict.undecided ∧ dec s ≠ Verdict.skip := by
  obtain ⟨a, hlo, hhi, h0, h1, h2⟩ := lemma22 hrr (t + 1)
  refine ⟨a, by omega, by omega, fun s hs1 hs2 => ?_⟩
  have hsc : D.leader s ∈ (Correct : Finset Validator) := by
    rcases (by omega : s = a ∨ s = a + 1 ∨ s = a + 2) with rfl | rfl | rfl
    exacts [h0, h1, h2]
  obtain ⟨l, -, hdcl⟩ := hsees s (by omega) (by omega) hsc
  rw [hwf.direct_commit s l hdcl]
  exact ⟨by simp, by simp⟩

/-- **Lemma 23, composed.** Every slot below the horizon is decided —
including the slots before GST, which the reverse pass decides from an
anchor above them. Only the *triple* has to sit past the coverage round,
which is why `R` enters through a maximum rather than as a floor on
`r`. -/
theorem all_decided {dc : ℕ → BlockId → Prop} {ds : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed dc ds choose dec) {R N r : ℕ}
    (hsees : SeesCommits D dc R N)
    (hrr : RoundRobin D.leader) (hN : max r R + (3 * F.f + 5) ≤ N) :
    dec r ≠ Verdict.undecided := by
  obtain ⟨a, hlo, -, htri⟩ :=
    committed_triple hwf hsees hrr (le_max_right r R) hN
  exact lemma23 hwf (lt_of_le_of_lt (le_max_left r R) hlo) htri

end Triple

/-! ## From decided slots to delivered blocks -/

omit [DecidableEq BlockId] in
/-- A committed slot's block is in the commit sequence, once the sequence
reaches that slot. -/
theorem mem_commitSeq {dec : ℕ → Verdict BlockId} {r : ℕ} {l : BlockId} :
    ∀ k, r < k → dec r = Verdict.commit l → l ∈ commitSeq dec k := by
  intro k
  induction k with
  | zero => intro h; omega
  | succ k ih =>
    intro hr hcom
    rcases Nat.lt_or_ge r k with h | h
    · exact List.mem_append_left _ (ih h hcom)
    · have hrk : r = k := by omega
      subst hrk
      simp [commitSeq, hcom]

/-- The accumulator survives the fold. -/
theorem subset_foldl (hist : BlockId → List BlockId) (ls acc : List BlockId) :
    ∀ b ∈ acc, b ∈ ls.foldl (fun acc l => acc ++ (hist l).filter (fun b => b ∉ acc)) acc := by
  obtain ⟨t, ht⟩ := linearise_foldl_append hist ls acc
  intro b hb
  rw [ht]
  exact List.mem_append_left _ hb

/-- **Everything in a committed leader's history is delivered.** Either
an earlier leader delivered it, or this one does. -/
theorem mem_linearise (hist : BlockId → List BlockId) :
    ∀ (ls : List BlockId) (acc : List BlockId) (l : BlockId), l ∈ ls → ∀ b ∈ hist l,
      b ∈ ls.foldl (fun acc l => acc ++ (hist l).filter (fun b => b ∉ acc)) acc := by
  intro ls
  induction ls with
  | nil => intro acc l hl; simp at hl
  | cons x xs ih =>
    intro acc l hl b hb
    rcases List.mem_cons.1 hl with rfl | hl'
    · by_cases hba : b ∈ acc
      · exact subset_foldl hist xs _ b (List.mem_append_left _ hba)
      · refine subset_foldl hist xs _ b (List.mem_append_right _ ?_)
        refine List.mem_filter.2 ⟨hb, ?_⟩
        simpa using hba
    · exact ih _ l hl' b hb

omit [DecidableEq BlockId] in
/-- **Lemma 25.** A committed leader block is in the commit sequence. -/
theorem lemma25 {dec : ℕ → Verdict BlockId} {r k : ℕ} {l : BlockId}
    (hr : r < k) (hcom : dec r = Verdict.commit l) : l ∈ commitSeq dec k :=
  mem_commitSeq k hr hcom

/-- **Theorem 24 (Agreement).** Two validators that have decided every
slot below `k` deliver the same sequence — not merely comparable ones.
Lemma 12 supplies the agreement, `commitSeq_congr` carries it to the
sequence, and the delivery order is a function of that. -/
theorem theorem24 {dec dec' : ℕ → Verdict BlockId} {k : ℕ}
    (hagree : ∀ s, dec s ≠ Verdict.undecided → dec' s ≠ Verdict.undecided → dec s = dec' s)
    (hdec : ∀ s, s < k → dec s ≠ Verdict.undecided)
    (hdec' : ∀ s, s < k → dec' s ≠ Verdict.undecided)
    (hist : BlockId → List BlockId) :
    linearise hist (commitSeq dec k) = linearise hist (commitSeq dec' k) := by
  rw [commitSeq_congr k fun s hs => hagree s (hdec s hs) (hdec' s hs)]

/-- **Theorem 26 (Validity), at the list layer.** A block in the causal
history of a committed leader is delivered. -/
theorem theorem26 {dec : ℕ → Verdict BlockId} {hist : BlockId → List BlockId} {r k : ℕ}
    {l b : BlockId} (hr : r < k) (hcom : dec r = Verdict.commit l) (hb : b ∈ hist l) :
    b ∈ linearise hist (commitSeq dec k) :=
  mem_linearise hist _ [] l (lemma25 hr hcom) b hb

/-! ## The delivery order, concretely -/

section Order

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {Payload : Type*} {D : Dag Validator BlockId Payload}

/-- **The delivery order's input, concretely.** A leader contributes its
causal history, which `historyFrom` computes from the references alone,
listed in the identifier order.

The paper asks only for "a deterministic sort", and what Theorems 24 and
26 read is that the list is a function of the block and lists its causal
history once each. Sorting by identifier is the cheapest such function
and keeps the definition computable; a causal order would serve equally
and is not what any result here consumes. -/
def histOf [LinearOrder BlockId] (D : Dag Validator BlockId Payload) (l : BlockId) :
    List BlockId :=
  (historyFrom D.block l).sort (· ≤ ·)

/-- `histOf` is the causal history: the faithfulness condition Theorem 26
asks for, discharged. -/
theorem mem_histOf [LinearOrder BlockId] {l c : BlockId} (hl : l ∈ D.ids)
    (h : ReachesFrom D.block l c) : c ∈ histOf D l :=
  (Finset.mem_sort _).2 (((causalStructure D).mem_history_iff hl).2 h)

/-- And it lists each block once, which is the condition Theorem 15 asks
for. -/
theorem nodup_histOf [LinearOrder BlockId] {l : BlockId} : (histOf D l).Nodup :=
  Finset.sort_nodup _ _

/-- **Theorem 15 at the concrete order.** No block is delivered twice. -/
theorem nodup_delivery [LinearOrder BlockId] (ls : List BlockId) :
    (linearise (histOf D) ls).Nodup :=
  theorem15 _ (fun _ => nodup_histOf) ls

end Order

/-! ## The two theorems, end to end -/

section Capstone

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {Payload : Type*} {D : Dag Validator BlockId Payload}

/-- **Theorem 24 (Agreement), end to end.** Two validators of one DAG
deliver the same sequence at every horizon the DAG supports.

Both halves are consumed here: Lemma 12 makes the verdicts agree wherever
both are decided, and Lemma 23 makes them decided. `hcommits` is the
liveness interface, and the schedule that supplies it does not appear.
The two finiteness conditions sit together rather than in conflict —
`hbound` says nothing above `M` is decided, and the horizon is placed
below what the DAG's own reach decides. -/
theorem agreement_of_commits {R N : ℕ}
    (hrr : RoundRobin D.leader)
    {dc dc' : ℕ → BlockId → Prop} {ds ds' : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec dec' : ℕ → Verdict BlockId}
    (hwf : WellFormed dc ds choose dec) (hwf' : WellFormed dc' ds' choose dec')
    (hch : ChooseSound D choose)
    (hdc : ∀ r l, dc r l → l ∈ slotBlocks D r ∧ DirectCommit D l)
    (hdc' : ∀ r l, dc' r l → l ∈ slotBlocks D r ∧ DirectCommit D l)
    (hds : ∀ r, ds r → DirectSkip D r) (hds' : ∀ r, ds' r → DirectSkip D r)
    (hsees : SeesCommits D dc R N) (hsees' : SeesCommits D dc' R N)
    (hslot : ∀ r A, dec r = Verdict.commit A → A ∈ slotBlocks D r)
    (hslot' : ∀ r A, dec' r = Verdict.commit A → A ∈ slotBlocks D r)
    {M : ℕ} (hbound : ∀ s, M ≤ s → dec s = Verdict.undecided ∧ dec' s = Verdict.undecided)
    {k : ℕ} (hkN : max k R + (3 * F.f + 5) ≤ N)
    (hist : BlockId → List BlockId) :
    linearise hist (commitSeq dec k) = linearise hist (commitSeq dec' k) := by
  have habove : ∀ (dq : ℕ → Verdict BlockId),
      (∀ r A, dq r = Verdict.commit A → A ∈ slotBlocks D r) →
      ∀ r a A, r + 2 < a → dq a = Verdict.commit A → A ∈ D.ids ∧ r + 3 ≤ (D.block A).round := by
    intro dq hq r a A hra hcom
    have hA := hq a A hcom
    simp only [slotBlocks, blocksAt, Finset.mem_filter] at hA
    exact ⟨hA.1.1, by omega⟩
  refine theorem24
    (lemma12 hwf hwf' (exclusions_of_dag hch hdc hdc' hds hds')
      (habove dec hslot) (habove dec' hslot') hbound)
    (fun s hs => all_decided hwf hsees hrr (by
      have : max s R ≤ max k R := max_le_max (by omega) le_rfl
      omega))
    (fun s hs => all_decided hwf' hsees' hrr (by
      have : max s R ≤ max k R := max_le_max (by omega) le_rfl
      omega))
    hist

end Capstone

end FinWhale

end LeanDag
