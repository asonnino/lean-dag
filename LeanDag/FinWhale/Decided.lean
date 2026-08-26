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

/-- **A committed triple above every round.** -/
theorem committed_triple {dc : ℕ → BlockId → Prop} {ds : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed dc ds choose dec) {R N t : ℕ}
    (hsees : ∀ r l, r + 2 ≤ N → l ∈ slotBlocks D r → DirectCommit D l → dc r l)
    (hsync : SynchronisedFrom D.block D.ids (Correct : Finset Validator) R)
    (hpop : ∀ n, n ≤ N → PopulatedFrom D.block D.ids (Correct : Finset Validator) n)
    (hrr : RoundRobin D.leader) (hR : R ≤ t) (hN : t + (3 * F.f + 5) ≤ N) :
    ∃ a, t < a ∧ a + 4 ≤ N ∧
      ∀ s, a ≤ s → s ≤ a + 2 →
        dec s ≠ Verdict.undecided ∧ dec s ≠ Verdict.skip := by
  obtain ⟨a, hlo, hhi, h0, h1, h2⟩ := lemma22 hrr (t + 1)
  refine ⟨a, by omega, by omega, fun s hs1 hs2 => ?_⟩
  -- the leader of `s` is correct, so its block is directly committed
  have hsc : D.leader s ∈ (Correct : Finset Validator) := by
    rcases (by omega : s = a ∨ s = a + 1 ∨ s = a + 2) with rfl | rfl | rfl
    exacts [h0, h1, h2]
  obtain ⟨l, hl, hlc, hlr⟩ := hpop s (by omega) (D.leader s) hsc
  have hslot : l ∈ slotBlocks D s := by
    simp only [slotBlocks, blocksAt, Finset.mem_filter]
    exact ⟨⟨hl, hlr⟩, hlc⟩
  have hcom : DirectCommit D l :=
    Or.inr (lemma20 hsync (by omega) (hpop (s + 1) (by omega)) (hpop (s + 2) (by omega))
      hl hlr (by rw [hlc]; exact hsc))
  rw [hwf.direct_commit s l (hsees s l (by omega) hslot hcom)]
  exact ⟨by simp, by simp⟩

/-- **Lemma 23, composed.** Every slot below the horizon is decided —
including the slots before GST, which the reverse pass decides from an
anchor above them. Only the *triple* has to sit past the coverage round,
which is why `R` enters through a maximum rather than as a floor on
`r`. -/
theorem all_decided {dc : ℕ → BlockId → Prop} {ds : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed dc ds choose dec) {R N r : ℕ}
    (hsees : ∀ r l, r + 2 ≤ N → l ∈ slotBlocks D r → DirectCommit D l → dc r l)
    (hsync : SynchronisedFrom D.block D.ids (Correct : Finset Validator) R)
    (hpop : ∀ n, n ≤ N → PopulatedFrom D.block D.ids (Correct : Finset Validator) n)
    (hrr : RoundRobin D.leader) (hN : max r R + (3 * F.f + 5) ≤ N) :
    dec r ≠ Verdict.undecided := by
  obtain ⟨a, hlo, -, htri⟩ :=
    committed_triple hwf hsees hsync hpop hrr (le_max_right r R) hN
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

section Validity

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {Payload : Type*} {D : Dag Validator BlockId Payload}

/-- **Every correct block reaches the next round's correct leader.**
Coverage, read as a statement about causal history: this is what carries
a correct validator's payload into a committed leader's history. -/
theorem reaches_of_synchronised {R n : ℕ}
    (hsync : SynchronisedFrom D.block D.ids (Correct : Finset Validator) R) (hR : R ≤ n)
    {b l : BlockId} (hb : b ∈ D.ids) (hbr : (D.block b).round = n)
    (hbc : (D.block b).creator ∈ (Correct : Finset Validator))
    (hl : l ∈ D.ids) (hlr : (D.block l).round = n + 1)
    (hlc : (D.block l).creator ∈ (Correct : Finset Validator)) :
    ReachesFrom D.block l b :=
  ReachesFrom.single (hsync n hR l hl hlr hlc b hb hbr hbc)

/-- **Theorem 26 (Validity).** A correct validator's block is delivered,
once the leader of the round above it is correct and its slot is
committed.

`hhist` is the faithfulness condition on the ordering: the list a leader
contributes is its causal history. -/
theorem theorem26_of_synchronised {dec : ℕ → Verdict BlockId}
    {hist : BlockId → List BlockId} {R n k : ℕ}
    (hsync : SynchronisedFrom D.block D.ids (Correct : Finset Validator) R) (hR : R ≤ n)
    {b l : BlockId} (hb : b ∈ D.ids) (hbr : (D.block b).round = n)
    (hbc : (D.block b).creator ∈ (Correct : Finset Validator))
    (hl : l ∈ D.ids) (hlr : (D.block l).round = n + 1)
    (hlc : (D.block l).creator ∈ (Correct : Finset Validator))
    (hhist : ∀ c, ReachesFrom D.block l c → c ∈ hist l)
    (hk : n + 1 < k) (hcom : dec (n + 1) = Verdict.commit l) :
    b ∈ linearise hist (commitSeq dec k) :=
  theorem26 hk hcom (hhist b (reaches_of_synchronised hsync hR hb hbr hbc hl hlr hlc))

/-- **A FinWhale DAG is a causal structure.** Its two conditions are the
DAG's closure under references and validity's predecessor clause. -/
theorem causalStructure (D : Dag Validator BlockId Payload) :
    CausalStructure D.block D.ids :=
  ⟨D.complete, fun i hi j hj => (D.valid i hi).predecessor j hj⟩

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
theorem nodup_delivery [LinearOrder BlockId] (ls : List BlockId) : (linearise (histOf D) ls).Nodup :=
  theorem15 _ (fun _ => nodup_histOf) ls

/-- **Theorem 26 at the concrete order.** A correct validator's block is
delivered once the leader above it is committed — with no hypothesis about
what the ordering reads, since it reads the causal history. -/
theorem delivered_of_synchronised [LinearOrder BlockId] {dec : ℕ → Verdict BlockId} {R n k : ℕ}
    (hsync : SynchronisedFrom D.block D.ids (Correct : Finset Validator) R) (hR : R ≤ n)
    {b l : BlockId} (hb : b ∈ D.ids) (hbr : (D.block b).round = n)
    (hbc : (D.block b).creator ∈ (Correct : Finset Validator))
    (hl : l ∈ D.ids) (hlr : (D.block l).round = n + 1)
    (hlc : (D.block l).creator ∈ (Correct : Finset Validator))
    (hk : n + 1 < k) (hcom : dec (n + 1) = Verdict.commit l) :
    b ∈ linearise (histOf D) (commitSeq dec k) :=
  theorem26_of_synchronised hsync hR hb hbr hbc hl hlr hlc (fun _ h => mem_histOf hl h) hk hcom

end Validity

/-! ## The two theorems, end to end -/

section Capstone

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {Payload : Type*} {D : Dag Validator BlockId Payload}

/-- **Theorem 26 (Validity), end to end.** A correct validator's block is
delivered, given the pacing line and a correct leader one round above it.
The leader's slot being committed is derived here rather than assumed:
coverage commits it (Lemma 20), and `hsees` is what puts that commit in
the deciding validator's view. -/
theorem delivered_of_viewPace {U : BlockUniverse Validator BlockId Payload} {N R : ℕ}
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hgst : vp.gst ≤ R) (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    {dc : ℕ → BlockId → Prop} {ds : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec : ℕ → Verdict BlockId}
    (hwf : WellFormed dc ds choose dec)
    (hsees : ∀ r l, l ∈ slotBlocks D r → DirectCommit D l → dc r l)
    {hist : BlockId → List BlockId} {n k : ℕ} (hR : R ≤ n) (hk : n + 1 < k) (hkN : n + 3 ≤ N)
    {b l : BlockId} (hb : b ∈ D.ids) (hbr : (D.block b).round = n)
    (hbc : (D.block b).creator ∈ (Correct : Finset Validator))
    (hl : l ∈ D.ids) (hlr : (D.block l).round = n + 1)
    (hlead : (D.block l).creator = D.leader (n + 1))
    (hlc : (D.block l).creator ∈ (Correct : Finset Validator))
    (hhist : ∀ c, ReachesFrom D.block l c → c ∈ hist l) :
    b ∈ linearise hist (commitSeq dec k) := by
  have hsync := synchronised_of_viewPace vp hids hblk hgst hbackoff
  have hpop := populated_of_viewPace vp hids hblk
  have hslot : l ∈ slotBlocks D (n + 1) := by
    simp only [slotBlocks, blocksAt, Finset.mem_filter]
    exact ⟨⟨hl, hlr⟩, hlead⟩
  have hcom : DirectCommit D l :=
    Or.inr (lemma20 hsync (show R ≤ n + 1 by omega) (hpop (n + 2) (by omega))
      (hpop (n + 3) (by omega)) hl hlr hlc)
  exact theorem26_of_synchronised hsync hR hb hbr hbc hl hlr hlc hhist hk
    (hwf.direct_commit _ _ (hsees _ _ hslot hcom))

/-- **Theorem 24 (Agreement), end to end.** Two validators of one DAG
deliver the same sequence at every horizon the DAG supports.

Both halves are consumed here: Lemma 12 makes the verdicts agree wherever
both are decided, and Lemma 23 makes them decided. The two finiteness
conditions are compatible rather than contradictory — `hbound` says
nothing above `M` is decided, `hkN` places the horizon well below the
DAG's own, and a DAG that reaches `N` decides everything up to about
`N − 3f`. -/
theorem agreement_of_viewPace {U : BlockUniverse Validator BlockId Payload} {N R : ℕ}
    (vp : ViewPace U (Correct : Finset Validator) N)
    (hids : D.ids = U.ids) (hblk : D.block = U.block)
    (hgst : vp.gst ≤ R) (hbackoff : ∀ n, R ≤ n → 2 * vp.delay + vp.proc ≤ vp.timeout n)
    (hrr : RoundRobin D.leader)
    {dc dc' : ℕ → BlockId → Prop} {ds ds' : ℕ → Prop}
    {choose : BlockId → ℕ → Option BlockId} {dec dec' : ℕ → Verdict BlockId}
    (hwf : WellFormed dc ds choose dec) (hwf' : WellFormed dc' ds' choose dec')
    (hch : ChooseSound D choose)
    (hdc : ∀ r l, dc r l → l ∈ slotBlocks D r ∧ DirectCommit D l)
    (hdc' : ∀ r l, dc' r l → l ∈ slotBlocks D r ∧ DirectCommit D l)
    (hds : ∀ r, ds r → DirectSkip D r) (hds' : ∀ r, ds' r → DirectSkip D r)
    (hsees : ∀ r l, r + 2 ≤ N → l ∈ slotBlocks D r → DirectCommit D l → dc r l)
    (hsees' : ∀ r l, r + 2 ≤ N → l ∈ slotBlocks D r → DirectCommit D l → dc' r l)
    (hslot : ∀ r A, dec r = Verdict.commit A → A ∈ slotBlocks D r)
    (hslot' : ∀ r A, dec' r = Verdict.commit A → A ∈ slotBlocks D r)
    {M : ℕ} (hbound : ∀ s, M ≤ s → dec s = Verdict.undecided ∧ dec' s = Verdict.undecided)
    {k : ℕ} (hkN : max k R + (3 * F.f + 5) ≤ N)
    (hist : BlockId → List BlockId) :
    linearise hist (commitSeq dec k) = linearise hist (commitSeq dec' k) := by
  have hsync := synchronised_of_viewPace vp hids hblk hgst hbackoff
  have hpop := populated_of_viewPace vp hids hblk
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
    (fun s hs => all_decided hwf hsees hsync hpop hrr (by
      have : max s R ≤ max k R := max_le_max (by omega) le_rfl
      omega))
    (fun s hs => all_decided hwf' hsees' hsync hpop hrr (by
      have : max s R ≤ max k R := max_le_max (by omega) le_rfl
      omega))
    hist

end Capstone

end FinWhale

end LeanDag
