import LeanDag.Quality.Coverage
import LeanDag.DoS.Exclusion

/-!
# Chain quality: post-synchrony inclusion

`chain-quality.md` §4, CQP2 — **CQ5**, **CQ6**. The aggregate coverage
of `Coverage.lean` upgrades to an *individual* guarantee — every correct
block enters the agreed ledger — at the price of the synchrony round
`R`, and only at that price: the witness file carries a model in which
commits recur for ever while the same correct validator is missing from
every flushed layer, so the upgrade is genuinely conditional, not a
proof gap.

The engine is the backbone (`mem_history_of_correct`): post-`R`, a
correct block is in the cone of every correct block at every later
round. Composition with commit recurrence (L6) then puts it in the
ledger, with the committing slot supplied by the fair schedule.

A scoping note, recorded in the design document: the schedule side is
`T ⊆ Correct`-relative, but the backbone consumes Correct-wide
coverage, so the theorems here take full `Synchronised U R`. A
`T`-relative variant would need a `T`-relative backbone lemma — possible
but not attempted in this arc.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]
variable {T : Finset Validator} {b L : BlockId} {R m : ℕ}

/-- **CQ5.** Post-`R`, every correct block is in the cone of **every**
committed leader block with a correct author at a later round — any
commit route, any view. The backbone does all the work. -/
theorem mem_history_of_decided_commit (hs : Synchronised U R)
    {V : View Validator BlockId Payload U} {k : ℕ}
    (hdec : Decided U V k (some L))
    (hLc : (U.block L).creator ∈ (Correct : Finset Validator))
    (hb : b ∈ U.ids) (hbc : (U.block b).creator ∈ (Correct : Finset Validator))
    (hR : R ≤ (U.block b).round)
    (hlt : (U.block b).round < (U.block L).round) :
    b ∈ history U L :=
  mem_history_of_correct hs ((U.block L).round - (U.block b).round - 1)
    L (isLeaderBlock_of_decided hdec).1 b hb hLc hbc hR (by omega)

/-- **A slot whose commit carries a whole round into the ledger.**

The conclusion CQ6 and its refinements share: in any sufficiently grown
synchronous execution, slot `k` commits a leader whose history contains
every correct round-`m` block, and every such block is in the agreed
ledger from any later position. Naming it keeps the quantifier order
visible — `k` is fixed by the schedule before an execution is named — as
`CommitsAt` does for the recurrence results. -/
def IncludesAt (BlockId : Type*) [DecidableEq BlockId] (Payload : Type*)
    [S : Slots Validator] (R m k : ℕ) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (N : ℕ),
    (∀ r ≤ N, Populated U r) → Synchronised U R →
    S.slotRound k + 2 ≤ N →
    ∃ L, Decided U (View.full U) k (some L) ∧
      ∀ b ∈ U.ids,
        (U.block b).creator ∈ (Correct : Finset Validator) →
        (U.block b).round = m →
        b ∈ history U L ∧
        ∀ (g : ℕ → Option BlockId) (n : ℕ), g k = some L → k < n →
          b ∈ ledgerSet U g n

/-- **CQ6 (inclusion liveness).** Under a fair schedule over reliable
validators and post-`R` synchrony, for every round `m ≥ R` there is a
committed slot — above `m`, led by a correct validator — whose flush
contains **every** correct round-`m` block; hence every such block is
in the agreed ledger of any verdict assignment covering that slot.

The slot is produced *before* the universe is quantified, exactly as in
L6: the schedule fixes it, and any sufficiently grown synchronous DAG
then commits it. -/
theorem committed_of_correct_block (hT : T ⊆ (Correct : Finset Validator))
    (hcard : quorumCard Validator ≤ T.card)
    (fair : FairScheduleOn T) (R m : ℕ) (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k' := by
  obtain ⟨k₀, hk₀⟩ := S.unbounded R
  obtain ⟨k', hk', hlead⟩ := fair (max (slotAt Validator (m + 1)) k₀)
  have hRk' : R ≤ S.slotRound k' :=
    le_trans hk₀ (S.mono (le_trans (le_max_right _ _) hk'))
  have hm : m < S.slotRound k' := by
    have h1 := le_slotRound_slotAt (Validator := Validator) (m + 1)
    have h2 := S.mono (le_trans (le_max_left (slotAt Validator (m + 1)) k₀) hk')
    omega
  refine ⟨k', hm, hRk', ?_⟩
  intro U N hpop hs hN
  obtain ⟨L, hLb, hdec⟩ :=
    decided_of_leader_of_populated hT hcard (hs.mono hT) hRk'
      (fun r _ hr => PopulatedOn.mono hT (hpop r hr)) (by omega) hlead
  refine ⟨L, hdec, ?_⟩
  intro b hb hbc hbr
  have hLc : (U.block L).creator ∈ (Correct : Finset Validator) := by
    rw [hLb.2.2]
    exact hT hlead
  have hmem : b ∈ history U L :=
    mem_history_of_decided_commit hs hdec hLc hb hbc (by omega)
      (by rw [hLb.2.1]; omega)
  exact ⟨hmem, fun g n hg hn =>
    mem_ledgerSet_of_mem_history hg hn (isLeaderBlock_of_decided hdec).1 hmem⟩

/-- **CQ6 at `T := Correct`.** -/
theorem committed_of_correct_block_correct
    (fair : FairScheduleOn (Correct : Finset Validator)) (R m : ℕ)
    (hRm : R ≤ m) :
    ∃ k', m < S.slotRound k' ∧ R ≤ S.slotRound k' ∧
      IncludesAt (Validator := Validator) BlockId Payload R m k' :=
  committed_of_correct_block Finset.Subset.rfl card_correct fair R m hRm

end LeanDag
