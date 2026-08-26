import LeanDag.FinWhale.Propagation

/-!
# FinWhale — the direct decision rule, and how far Lemma 12 gets

Lemma 12 says two honest validators never decide a slot differently. Its
proof splits: either one of them decided **directly**, and the direct
rules exclude each other; or both decided **indirectly**, and the
argument is that by maximality they committed the same anchor, and the
same anchor gives the same decisions.

This file settles the first branch and states the second's requirement.

**The first branch is proved.** A direct commit, fast or slow, carries a
quorum of round-`(r+1)` voters — for the fast path by threshold, for the
slow path because an SP-certificate *references* that quorum
(`voters_of_spCommit`). One quorum of voters excludes another for a
conflicting block (Lemma 8), and excludes the SP-skip half of the skip
rule (Lemma 6). So `direct_commit_unique` and `no_directSkip_of_commit`
close every case where either validator decided directly, and neither
needs the FP-evidence half of the skip rule at all.

**The second branch is not.** It rests on the indirect rule being a
function of the anchor's causal history, which this arc does not model:
`AnchorDetermined` states it, `lemma12_of_anchorDetermined` shows Lemma
12 follows from it and the first branch, and nothing here discharges it.
That is the honest shape of the gap. It is also where the Black Marlin
arc found what it found — its commit rule was sound and its descent was
not — so the requirement is worth naming rather than absorbing.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- The blocks of the leader slot of round `r`. There may be several, if
the leader equivocates. -/
def slotBlocks (D : Dag Validator BlockId Payload) (r : ℕ) : Finset BlockId :=
  (blocksAt D r).filter (fun b => (D.block b).creator = D.leader r)

/-- **The slow-path direct commit**: a quorum of SP-certificates from
distinct validators at round `r + 2`. -/
def SPCommit (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  ∃ certs : Finset Validator, spQuorum Validator ≤ certs.card ∧
    ∀ v ∈ certs, ∃ b ∈ blocksAt D ((D.block l).round + 2),
      (D.block b).creator = v ∧ SPCertificate D b l

/-- **The direct commit rule**: either path. -/
def DirectCommit (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  FastCommit D l ∨ SPCommit D l

/-- **The direct skip rule**: an SP-skip pattern at every block of the
slot, and a quorum of Non-FP-evidence blocks at round `r + 2`. -/
def DirectSkip (D : Dag Validator BlockId Payload) (r : ℕ) : Prop :=
  (∀ l ∈ slotBlocks D r, SPSkip D l) ∧
    ∃ nonev : Finset Validator, spQuorum Validator ≤ nonev.card ∧
      ∀ v ∈ nonev, ∃ b ∈ blocksAt D (r + 2),
        (D.block b).creator = v ∧ NonFPEvidence D b (slotBlocks D r)

/-- **An SP-certificate exhibits the voters it certifies.** Its parents
voting for `l` are round-`(r+1)` blocks referencing `l`, so a certificate
carries a quorum of voters with it. -/
theorem voters_of_spCertificate {b l : BlockId} (hb : b ∈ D.ids)
    (hround : (D.block b).round = (D.block l).round + 2)
    (hcert : SPCertificate D b l) :
    spQuorum Validator ≤ (voters D l).card := by
  refine le_trans hcert (Finset.card_le_card ?_)
  intro v hv
  simp only [parentsVoting, mem_creatorsOf, Finset.mem_filter] at hv
  obtain ⟨q, ⟨hq, hqref⟩, hqv⟩ := hv
  have hqids : q ∈ D.ids := D.complete b hb q hq
  have hqround : (D.block q).round = (D.block l).round + 1 := by
    have := parent_round hb hq; omega
  refine mem_creatorsOf.2 ⟨q, ?_, hqv⟩
  rw [Finset.mem_filter]
  exact ⟨by rw [blocksAt, Finset.mem_filter]; exact ⟨hqids, hqround⟩, hqref⟩

/-- **Every direct commit carries a quorum of voters.** The fast path by
its threshold, the slow path through its certificates. -/
theorem voters_of_directCommit {l : BlockId} (hcom : DirectCommit D l) :
    spQuorum Validator ≤ (voters D l).card := by
  rcases hcom with hfast | ⟨certs, hcard, hcerts⟩
  · exact spQuorum_le_of_fastCommit hfast
  · have hpos : 0 < certs.card := by
      have := params_arith (Validator := Validator)
      simp only [spQuorum] at hcard; omega
    obtain ⟨v, hv⟩ := Finset.card_pos.1 hpos
    obtain ⟨b, hb, -, hcert⟩ := hcerts v hv
    simp only [blocksAt, Finset.mem_filter] at hb
    exact voters_of_spCertificate hb.1 hb.2 hcert

/-- **Corollary 11, the direct half.** Two blocks of one slot cannot both
be directly committed. -/
theorem direct_commit_unique {r : ℕ} {l l' : BlockId}
    (hl : l ∈ slotBlocks D r) (hl' : l' ∈ slotBlocks D r)
    (hcom : DirectCommit D l) (hcom' : DirectCommit D l') : l = l' := by
  by_contra hne
  simp only [slotBlocks, blocksAt, Finset.mem_filter] at hl hl'
  exact lemma8 hl.1.1 ⟨hne, by rw [hl.1.2, hl'.1.2], by rw [hl.2, hl'.2]⟩
    (voters_of_directCommit hcom) (voters_of_directCommit hcom')

/-- **Lemma 6 and Lemma 7, the direct half.** A slot with a directly
committed block is not directly skipped. The SP-skip half of the rule is
already unsatisfiable, so the FP-evidence half is not needed. -/
theorem no_directSkip_of_commit {r : ℕ} {l : BlockId}
    (hl : l ∈ slotBlocks D r) (hcom : DirectCommit D l) : ¬ DirectSkip D r := by
  rintro ⟨hskip, -⟩
  exact no_skip_of_quorum (voters_of_directCommit hcom) (hskip l hl)

/-- **Lemma 12, the direct branch.** Where either validator decided the
slot directly, the two decisions agree: the committed block is unique and
the slot is not skipped.

The indirect branch is not here, and stating what it would need is more
useful than a definition that proves itself. The paper argues that two
validators deciding indirectly do so from anchors that are the *same
block* — by maximality of the disagreeing round, their decisions agree
above it, so the anchors they commit are one block by Corollary 11 at the
anchor's round — and that the same anchor yields the same decision, since
the decision reads only its causal history.

Neither half is available in this model. The reverse pass that picks an
anchor is not modelled, so "the anchors are the same block" has nothing
to be proved from; and with no anchor recursion there is no `decide` to
show reads only the history. Both are what `Model/Rule.lean` would have
to grow for Lemma 12 to close, and on the Black Marlin precedent — a
sound commit rule and an unsound descent — that recursion is where the
remaining risk sits. -/
theorem lemma12_direct {r : ℕ} {l l' : BlockId}
    (hl : l ∈ slotBlocks D r) (hl' : l' ∈ slotBlocks D r)
    (hcom : DirectCommit D l) (hcom' : DirectCommit D l') :
    l = l' ∧ ¬ DirectSkip D r :=
  ⟨direct_commit_unique hl hl' hcom hcom', no_directSkip_of_commit hl hcom⟩

end FinWhale

end LeanDag
