import LeanDag.GC.Chop
import LeanDag.DoS.Exclusion

/-!
# The attested base: the inexact certificate

`garbage.md` §6, **G10**. A joining validator cannot fetch the pruned
prefix; it adopts the new genesis layer from others. Correct presenters
never agree block-for-block — their layers share the correct core exactly
but differ in Byzantine fringe — so the certificate is *inexact*, filtered
per block: **attest the layer, keep what `f+1` distinct authors attest.**

No signatures: in this model a validator's attestation *is its block* —
its cone is its objective (D13), unforgeable statement of what the layer
contains — so the certificate is DAG-internal and decidable, and
equivocating attesters are neutered by counting distinct authors.

The sandwich, in two halves:

* **soundness** (`exists_correct_attester_of_mem_base`): everything in the
  base has a correct attester, hence lies in a correct cone — `f+1`
  authors always include a correct one;
* **completeness** (`correct_mem_base`): post-`R`, every correct block of
  the layer is attested by *every* correct author with a round-`t` block
  (the backbone), so nothing of the shared correct layer can be filtered
  out — by anyone.

Bases at different attestation samples differ only in fringe, and the
verdict machinery above the cut never reads the difference (G2): inexact
certificates, exact decisions.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {t G : ℕ} {y : BlockId}

/-- The authors attesting `y` at round `t`: those with a round-`t` block
whose cone holds `y`. An author's block *is* its attestation. -/
def attesters (U : BlockUniverse Validator BlockId Payload) (t : ℕ)
    (y : BlockId) : Finset Validator :=
  creatorsOf U.block ((blocksAt U t).filter fun a => y ∈ history U a)

theorem mem_attesters {v : Validator} :
    v ∈ attesters U t y ↔
      ∃ a ∈ U.ids, (U.block a).round = t ∧ y ∈ history U a ∧
        (U.block a).creator = v := by
  unfold attesters
  simp only [mem_creatorsOf, Finset.mem_filter, mem_blocksAt]
  tauto

/-- **The inexact certificate**: the round-`G` blocks attested by more
than `f` distinct authors at round `t`. -/
def Base (U : BlockUniverse Validator BlockId Payload) (t G : ℕ) :
    Finset BlockId :=
  (blocksAt U G).filter fun y => F.f + 1 ≤ (attesters U t y).card

theorem mem_base :
    y ∈ Base U t G ↔
      (y ∈ U.ids ∧ (U.block y).round = G) ∧
        F.f + 1 ≤ (attesters U t y).card := by
  unfold Base
  rw [Finset.mem_filter, mem_blocksAt]

/-- **G10, soundness.** Everything in the base has a correct attester —
`f+1` authors always include one — and so lies in a correct cone. The
adversary cannot smuggle fabrications into anyone's base. -/
theorem exists_correct_attester_of_mem_base (hy : y ∈ Base U t G) :
    ∃ a ∈ U.ids, (U.block a).round = t ∧
      (U.block a).creator ∈ (Correct : Finset Validator) ∧
      y ∈ history U a := by
  obtain ⟨-, hcard⟩ := mem_base.mp hy
  obtain ⟨v, hv, hvc⟩ := exists_correct_of_card hcard
  obtain ⟨a, ha, har, hya, hac⟩ := mem_attesters.mp hv
  exact ⟨a, ha, har, by rw [hac]; exact hvc, hya⟩

/-- **G10, completeness.** Post-`R`, every correct block of the layer is
in every correct attestation (the backbone), so it clears the `f+1` bar in
*every* sample — the shared correct layer `C` is in every base, and the
adversary cannot filter it out. -/
theorem correct_mem_base {R : ℕ} (hs : Synchronised U R) (hR : R ≤ G)
    (hGt : G < t) (hpop : Populated U t) (hy : y ∈ U.ids)
    (hyr : (U.block y).round = G)
    (hyc : (U.block y).creator ∈ (Correct : Finset Validator)) :
    y ∈ Base U t G := by
  refine mem_base.mpr ⟨⟨hy, hyr⟩, ?_⟩
  have hsub : (Correct : Finset Validator) ⊆ attesters U t y := by
    intro w hw
    obtain ⟨a, ha, hac, har⟩ := hpop w hw
    refine mem_attesters.mpr ⟨a, ha, har, ?_, hac⟩
    exact mem_history_of_correct hs (t - G - 1) a ha y hy
      (by rw [hac]; exact hw) hyc (by omega) (by omega)
  have h2 := two_f_add_one_le_card_correct (Validator := Validator)
  have := Finset.card_le_card hsub
  omega

end LeanDag
