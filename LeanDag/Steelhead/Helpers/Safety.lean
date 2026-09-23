import LeanDag.Steelhead.Safety.Statement
import LeanDag.Common.Anchored.Bounded
/-!
# Helpers — safety at any rule

Generated lemma infrastructure for `Safety/Statement.lean`; not part of
the audit surface. Agreement is the relation's `decided_unique`. The
handover asks the anchor's rungs for a verdict and reads it against the
direct commit, which a lawful rule allows only one way. Conservativity is
one induction on the derivation: two rules that read the same wave,
direct predicates, rungs and tie-break at every slot of a schedule derive
the same verdicts there, and a composite at a schedule of one kind reads
exactly the data of the rule of that kind.
-/

namespace LeanDag

namespace Steelhead

section Agree

variable {Validator : Type*} {BlockId : Type*} {Payload : Type*}
variable {P : Validity Validator BlockId Payload} {honest : Finset Validator}

/-- **Two rules that read the same data at every slot of a schedule decide alike there**: the
same wave, direct commit, direct skip, rungs and tie-break, each read at the slot it concerns. -/
theorem decided_of_agreeOn {R₁ R₂ : AnchoredRule Validator BlockId Payload P honest}
    {S : Slots Validator} (hw : ∀ k, R₁.waveAt (S.kind k) = R₂.waveAt (S.kind k))
    (hc : ∀ (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (L : BlockId) (k : ℕ),
      R₁.Commit U V L (S.slotRound k) (S.kind k) → R₂.Commit U V L (S.slotRound k) (S.kind k))
    (hs : ∀ (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (k : ℕ),
      R₁.Skip U V S k → R₂.Skip U V S k)
    (hl : ∀ (i : ℕ) (U : BlockRecord Validator BlockId Payload P honest) (A L : BlockId) (k : ℕ),
      R₁.Link i U A L S k ↔ R₂.Link i U A L S k)
    (hr : R₁.rungs = R₂.rungs) (ht : R₁.tie = R₂.tie)
    {U : BlockRecord Validator BlockId Payload P honest} {V : U.View} {k : ℕ}
    {v : Option BlockId} (h : R₁.Decided (S := S) U V k v) : R₂.Decided (S := S) U V k v := by
  have he : ∀ k j, R₁.Eligible (S := S) k j ↔ R₂.Eligible (S := S) k j := fun k j => by
    rw [AnchoredRule.eligible_iff, AnchoredRule.eligible_iff, hw k]
  induction h with
  | directCommit hL hc' => exact AnchoredRule.Decided.directCommit hL (hc _ _ _ _ hc')
  | directSkip hs' => exact AnchoredRule.Decided.directSkip (hs _ _ _ hs')
  | indirectCommit hkj helig _ _ hi hemp hL hlink hleast ihj ihmid =>
    refine AnchoredRule.Decided.indirectCommit hkj ((he _ _).mp helig) ihj
      (fun m h1 h2 h3 => ihmid m h1 h2 ((he _ _).mpr h3)) (by rw [← hr]; exact hi)
      (fun i' hi' L' hL' hl' => hemp i' hi' L' hL' ((hl _ _ _ _ _).mpr hl'))
      hL ((hl _ _ _ _ _).mp hlink) fun L' hL' hl' ht' => hleast L' hL' ((hl _ _ _ _ _).mpr hl') ?_
    rw [ht]
    exact ht'
  | indirectSkip hkj helig _ _ hnone ihj ihmid =>
    exact AnchoredRule.Decided.indirectSkip hkj ((he _ _).mp helig) ihj
      (fun m h1 h2 h3 => ihmid m h1 h2 ((he _ _).mpr h3))
      fun i hi L' hL' hl' => hnone i (by rw [hr]; exact hi) L' hL' ((hl _ _ _ _ _).mpr hl')

/-- **SH4.** At a schedule whose every slot has the kind `κ`, the composite reads every datum of a
slot from the rule of kind `κ`, and the rung count and tie-break agree across the family, so the
two derive the same verdicts. -/
theorem compose_decided_iff {rules : ℕ → AnchoredRule Validator BlockId Payload P honest} {κ : ℕ}
    (hr : ∀ r, (rules r).rungs = (rules 0).rungs) (ht : ∀ r, (rules r).tie = (rules 0).tie)
    {S : Slots Validator} (hkind : ∀ k, S.kind k = κ)
    {U : BlockRecord Validator BlockId Payload P honest} {V : U.View} {k : ℕ}
    {v : Option BlockId} :
    (compose rules).Decided (S := S) U V k v ↔ (rules κ).Decided (S := S) U V k v := by
  have hw : ∀ k, (compose rules).waveAt (S.kind k) = (rules κ).waveAt (S.kind k) := fun k => by
    change (rules (S.kind k)).waveAt (S.kind k) = _
    rw [hkind k]
  have hc : ∀ (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (L : BlockId)
      (k : ℕ), (compose rules).Commit U V L (S.slotRound k) (S.kind k) ↔
        (rules κ).Commit U V L (S.slotRound k) (S.kind k) := fun U V L k => by
    change (rules (S.kind k)).Commit U V L (S.slotRound k) (S.kind k) ↔ _
    rw [hkind k]
  have hs : ∀ (U : BlockRecord Validator BlockId Payload P honest) (V : U.View) (k : ℕ),
      (compose rules).Skip U V S k ↔ (rules κ).Skip U V S k := fun U V k => by
    change (rules (S.kind k)).Skip U V S k ↔ _
    rw [hkind k]
  have hl : ∀ (i : ℕ) (U : BlockRecord Validator BlockId Payload P honest) (A L : BlockId)
      (k : ℕ), (compose rules).Link i U A L S k ↔ (rules κ).Link i U A L S k :=
    fun i U A L k => by
      change (rules (S.kind k)).Link i U A L S k ↔ _
      rw [hkind k]
  have hrr : (compose rules).rungs = (rules κ).rungs := (hr κ).symm
  have htt : (compose rules).tie = (rules κ).tie := (ht κ).symm
  exact ⟨decided_of_agreeOn hw (fun U V L k => (hc U V L k).mp) (fun U V k => (hs U V k).mp) hl
      hrr htt,
    decided_of_agreeOn (fun k => (hw k).symm) (fun U V L k => (hc U V L k).mpr)
      (fun U V k => (hs U V k).mpr) (fun i U A L k => (hl i U A L k).symm) hrr.symm htt.symm⟩

end Agree

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type} [LinearOrder BlockId] {Payload : Type}
variable [S : Slots Validator] {R : AnchoredRule Validator BlockId Payload ValidWrt Correct}

/-- **SH3.** The anchor's rungs have a choice, so the anchor search gives the slot a verdict; a
lawful rule decides the slot one way, and the direct commit in the other view is a verdict, so
that one is the commit and no view skips the slot. -/
theorem handover {U : BlockUniverse Validator BlockId Payload} (hl : R.Laws)
    (hleast : LeastLinked R) {V₁ V₂ : View Validator BlockId Payload U} {k : ℕ} {L : BlockId}
    (hL : IsLeaderBlock U k L) (hc : R.Commit U V₁ L (S.slotRound k) (S.kind k)) :
    (∀ (j : ℕ) (A : BlockId),
      k < j → R.Eligible k j → R.Decided U V₂ j (some A) →
      (∀ m, k < m → m < j → R.Eligible k m → R.Decided U V₂ m none) →
      R.Decided U V₂ k (some L)) ∧
    ¬ R.Decided U V₂ k none := by
  have hd : R.Decided U V₁ k (some L) := AnchoredRule.Decided.directCommit hL hc
  refine ⟨fun j A _ helig hj hmid => ?_, fun hskip => ?_⟩
  · obtain ⟨v, hv⟩ :=
      AnchoredRule.exists_decided_of_anchor (fun hi h => hleast hi h) helig hj hmid
    have hvL := AnchoredRule.decided_agree hl trivial hd hv
    subst hvL
    exact hv
  · have := AnchoredRule.decided_agree hl trivial hd hskip
    simp at this

end Steelhead

end LeanDag
