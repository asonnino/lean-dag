import LeanDag.Hybrid.Checkpoint.Safety

/-!
# Authenticated broadcast and implemented recovery selection

The broadcast contract contains only authentication, agreement, and
delivery of actual concrete certificate payloads from correct senders.
Recovery handlers submit recorded certificates and separately validate
delivered signer evidence.  Selection is the maximum element of the
finite validated set, with checkpoint ordering led by height; the
supplied genesis is returned for an empty set.

`RecoveryCorrect` membership alone is not a recovery protocol.  The
results below additionally assume correct certificate submission,
authenticated broadcast, local validation, deterministic selection, and
adoption of the selected history as the next epoch's genesis.  They
recover checkpoint state, not the discarded DAG or its runtime state.
-/

namespace LeanDag.Hybrid.Checkpoint

variable {Validator Value : Type*}
variable [Fintype Validator] [DecidableEq Validator]
variable [H : HybridFaults Validator]

namespace Model

variable (M : Model Validator Value)

namespace Execution

variable (E : M.Execution Value)

/-- The Dolev--Strong-style contract used by recovery.  It says nothing
about checkpoint validity or local certificate storage. -/
structure AuthenticatedBroadcast where
  /-- Authenticated protocol inputs, indexed by sender and payload. -/
  input : Validator →
    CertificatePayload (Validator := Validator) (Value := Value) → Prop
  /-- Messages delivered to a recipient with their authenticated sender. -/
  delivered : Validator → Validator →
    CertificatePayload (Validator := Validator) (Value := Value) → Prop
  /-- A delivered message was an actual input by its claimed sender. -/
  integrity :
    ∀ {receiver sender payload},
      delivered receiver sender payload → input sender payload
  /-- Correct recipients agree on every authenticated delivery. -/
  agreement :
    ∀ {v w}, v ∈ M.RecoveryCorrect → w ∈ M.RecoveryCorrect →
      ∀ sender payload,
        delivered v sender payload ↔ delivered w sender payload
  /-- An actual input from a correct sender reaches every correct
  recipient. -/
  delivery :
    ∀ {sender receiver payload},
      sender ∈ M.RecoveryCorrect → receiver ∈ M.RecoveryCorrect →
      input sender payload → delivered receiver sender payload

/-- Explicit local validation for a delivered recovery payload.  The
closing epoch check rejects stale and future certificates; `Valid`
checks quorum size and every concrete signer proposal. -/
def validateCertificate (epoch : ℕ)
    (payload : CertificatePayload (Validator := Validator) (Value := Value)) :
    Prop :=
  payload.checkpoint.epoch = epoch ∧
    CertificatePayload.Valid M E payload

/-- Validation soundness is constructive: accepted wire evidence
directly builds the corresponding checkpoint QC. -/
theorem validateCertificate_sound {epoch : ℕ}
    {payload : CertificatePayload (Validator := Validator) (Value := Value)}
    (valid : validateCertificate (M := M) (E := E) epoch payload) :
    Nonempty (Model.Execution.CheckpointQC M E payload.checkpoint) :=
  ⟨CertificatePayload.toCheckpointQC M E payload valid.2⟩

/-- Recovery-handler state separates protocol submission and local
certificate validation from the broadcast channel. -/
structure RecoveryRound (B : AuthenticatedBroadcast M) (epoch : ℕ) where
  /-- Finite set of checkpoint contents parsed and validated locally. -/
  validated : Validator → Finset (CheckpointData Value)
  /-- A correct handler inputs a concrete valid payload for every
  checkpoint certificate it recorded.  This is the assumed correct
  recovery submission behavior. -/
  submits_recorded :
    ∀ {sender checkpoint}, sender ∈ M.RecoveryCorrect →
      E.recorded sender checkpoint →
      ∃ payload, payload.checkpoint = checkpoint ∧
        validateCertificate (M := M) (E := E) epoch payload ∧
          B.input sender payload
  /-- The finite handler state contains exactly checkpoint contents of
  delivered payloads accepted by the explicit local verifier. -/
  validated_spec :
    ∀ {receiver checkpoint}, checkpoint ∈ validated receiver ↔
      ∃ sender payload, B.delivered receiver sender payload ∧
        validateCertificate (M := M) (E := E) epoch payload ∧
        payload.checkpoint = checkpoint

namespace RecoveryRound

variable {B : AuthenticatedBroadcast M} {epoch : ℕ}
variable (R : RecoveryRound M E B epoch)

/-- Correct recipients obtain identical finite validated checkpoint
sets from broadcast agreement and deterministic local verification. -/
theorem validated_agreement {v w : Validator}
    (hv : v ∈ M.RecoveryCorrect) (hw : w ∈ M.RecoveryCorrect) :
    R.validated v = R.validated w := by
  ext checkpoint
  rw [R.validated_spec, R.validated_spec]
  constructor
  · rintro ⟨sender, payload, hd, hvalid, heq⟩
    exact ⟨sender, payload, (B.agreement hv hw sender payload).mp hd,
      hvalid, heq⟩
  · rintro ⟨sender, payload, hd, hvalid, heq⟩
    exact ⟨sender, payload, (B.agreement hv hw sender payload).mpr hd,
      hvalid, heq⟩

/-- Membership in the validated set yields both a genuine checkpoint QC
and the round's closing epoch. -/
theorem validated_sound {receiver : Validator}
    {checkpoint : CheckpointData Value}
    (member : checkpoint ∈ R.validated receiver) :
    Nonempty (Model.Execution.CheckpointQC M E checkpoint) ∧
      checkpoint.epoch = epoch := by
  obtain ⟨sender, payload, delivered, valid, rfl⟩ :=
    R.validated_spec.mp member
  exact ⟨validateCertificate_sound M E valid, valid.1⟩

/-- A checkpoint is highest in a finite set when it belongs to the set
and no member has greater height. -/
def IsHighest (s : Finset (CheckpointData Value))
    (checkpoint : CheckpointData Value) :
    Prop :=
  checkpoint ∈ s ∧ ∀ other ∈ s, other.height ≤ checkpoint.height

/-- Every nonempty finite checkpoint set has a highest member. -/
theorem exists_highest {s : Finset (CheckpointData Value)} (hs : s.Nonempty) :
    ∃ checkpoint, IsHighest s checkpoint := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert checkpoint s hnot ih =>
      by_cases hse : s.Nonempty
      · obtain ⟨best, hbest, hmax⟩ := ih hse
        by_cases hle : checkpoint.height ≤ best.height
        · exact ⟨best, by
            refine ⟨Finset.mem_insert_of_mem hbest, ?_⟩
            intro other ho
            rcases Finset.mem_insert.mp ho with rfl | ho
            · exact hle
            · exact hmax other ho⟩
        · exact ⟨checkpoint, by
            refine ⟨Finset.mem_insert_self _ _, ?_⟩
            intro other ho
            rcases Finset.mem_insert.mp ho with rfl | ho
            · exact le_rfl
            · exact le_trans (hmax other ho) (Nat.le_of_lt (lt_of_not_ge hle))⟩
      · exact ⟨checkpoint, by
          refine ⟨Finset.mem_insert_self _ _, ?_⟩
          intro other ho
          rcases Finset.mem_insert.mp ho with rfl | ho
          · exact le_rfl
          · exact (hse ⟨other, ho⟩).elim⟩

/-- Highest-checkpoint selection is a function over the finite validated
set, returning the explicit epoch genesis in the empty case.  Classical
choice selects a maximum witness; same-height uniqueness below proves
that the result is independent of that choice. -/
noncomputable def select (genesis : CheckpointData Value) (receiver : Validator) :
    CheckpointData Value :=
  if hs : (R.validated receiver).Nonempty then
    Classical.choose (exists_highest hs)
  else genesis

/-- The nonempty selection satisfies membership and maximality. -/
theorem select_spec {genesis : CheckpointData Value} {receiver : Validator}
    (hs : (R.validated receiver).Nonempty) :
    IsHighest (R.validated receiver) (select M E R genesis receiver) := by
  simp only [select, dif_pos hs]
  exact Classical.choose_spec (exists_highest hs)

/-- Nonempty selection is one of the locally validated checkpoints. -/
theorem select_mem {genesis : CheckpointData Value} {receiver : Validator}
    (hs : (R.validated receiver).Nonempty) :
    select M E R genesis receiver ∈ R.validated receiver := by
  exact (select_spec M E R hs).1

/-- The selected checkpoint has maximum height among all validated
checkpoints. -/
theorem height_le_select {genesis : CheckpointData Value}
    {receiver : Validator} (hs : (R.validated receiver).Nonempty)
    {checkpoint : CheckpointData Value}
    (hc : checkpoint ∈ R.validated receiver) :
    checkpoint.height ≤ (select M E R genesis receiver).height := by
  exact (select_spec M E R hs).2 checkpoint hc

/-- Equal-height validated candidates are equal.  Thus the
implementation's tie result is unique independently of set ordering. -/
theorem eq_of_validated_height {receiver : Validator}
    {x y : CheckpointData Value}
    (hx : x ∈ R.validated receiver) (hy : y ∈ R.validated receiver)
    (hh : x.height = y.height) : x = y := by
  obtain ⟨⟨QX⟩, hex⟩ := validated_sound M E R hx
  obtain ⟨⟨QY⟩, hey⟩ := validated_sound M E R hy
  exact checkpointQC_eq_of_same_height M E QX QY
    (hex.trans hey.symm) hh

/-- Correct recipients deterministically select the same recovery
checkpoint, including the explicit empty-set case. -/
theorem selection_agreement (genesis : CheckpointData Value) {v w : Validator}
    (hv : v ∈ M.RecoveryCorrect) (hw : w ∈ M.RecoveryCorrect) :
    select M E R genesis v = select M E R genesis w := by
  have hagree := validated_agreement M E R hv hw
  by_cases hs : (R.validated v).Nonempty
  · have hsw : (R.validated w).Nonempty := by
      obtain ⟨checkpoint, hc⟩ := hs
      exact ⟨checkpoint, by simpa [← hagree] using hc⟩
    have hsv := select_mem M E R
      (genesis := genesis) (receiver := v) hs
    have hswm := select_mem M E R
      (genesis := genesis) (receiver := w) hsw
    apply eq_of_validated_height M E R hsv
      (by simpa [← hagree] using hswm)
    apply Nat.le_antisymm
    · exact height_le_select M E R hsw
        (by simpa [← hagree] using hsv)
    · exact height_le_select M E R hs
        (by simpa [← hagree] using hswm)
  · have hsw : ¬(R.validated w).Nonempty := by
      intro hn
      obtain ⟨checkpoint, hc⟩ := hn
      exact hs ⟨checkpoint, by simpa [hagree] using hc⟩
    simp [select, hs, hsw]

/-- Every validated checkpoint is a prefix of the selected maximum. -/
theorem validated_prefix_select {genesis : CheckpointData Value}
    {receiver : Validator} (hs : (R.validated receiver).Nonempty)
    {checkpoint : CheckpointData Value}
    (hc : checkpoint ∈ R.validated receiver) :
    checkpoint.history.IsPrefix
      (select M E R genesis receiver).history := by
  have hm := select_mem M E R (genesis := genesis) hs
  obtain ⟨⟨QS⟩, hes⟩ := validated_sound M E R hm
  obtain ⟨⟨QC⟩, hec⟩ := validated_sound M E R hc
  exact checkpointQC_prefix M E QC QS
    (hec.trans hes.symm)
    (height_le_select M E R hs hc)

/-- A checkpoint recorded by a recovery-correct handler enters every
correct recipient's validated set through protocol submission,
broadcast delivery, and local certificate validation. -/
theorem recorded_mem_validated {sender receiver : Validator}
    (hs : sender ∈ M.RecoveryCorrect)
    (hr : receiver ∈ M.RecoveryCorrect)
    {checkpoint : CheckpointData Value}
    (hrecorded : E.recorded sender checkpoint) :
    checkpoint ∈ R.validated receiver := by
  obtain ⟨payload, heq, hvalid, hin⟩ :=
    R.submits_recorded hs hrecorded
  have hdel := B.delivery hs hr hin
  exact R.validated_spec.mpr
    ⟨sender, payload, hdel, hvalid, heq⟩

/-- Highest-checkpoint recovery preserves every checkpoint recorded by
a recovery-correct participant, not only those later finalized. -/
theorem recovery_preserves_recorded {genesis : CheckpointData Value}
    {sender receiver : Validator}
    (hs : sender ∈ M.RecoveryCorrect)
    (hr : receiver ∈ M.RecoveryCorrect)
    {checkpoint : CheckpointData Value}
    (hrecorded : E.recorded sender checkpoint) :
    checkpoint.history.IsPrefix
      (select M E R genesis receiver).history := by
  have hm := recorded_mem_validated M E R hs hr hrecorded
  exact validated_prefix_select M E R ⟨checkpoint, hm⟩ hm

/-- A previously finalized checkpoint is included in every correct
recipient's validated set.  This derives protocol submission, broadcast
delivery, and local validation in three separate steps. -/
theorem finalized_mem_validated {receiver : Validator}
    (hr : receiver ∈ M.RecoveryCorrect) {checkpoint : CheckpointData Value}
    (F : Model.Execution.FinalityQC M E checkpoint) :
    checkpoint ∈ R.validated receiver := by
  obtain ⟨sender, hs, hrec⟩ :=
    exists_recoveryCorrect_recorder M E F
  obtain ⟨payload, heq, hvalid, hin⟩ :=
    R.submits_recorded hs hrec
  have hdel := B.delivery hs hr hin
  exact R.validated_spec.mpr
    ⟨sender, payload, hdel, hvalid, heq⟩

/-- Highest-checkpoint recovery preserves every checkpoint finalized in
the closing epoch. -/
theorem recovery_preserves_finality {genesis : CheckpointData Value}
    {receiver : Validator} (hr : receiver ∈ M.RecoveryCorrect)
    {checkpoint : CheckpointData Value}
    (F : Model.Execution.FinalityQC M E checkpoint) :
    checkpoint.history.IsPrefix
      (select M E R genesis receiver).history := by
  have hm := finalized_mem_validated M E R hr F
  exact validated_prefix_select M E R ⟨checkpoint, hm⟩ hm

/-- A recovery transition connects the selected output to the genesis
used by the next epoch's signing state. -/
structure EpochTransition (genesis : CheckpointData Value)
    (receiver : Validator) where
  /-- The receiver follows the recovery protocol. -/
  receiver_correct : receiver ∈ M.RecoveryCorrect
  /-- The next epoch is the successor of the closing epoch. -/
  next_epoch : ℕ
  /-- Epoch numbering advances once. -/
  next_epoch_eq : next_epoch = epoch + 1
  /-- Subsequent checkpoint state starts from the selected history. -/
  adopted :
    E.genesis next_epoch = (select M E R genesis receiver).history

/-- A finalized checkpoint remains a prefix of the genesis adopted by
the concrete recovery transition. -/
theorem finalized_prefix_next_genesis {genesis : CheckpointData Value}
    {receiver : Validator}
    (T : EpochTransition M E R genesis receiver)
    {checkpoint : CheckpointData Value}
    (F : Model.Execution.FinalityQC M E checkpoint) :
    checkpoint.history.IsPrefix (E.genesis T.next_epoch) := by
  rw [T.adopted]
  exact recovery_preserves_finality M E R T.receiver_correct F

/-- Subsequent checkpoint signing preserves finalized pre-recovery
state: the selected history becomes the next genesis, and every
reliable signer extends that genesis before emitting a new checkpoint. -/
theorem finalized_prefix_next_checkpoint {genesis : CheckpointData Value}
    {receiver : Validator}
    (T : EpochTransition M E R genesis receiver)
    {old new : CheckpointData Value}
    (F : Model.Execution.FinalityQC M E old)
    (Q : Model.Execution.CheckpointQC M E new)
    (hne : new.epoch = T.next_epoch) :
    old.history.IsPrefix new.history := by
  obtain ⟨v, hv, hgood⟩ :=
    M.exists_reliableSigner_mem_inter Q.quorum Q.quorum
  have hem := Q.messages v (Finset.mem_inter.mp hv).1
  have hg := E.genesis_prefix hem hgood
  have hold := finalized_prefix_next_genesis M E R T F
  exact hold.trans (by simpa [hne] using hg)

end RecoveryRound

end Execution

end Model

end LeanDag.Hybrid.Checkpoint
