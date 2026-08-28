import LeanDag.Adaptive.Policy
import LeanDag.Mysticeti

/-!
# The adaptive run, and safety as uniqueness of the fixpoint

An `AdaptiveRun` is a schedule-and-verdict pair coherent with a policy:
every slot's verdict is derivable with anchors inside its epoch window,
against the schedule the policy computes from the verdicts themselves.
Existence and uniqueness are deliberately separated, mirroring the base
development's split between the `Decided` relation and `decided_unique`:
**uniqueness is the safety theorem, existence is the liveness theorem.**

The safety argument (`adaptiveRun_agree`) is a strong induction on
epochs in which nothing about counting is ever re-proved. At epoch `e`
the verdict prefixes of both runs agree below by hypothesis, so
`adapted` forces the two assignments to agree through epoch `e + 1`, so
`decidedWithin_congr` places both runs' epoch-`e` derivations in the
*same* `Slots` instance — where agreement is M6, through the embedding.
The theorem carries **no fairness, synchrony or view hypothesis of any
kind**: adaptivity is safe unconditionally, for arbitrary — even
adversarial — adapted policies, and only liveness prices the policy's
choices.

The induction is stated over *partial* runs — closed up to an epoch
height — so that two validators that have not decided equally far agree
on their common prefix; total runs are the special case at every height.
Conservativity (`AdaptivePolicy.const_run_decided`) anchors the
definitions: under the constant policy a run's verdicts are ordinary
`Decided` verdicts of the base schedule.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator]

/-- A run closed up to epoch height `E`: verdicts derived for every slot
of epochs `< E`, the schedule coherent as far as those derivations read
it (epochs `< E + 1`). What a validator holds mid-execution. -/
structure PartialRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) (E : ℕ) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot of a closed epoch is decided inside its window: anchors
  strictly below the start of epoch `e + 2`. -/
  closed : ∀ k, epochOf P.W k < E →
    DecidedWithin (S := slotsOf P.inj assign) U V
      (P.W * (epochOf P.W k + 2)) k (vdct k)
  /-- The assignment is the policy's, computed on this view, as far as
  the derivations read it. -/
  coherent : ∀ m, epochOf P.W m < E + 1 → assign m = P.pick U V vdct m

/-- A total run: the adaptive fixpoint itself. -/
structure AdaptiveRun (P : AdaptivePolicy Validator BlockId Payload)
    (U : BlockUniverse Validator BlockId Payload)
    (V : View Validator BlockId Payload U) where
  /-- The leader assignment. -/
  assign : ℕ → Validator
  /-- The verdicts. -/
  vdct : ℕ → Option BlockId
  /-- Every slot is decided inside its epoch window. -/
  closed : ∀ k, DecidedWithin (S := slotsOf P.inj assign) U V
    (P.W * (epochOf P.W k + 2)) k (vdct k)
  /-- The assignment is the policy's, computed on this view, everywhere. -/
  coherent : ∀ m, assign m = P.pick U V vdct m

/-- A total run is partial at every height. -/
def AdaptiveRun.toPartial {P : AdaptivePolicy Validator BlockId Payload}
    {V : View Validator BlockId Payload U} (R : AdaptiveRun P U V) (E : ℕ) :
    PartialRun P U V E where
  assign := R.assign
  vdct := R.vdct
  closed := fun k _ => R.closed k
  coherent := fun m _ => R.coherent m

/-- **The master agreement lemma.** Two partial runs over one universe —
whatever views, each computing its schedule on its own, whatever heights
— agree on the verdicts of their common epochs and on the assignments
those verdicts determine.

The strong induction the module docstring describes: verdict agreement
below an epoch forces assignment agreement through the epoch above it
(`adapted`), which forces verdict agreement at the epoch itself
(`decidedWithin_congr`, then M6 through the embedding). -/
theorem partialRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U} {E₁ E₂ : ℕ}
    (R₁ : PartialRun P U V₁ E₁) (R₂ : PartialRun P U V₂ E₂) :
    ∀ k, epochOf P.W k < min E₁ E₂ → R₁.vdct k = R₂.vdct k := by
  -- Strong induction on the epoch of the slot.
  suffices main : ∀ e k, epochOf P.W k = e → epochOf P.W k < min E₁ E₂ →
      R₁.vdct k = R₂.vdct k by
    intro k hk; exact main _ k rfl hk
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ih =>
    intro k hke hk
    -- The assignments agree below this epoch's window.
    have hassign : ∀ m, m < P.W * (epochOf P.W k + 2) →
        R₁.assign m = R₂.assign m := by
      intro m hm
      have hme : epochOf P.W m < epochOf P.W k + 2 :=
        (epochOf_lt_iff P.W_pos).mpr hm
      rw [R₁.coherent m (by omega), R₂.coherent m (by omega)]
      refine P.adapted U V₁ V₂ R₁.vdct R₂.vdct m (fun j hj => ?_)
      exact ih (epochOf P.W j) (by omega) j rfl (by omega)
    -- Both derivations live in one instance; agreement is M6.
    have h₁ := R₁.closed k (by omega)
    have h₂ := R₂.closed k (by omega)
    exact DecidedWithin.agree (S := slotsOf P.inj R₂.assign)
      (decidedWithin_congr hassign h₁) h₂

/-- Assignments agree wherever the common verdicts determine them. -/
theorem partialRun_assign_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U} {E₁ E₂ : ℕ}
    (R₁ : PartialRun P U V₁ E₁) (R₂ : PartialRun P U V₂ E₂) :
    ∀ m, epochOf P.W m < min E₁ E₂ + 1 → R₁.assign m = R₂.assign m := by
  intro m hm
  rw [R₁.coherent m (by omega), R₂.coherent m (by omega)]
  refine P.adapted U V₁ V₂ R₁.vdct R₂.vdct m (fun j hj => ?_)
  exact partialRun_agree R₁ R₂ j (by omega)

/-- **Safety: the adaptive fixpoint is unique.** Two total runs over one
universe — derived from any two views, under no synchrony or fairness
hypothesis — hold the same verdicts and run the same schedule. Adaptive
validators cannot diverge, whatever the policy adapts to. -/
theorem adaptiveRun_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) :
    (∀ k, R₁.vdct k = R₂.vdct k) ∧ (∀ m, R₁.assign m = R₂.assign m) := by
  constructor
  · intro k
    exact partialRun_agree (R₁.toPartial (epochOf P.W k + 1))
      (R₂.toPartial (epochOf P.W k + 1)) k (by omega)
  · intro m
    exact partialRun_assign_agree (R₁.toPartial (epochOf P.W m + 1))
      (R₂.toPartial (epochOf P.W m + 1)) m (by omega)

/-- The verdict form of uniqueness, in the shape of M6. -/
theorem adaptive_decided_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) (k : ℕ) :
    R₁.vdct k = R₂.vdct k :=
  (adaptiveRun_agree R₁ R₂).1 k

/-- **The adaptive ledger is agreed** — M7's shape: the committed-leader
sequence read from any two runs' verdicts is the same list. -/
theorem adaptive_commitSeq_agree {P : AdaptivePolicy Validator BlockId Payload}
    {V₁ V₂ : View Validator BlockId Payload U}
    (R₁ : AdaptiveRun P U V₁) (R₂ : AdaptiveRun P U V₂) (n : ℕ) :
    commitSeq R₁.vdct n = commitSeq R₂.vdct n := by
  rw [funext (adaptiveRun_agree R₁ R₂).1]

namespace AdaptivePolicy

/-- **Conservativity.** Under the constant policy a run's verdicts are
ordinary `Decided` verdicts of the base schedule — the adaptive
development instantiates to the base one, per the house rule that a new
relation must collapse onto the old. With M6 this also pins each
`vdct k` to the unique base verdict. -/
theorem const_run_decided {W : ℕ} {hW : 0 < W}
    {hinj : Function.Injective S.slotRound}
    {V : View Validator BlockId Payload U}
    (R : AdaptiveRun (const (Validator := Validator) (BlockId := BlockId)
      (Payload := Payload) W hW hinj) U V) (k : ℕ) :
    Decided U V k (R.vdct k) := by
  have h := decidedWithin_congr (a₂ := S.leader)
    (fun m _ => R.coherent m) (R.closed k)
  rw [slotsOf_base hinj] at h
  exact h.toDecided

end AdaptivePolicy

end LeanDag
