import LeanDag.Adaptive.Basic

/-!
# The adaptive policy

The reassignment rule, packaged with the clauses it owes. `pick` maps
the universe and a verdict function to a leader assignment; `adapted` is
the measurability clause — the leader of slot `k` is a function of the
verdicts of epochs `≤ epochOf k − 2` and of nothing else — and it is the
whole of what safety will consume. The lag of two is the least that
makes the adaptive fixpoint well-founded: with lag one, the slots at the
top of an epoch would have no eligible anchors inside their window (see
`adaptive-leaders.md` §2).

`pick` receives the universe and the validator's own view of it, so
that a reputation rule may consult the committed blocks themselves —
certification patterns, payload contents — and not merely the verdict
vector. The view is what a validator actually has; nothing then makes
two validators agree, and nothing should — a rule reading its own view
freely could hand two correct validators different leaders. `adapted`
is what rules that out: the leader of a slot is a function of the
verdict prefix and of nothing else, the view included. That is not a
restriction in practice — the committed prefix is what every view
holding those verdicts holds whole, by causal completeness — and a
rule computing from its own copy of it satisfies the clause; as with
the enforceability discussion of report §4 the model states the
mathematical condition while the implementation owes the discipline.

`base_prefix` pins epochs `0` and `1` to the base schedule: the first
window from which `pick` has a two-epoch-old prefix to read is epoch
`2`.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- A Hammerhead-style reassignment policy: epoch length, the rule, and
the clauses it owes. Fairness — the clause liveness will price — is
deliberately *not* here: safety must hold for arbitrary, even
adversarial, adapted policies, and stating fairness where liveness
consumes it keeps that separation visible. -/
structure AdaptivePolicy (Validator : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] (BlockId : Type*)
    [DecidableEq BlockId] (Payload : Type*) [S : Slots Validator] where
  /-- The epoch length, in slots. -/
  W : ℕ
  W_pos : 0 < W
  /-- One leader per round, for the whole arc. -/
  inj : Function.Injective S.slotRound
  /-- The reassignment rule: from the universe, the validator's view of
  it and a verdict function, the leader of each slot. -/
  pick : (U : BlockUniverse Validator BlockId Payload) →
    View Validator BlockId Payload U → (ℕ → Option BlockId) → ℕ → Validator
  /-- **Adaptedness.** The leader of slot `k` reads the verdicts of
  epochs `≤ epochOf k − 2` and nothing else — not the view either. -/
  adapted : ∀ U (V₁ V₂ : View Validator BlockId Payload U) v w k,
    (∀ j, epochOf W j + 2 ≤ epochOf W k → v j = w j) →
    pick U V₁ v k = pick U V₂ w k
  /-- Epochs `0` and `1` run the base schedule. -/
  base_prefix : ∀ U V v k, epochOf W k < 2 → pick U V v k = S.leader k

namespace AdaptivePolicy

variable [S : Slots Validator]

/-- The constant policy: reassign nothing. The conservativity anchor —
under it the adaptive development must collapse onto the base one. -/
def const (W : ℕ) (hW : 0 < W) (hinj : Function.Injective S.slotRound) :
    AdaptivePolicy Validator BlockId Payload where
  W := W
  W_pos := hW
  inj := hinj
  pick _ _ _ k := S.leader k
  adapted _ _ _ _ _ _ _ := rfl
  base_prefix _ _ _ _ _ := rfl

@[simp] theorem const_pick (W : ℕ) (hW : 0 < W)
    (hinj : Function.Injective S.slotRound)
    (U : BlockUniverse Validator BlockId Payload) (V : View Validator BlockId Payload U)
    (v : ℕ → Option BlockId) (k : ℕ) : (const W hW hinj).pick U V v k = S.leader k := rfl

end AdaptivePolicy

end LeanDag
