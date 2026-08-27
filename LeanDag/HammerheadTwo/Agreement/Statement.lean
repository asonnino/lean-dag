import LeanDag.HammerheadTwo.Model.Run

/-!
# HH3 — the configuration sequence is agreed

The paper's Leader-Count Agreement proposition, and the safety
theorem's core (`hammerhead-two.md` §6): two validators adopt the same
sequence of configurations — the same start rounds *and* the same
counts — and the same verdicts.

The claim is stated for **any update rule**, with no synchrony, fairness
or view hypothesis: the verdicts of a range are derivations against one
fixed schedule and agree by the base rule's own agreement law; the
anchor is the least committed slot past one threshold in one verdict
function; and the update is one function of one universe, one anchor
and one state. The AIMD rule is one instance.

* **HH3, partial runs agree** — two runs closed to any two heights, over
  any two views, agree on every configuration up to the lower height and
  on every verdict of the ranges below it. There is no total form: a
  universe holds finitely many blocks and every configuration commits
  one, so runs are prefixes and agreement of prefixes is the whole claim
  (`hammerhead-two.md` §5).

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace HammerheadTwo

namespace Agreement

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **HH3, partial runs agree.** Two partial runs over one universe —
whatever views, whatever heights `K₁`, `K₂` — agree on `start`, `count`
and `backoff` up to `min K₁ K₂`, and below it on the anchor and on every
verdict of the range. The paper's Leader-Count Agreement, with the
"same value" half the outline found missing. -/
def PartialRunAgreement (R : BaseRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders) (upd : UpdateRule R) : Prop :=
  -- One universe; two validators, holding views `V₁` and `V₂` of it, whose
  -- runs are closed up to heights `K₁` and `K₂` — they need not have
  -- decided equally far.
  ∀ (U : R.Universe) (V₁ V₂ : R.View U) (K₁ K₂ : ℕ)
    (R₁ : PartialRun R P getLeader hk upd U V₁ K₁) (R₂ : PartialRun R P getLeader hk upd U V₂ K₂),
    -- For every configuration both have reached …
    ∀ k, k ≤ min K₁ K₂ →
      -- … they agree on when it starts, how many leaders it has, and its
      -- back-off — the paper's "same switch point" and "same value".
      R₁.start k = R₂.start k ∧ R₁.count k = R₂.count k ∧ R₁.backoff k = R₂.backoff k ∧
      -- And for every configuration both have *closed* — found its anchor —
      (k < min K₁ K₂ →
        -- they agree on which slot the anchor is …
        R₁.anchor k = R₂.anchor k ∧
        -- … and on the verdict of every slot `κ` of the range: rounds
        -- strictly after `start k` (`κ / count k` is `κ`'s round), up to and
        -- including the anchor's round, which is `start (k + 1)`.
        ∀ κ, R₁.start k < κ / R₁.count k → κ / R₁.count k ≤ R₁.start (k + 1) →
          R₁.vdct k κ = R₂.vdct k κ)

/-- Agreement of the configuration sequence and the verdicts, for every
base rule satisfying the laws, every parameter set, every keyed leader
function and **every update rule**. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : BaseRule Validator BlockId Payload), R.Laws →
    ∀ (P : Params) (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
      (upd : UpdateRule R),
      PartialRunAgreement R P getLeader hk upd

end Agreement

end HammerheadTwo

end LeanDag
