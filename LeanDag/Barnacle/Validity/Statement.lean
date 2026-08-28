import LeanDag.Barnacle.Model.Run
import LeanDag.Barnacle.Model.Live

/-!
# BN14 — validity: a good author's block is delivered

BN5 gives the paper's Agreement, Total order and Integrity. The fourth
property the rest of this development proves of a commit rule — that a
correct validator's block eventually *reaches* the ledger — was absent,
and the paper does not claim it, but the bar here is the development's.

The route is the one the base protocols already supply. A run of height
`K` commits an anchor at each of its `K` configurations, at the round the
next configuration starts (`start_succ`). A good author's block two
rounds below such an anchor lies in the anchor's causal history, by
`LiveRule.Delivers` — which is coverage read as delivery, and holds of
whoever authored the anchor, not only of good authors. So the block is
carried by something the run commits.

Nothing about leadership is needed. The author does not have to lead a
slot, nor to be in the schedule at the right round: the anchor delivers
it whether or not the author ever leads again. That is a stronger route
than "a correct validator is eventually a leader", and it costs no
rotation hypothesis.

Statements only; the proofs live in `Proof.lean`.
-/

namespace LeanDag

namespace Barnacle

namespace Validity

variable {Validator : Type} [Fintype Validator] [DecidableEq Validator]
  {BlockId : Type} [DecidableEq BlockId] {Payload : Type}

/-- **BN14, validity.** In a run of height `K`, a good author's block two
rounds below the anchor of a configuration the run closed lies in the
causal history of the block that configuration commits. -/
def Delivered (R : LiveRule Validator BlockId Payload) (P : Params)
    (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
    (upd : UpdateRule R.toBaseRule) (slack : ℕ) : Prop :=
  -- Given the base protocol's delivery law …
  R.Delivers slack →
  -- … on any run over a good DAG …
  ∀ (U : R.Universe) (V : R.View U) (K : ℕ)
    (Rn : PartialRun R.toBaseRule P getLeader hk upd U V K) (Rnd N : ℕ),
    R.Good U Rnd N →
    -- … there is a good set, all but at most `slack` validators, …
    ∃ T : Finset Validator, Fintype.card Validator ≤ T.card + slack ∧
      -- … each of whose blocks, past the synchrony round and under the
      -- horizon, and two rounds below a closed configuration's anchor, …
      ∀ b ∈ R.ids U, (R.block U b).creator ∈ T → Rnd ≤ (R.block U b).round →
        (R.block U b).round + 1 ≤ N →
        ∀ k, k < K → (R.block U b).round + 2 ≤ Rn.start (k + 1) →
          -- … is in the history of the block that configuration commits.
          ∃ A, Rn.vdct k (Rn.anchor k) = some A ∧ b ∈ historyFrom (R.block U) A

/-- Validity, for every live rule satisfying the laws. -/
def Statement : Prop :=
  ∀ (Validator BlockId Payload : Type) [Fintype Validator] [DecidableEq Validator]
    [DecidableEq BlockId] (R : LiveRule Validator BlockId Payload), R.Laws →
    ∀ (P : Params) (getLeader : ℕ → Validator) (hk : Keyed getLeader P.maxLeaders)
      (upd : UpdateRule R.toBaseRule) (slack : ℕ),
      Delivered R P getLeader hk upd slack

end Validity

end Barnacle

end LeanDag
