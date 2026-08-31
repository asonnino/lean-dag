import LeanDag.RedSnapper.Model.Five.Freeze
import LeanDag.RedSnapper.Model.Verdict

/-!
# The 5f+1 verdicts

Trusted core: the three decision routes of `Alg:snapper5f`'s
`TryDecide` — `TryFullDecideTX`, `TryFullUnlockObj`,
`ResolveOnCommitObj` — as one order-free inductive relation, the D6
pattern: a constructor per route, any derivable verdict counts, and
that all derivable verdicts agree is RS8's theorem, never a side
condition. `Fate` is shared with the `3f+1` verdict.

The consensusless routes read a **view** and decide on a *single*
observed certificate block — finality in one observation, unlike the
`3f+1` round quorum. The unlock route drops every owned candidate of
the object seen anywhere in the view (the algorithm's
`K = ⋃_{b ∈ DAG[r]} Candidates(b, o)`, re-run each round: any candidate
ever seen is eventually dropped; reading the whole view only enlarges
the set of derivable drops the agreement theorem covers). The recovery
route reads the global `(U, A)` of D4, so its cross-validator agreement
is definitional; it commits the eligible candidate minimal under
`prio`, the algorithm's fixed hash order rendered as a linear-order
parameter (D8's treatment of the coin) — `RecoverySafetyWin` holds for
an arbitrary member of `W`, so the tie-break carries no safety weight.

The algorithm's `decidedObj` one-shot and route precedence appear as no
clause, exactly as in the `3f+1` relation: RS8 proves the routes never
disagree.
-/

namespace LeanDag

namespace RedSnapper

variable {Validator BlockId Tx Obj : Type*} [Fintype Validator] [DecidableEq Validator]
  [DecidableEq BlockId] [F : Faults Validator] [T : Transactions Tx Obj]

/-- The verdict relation at `5f+1`: `VerdictFive U A V prio tx f` — the
validator holding view `V`, over the committed anchors `A` and the
fixed transaction order `prio`, can justify fate `f` for `tx`. -/
inductive VerdictFive (U : Universe Validator BlockId Tx Obj) (A : Anchors U) (V : View U)
    (prio : Tx → Tx → Prop) : Tx → Fate → Prop where
  /-- Consensusless finality (`TryFullDecideTX`): one observed full
  certificate finalises an owned transaction. -/
  | fullFinal {tx : Tx} {C : BlockId} :
      Owned tx →                        -- the IsOwned gate (D9)
      C ∈ V.ids →                       -- a block of the view ...
      IsFullCert U C tx →               -- ... carrying a full certificate
      VerdictFive U A V prio tx Fate.finalized
  /-- Consensusless release (`TryFullUnlockObj`): one observed full
  unlock certificate drops every owned candidate of the object. -/
  | fullUnlockDrop {tx : Tx} {C b : BlockId} :
      C ∈ V.ids →                       -- a block of the view ...
      IsFullUnlockCert U C (T.input tx) →  -- ... unlocking the input
      b ∈ V.ids →                       -- and the dropped transaction is
      OwnedCandidate U b (T.input tx) tx →  -- an owned candidate seen in the view
      VerdictFive U A V prio tx Fate.dropped
  /-- The recovery commit (`ResolveOnCommitObj`, `win = tx`): at the
  resolving anchor, the transaction is eligible and `prio`-minimal
  among the eligible. -/
  | recoveryFinal {tx : Tx} {i j : ℕ} {aₖ a : BlockId} :
      ResolvesFiveAt U A (T.input tx) i j →
      A.seq[i]? = some aₖ → A.seq[j]? = some a →
      EligibleFive U aₖ a (T.input tx) tx →     -- tx ∈ W ...
      (∀ tx', EligibleFive U aₖ a (T.input tx) tx' → prio tx tx') →
                                        -- ... and minimal under the fixed order
      VerdictFive U A V prio tx Fate.finalized
  /-- The recovery drop of a loser (`win = tx' ≠ tx`): a candidate that
  is not the winner is dropped at the resolving anchor. -/
  | recoveryDropLoser {tx tx' : Tx} {i j : ℕ} {aₖ a : BlockId} :
      ResolvesFiveAt U A (T.input tx) i j →
      A.seq[i]? = some aₖ → A.seq[j]? = some a →
      OwnedCandidate U a (T.input tx) tx →      -- tx ∈ K ...
      EligibleFive U aₖ a (T.input tx) tx' →    -- ... while the winner
      (∀ tx'', EligibleFive U aₖ a (T.input tx) tx'' → prio tx' tx'') →
      tx ≠ tx' →                                -- ... is someone else
      VerdictFive U A V prio tx Fate.dropped
  /-- The recovery release (`win = ⊥`): with nothing eligible, every
  candidate is dropped and the object released. -/
  | recoveryDropBot {tx : Tx} {i j : ℕ} {aₖ a : BlockId} :
      ResolvesFiveAt U A (T.input tx) i j →
      A.seq[i]? = some aₖ → A.seq[j]? = some a →
      OwnedCandidate U a (T.input tx) tx →      -- tx ∈ K ...
      (∀ tx', ¬ EligibleFive U aₖ a (T.input tx) tx') →  -- ... and W is empty
      VerdictFive U A V prio tx Fate.dropped

end RedSnapper

end LeanDag
