import LeanDag.FinWhale.Model.Anchor
import Mathlib.Data.Finset.Max

/-!
# FinWhale — verdicts, the reverse pass, and the tie-break

A validator's decisions are a verdict per leader slot. The reverse pass
fixes them: a slot decided by the direct rules takes that verdict, and
otherwise the validator finds its **anchor** — the first slot above
`r + 2` that is not skipped — and reads the slot off the anchor's causal
history, marking the slot undecided if the anchor is. `Verdict`, `Anchor`
and `WellFormed` state that, the last as a condition on a verdict
assignment rather than as a procedure. `Model/Pass.lean` gives the
procedure.

`WellFormed` takes the direct rules as parameters, because each validator
evaluates them on its own view. `choose` — the paper's "deterministic
rule" for selecting among an anchor's conflicting candidates — is shared,
since it reads only the anchor and the round. `ChooseSound` is what such
a rule must satisfy, and `chooseLeast` is one that does: the least
candidate in the identifier order, where the paper names none.

`Exclusions` is not part of the protocol. It is the interface Lemma 12
consumes — what two validators' direct rules must satisfy against each
other — and `exclusions_of_dag` and `exclusions_of_views` discharge it.
-/


namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {D : Dag Validator BlockId Payload}

/-- A validator's verdict for a leader slot. -/
inductive Verdict (BlockId : Type*) where
  /-- The slot is decided, and this block of it is committed. -/
  | commit (b : BlockId)
  /-- The slot is decided, and no block of it is committed. -/
  | skip
  /-- The slot is not yet decided. -/
  | undecided
  deriving DecidableEq

/-- **The anchor of `r`**: the first slot above `r + 2` that is not
skipped. -/
def Anchor (dec : ℕ → Verdict BlockId) (r a : ℕ) : Prop :=
  r + 2 < a ∧ dec a ≠ Verdict.skip ∧ ∀ a', r + 2 < a' → a' < a → dec a' = Verdict.skip

/-- **The reverse pass, as a condition on the verdicts.** The direct
rules are taken as parameters, because each validator evaluates them on
its own view: `dcommit r l` is "this validator sees a direct commit of
`l` at `r`", `dskip r` likewise. `choose` is the paper's deterministic
rule and is *shared*, since it reads only the anchor and the round. -/
structure WellFormed (dcommit : ℕ → BlockId → Prop) (dskip : ℕ → Prop)
    (choose : BlockId → ℕ → Option BlockId) (dec : ℕ → Verdict BlockId) : Prop where
  /-- A direct commit is taken. -/
  direct_commit : ∀ r l, dcommit r l → dec r = Verdict.commit l
  /-- A direct skip is taken. -/
  direct_skip : ∀ r, dskip r → dec r = Verdict.skip
  /-- Undecided where the anchor is undecided. -/
  indirect_undecided : ∀ r a, (¬ ∃ l, dcommit r l) → ¬ dskip r → Anchor dec r a →
    dec a = Verdict.undecided → dec r = Verdict.undecided
  /-- Decided by the anchor otherwise. -/
  indirect_commit : ∀ r a A, (¬ ∃ l, dcommit r l) → ¬ dskip r → Anchor dec r a →
    dec a = Verdict.commit A →
    dec r = (match choose A r with
      | some b => Verdict.commit b
      | none => Verdict.skip)
  /-- A slot decided without a direct rule was decided from an anchor. -/
  has_anchor : ∀ r, (¬ ∃ l, dcommit r l) → ¬ dskip r → dec r ≠ Verdict.undecided →
    ∃ a, Anchor dec r a

/-- **The exclusions Lemma 12 needs across two views**, as an interface.
Each is a universe-level fact this arc proves — `direct_commit_unique`,
`no_directSkip_of_commit`, `no_indirectCommit_of_fastCommit`,
`no_indirectCommit_of_directSkip`, and Lemmas 3 and 5 for the last —
lifted to two validators' views, where a direct verdict in a view is one
in the universe because a view is a sub-DAG. -/
structure Exclusions (dc dc' : ℕ → BlockId → Prop) (ds ds' : ℕ → Prop)
    (choose : BlockId → ℕ → Option BlockId) (Above : ℕ → BlockId → Prop) : Prop where
  /-- Two views cannot directly commit different blocks of a slot. -/
  commit_unique : ∀ r l l', dc r l → dc' r l' → l = l'
  /-- A direct commit in one view bars a direct skip in the other. -/
  commit_bars_skip : ∀ r l, dc r l → ¬ ds' r
  /-- And symmetrically. -/
  commit_bars_skip' : ∀ r l, dc' r l → ¬ ds r
  /-- A direct commit bars the deterministic rule naming anything else. -/
  commit_pins_choose : ∀ r l A b, dc r l → choose A r = some b → b = l
  /-- And symmetrically. -/
  commit_pins_choose' : ∀ r l A b, dc' r l → choose A r = some b → b = l
  /-- Under a direct commit the evidence reaches every anchor, so the
  rule always finds a candidate. This is Lemma 7's indirect half, out of
  Lemmas 3 and 5. -/
  commit_forces_choose : ∀ r l A, Above r A → dc r l → ∃ b, choose A r = some b
  /-- And symmetrically. -/
  commit_forces_choose' : ∀ r l A, Above r A → dc' r l → ∃ b, choose A r = some b
  /-- A direct skip bars the deterministic rule naming anything. -/
  skip_bars_choose : ∀ r A b, ds r → choose A r ≠ some b
  /-- And symmetrically. -/
  skip_bars_choose' : ∀ r A b, ds' r → choose A r ≠ some b

/-- **What the deterministic rule must satisfy.** It names only blocks
the anchor could indirectly commit, and it names one whenever there is
one to name. The paper's rule is a choice among the candidates, so both
hold of it. -/
structure ChooseSound (D : Dag Validator BlockId Payload)
    (choose : BlockId → ℕ → Option BlockId) : Prop where
  /-- Whatever it names is a candidate. -/
  sound : ∀ A r b, choose A r = some b → IndirectCommit D A r b
  /-- Where there is a candidate, it names one. -/
  total : ∀ A r, (∃ b, IndirectCommit D A r b) → ∃ b, choose A r = some b

open scoped Classical in
/-- **The deterministic rule, exhibited.** The paper resolves the choice
among an anchor's candidates "according to a deterministic rule" and
names none; this is one — the least candidate in the identifier order.

Soundness and totality are all any result here reads, and both hold of it
by construction. It is a function of the anchor and the round, so two
validators holding the same anchor make the same choice, which is what
`finwhale.md` §6 turns on. -/
noncomputable def chooseLeast [LinearOrder BlockId] (D : Dag Validator BlockId Payload)
    (A : BlockId) (r : ℕ) : Option BlockId :=
  if h : ((slotBlocks D r).filter (fun b => IndirectCommit D A r b)).Nonempty then
    some (((slotBlocks D r).filter (fun b => IndirectCommit D A r b)).min' h)
  else none

end FinWhale

end LeanDag
