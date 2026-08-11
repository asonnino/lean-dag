import LeanDag.BlockDag
import Mathlib.Logic.Relation

/-!
# Causal history

`spec.md` §3.4 and T2.

`Reaches U c b` says `b` lies in the causal history of `c`: one can walk
from `c` down to `b` by following references zero or more times. This is the
relation the persistence theorem (T3) concludes.

Most of T2 comes free from `Relation.ReflTransGen` — reflexivity, single
steps, transitivity. The content is `round_le_of_reaches`: following a
reference strictly decreases the round (§3.2's predecessor condition), so
causal history only ever runs *downward*. Note that T3 inducts on the round
*number*, an ordinary `ℕ`, not on `Reaches` itself; no well-founded relation
instance is needed, only the fact that a block's references sit at a
strictly smaller round.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

/-- One step of causal history: `j` is directly referenced by `i`. -/
def RefStep (U : BlockUniverse Validator BlockId Payload) (i j : BlockId) : Prop :=
  j ∈ (U.block i).refs

/-- `Reaches U c b` — `b` lies in the causal history of `c`. -/
def Reaches (U : BlockUniverse Validator BlockId Payload) : BlockId → BlockId → Prop :=
  Relation.ReflTransGen (RefStep U)

namespace Reaches

/-- Every block is in its own causal history. -/
@[refl]
theorem refl {c : BlockId} : Reaches U c c :=
  Relation.ReflTransGen.refl

/-- A direct reference is one step of causal history. -/
theorem single {i j : BlockId} (h : j ∈ (U.block i).refs) : Reaches U i j :=
  Relation.ReflTransGen.single h

/-- Causal history composes. This is what glues `c → i` onto `i` reaches `b`
at the end of both branches of T3. -/
theorem trans {a b c : BlockId} (h₁ : Reaches U a b) (h₂ : Reaches U b c) : Reaches U a c :=
  Relation.ReflTransGen.trans h₁ h₂

/-- Prepend a direct reference: if `i` references `j` and `j` reaches `b`,
then `i` reaches `b`. The exact shape T3's inductive step needs. -/
theorem of_mem_refs {i j b : BlockId} (hij : j ∈ (U.block i).refs) (hjb : Reaches U j b) :
    Reaches U i b :=
  trans (single hij) hjb

end Reaches

/-- Causal history stays inside the universe: completeness propagates along
every step. -/
theorem mem_ids_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) : b ∈ U.ids := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih => exact U.complete _ ih _ hstep

/-- A block with no references reaches only itself. In particular genesis
blocks (`spec.md` §3.2, `refs_empty_of_round_zero`) are causal-history leaves. -/
theorem eq_of_reaches_of_refs_empty {c b : BlockId} (hc : (U.block c).refs = ∅)
    (h : Reaches U c b) : b = c := by
  rcases h.cases_head with heq | ⟨_, hstep, _⟩
  · exact heq.symm
  · simp [RefStep, hc] at hstep

/-- **T2.** Causal history runs downward in rounds: anything `c` reaches
sits at a round no greater than `c`'s.

This is the substantive half of T2 — reflexivity, single steps and
transitivity are inherited from `ReflTransGen`. It rests on `spec.md` §3.2's
predecessor condition, applied at each step to an intermediate id that
`mem_ids_of_reaches` keeps inside the universe. -/
theorem round_le_of_reaches {c b : BlockId} (hc : c ∈ U.ids) (h : Reaches U c b) :
    (U.block b).round ≤ (U.block c).round := by
  induction h with
  | refl => exact le_refl _
  | tail hab hstep ih =>
      have hmid := mem_ids_of_reaches hc hab
      have := U.round_of_mem_refs hmid hstep
      omega

/-- A block cannot reach anything strictly above it. Contrapositive of T2,
and the form that rules out spurious causal links. -/
theorem not_reaches_of_round_lt {c b : BlockId} (hc : c ∈ U.ids)
    (h : (U.block c).round < (U.block b).round) : ¬ Reaches U c b := by
  intro hreach
  have := round_le_of_reaches hc hreach
  omega

/-! ## Views

`spec.md` T6a. A view is downward-closed, so causal history computed inside
one coincides with causal history in the universe. That is what lets two
validators holding *different* views nonetheless agree about what lies in a
given block's history — the check does not depend on which view asks. -/

/-- **T6a.** Causal history never escapes a view. -/
theorem View.mem_of_reaches {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {c b : BlockId}
    (hc : c ∈ V.ids) (h : Reaches U c b) : b ∈ V.ids := by
  induction h with
  | refl => exact hc
  | tail _ hstep ih => exact V.complete _ ih _ hstep

/-- **T6a, in the form the commit rules consume.** Asking "is there a `P`-block
in `c`'s causal history?" gives the same answer whether or not the search is
confined to the view. Restricting to `V` changes nothing, because the answer
could never have lain outside it.

This is what makes a view-relative certificate check well defined: two
validators with different views but the same anchor cannot disagree. -/
theorem View.exists_reaches_iff {U : BlockUniverse Validator BlockId Payload}
    {V : View Validator BlockId Payload U} {P : BlockId → Prop} {c : BlockId}
    (hc : c ∈ V.ids) :
    (∃ b, b ∈ V.ids ∧ P b ∧ Reaches U c b) ↔ (∃ b, P b ∧ Reaches U c b) := by
  constructor
  · rintro ⟨b, _, hP, hr⟩
    exact ⟨b, hP, hr⟩
  · rintro ⟨b, hP, hr⟩
    exact ⟨b, View.mem_of_reaches hc hr, hP, hr⟩

end LeanDag
