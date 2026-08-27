import LeanDagTest.DoS.Density
import LeanDag.FinWhale.DoSBridge

/-!
# FinWhale witnesses — a DoS-valid universe, read as a FinWhale DAG

`Utwin` (`dos-equivocation-and-growth.md` §7) is the DoS arc's own
execution: four validators, validator `0` equivocating at round `0` with
blocks `0` and `4`, and `utwin_dosValid` settles the denial-of-service
condition on it by `decide`.

That is enough to make it a FinWhale DAG, and the leader clause is doing
real work there rather than holding vacuously. Take validator `0` — the
equivocator — as the leader of every round. Its slot at round `0` has two
blocks. Block `5` votes for one version and block `6` for the other, so
block `8`, which has both among its parents, exposes the equivocation —
and its parents are `{5, 6, 7}`, authored by validators `1`, `2` and `3`.
The equivocator is not among them, which is exactly what the clause
requires and what `DoSValid` already forced.
-/

namespace LeanDagTest

namespace FinWhaleDoS

open LeanDag LeanDag.FinWhale

/-- FinWhale's smallest committee, on the DoS arc's four validators. -/
local instance twinParams : Params (Fin 4) where
  p := 1
  p_pos := by omega
  p_le_f := by decide
  card_add_one := by decide

/-- The equivocator leads every round, which is the case the clause is
for. -/
def twinLeader : ℕ → Fin 4 := fun _ => 0

/-- **The bridge, on data**: a DoS-valid universe as a FinWhale DAG. -/
def Dtwin : Dag (Fin 4) (Fin 9) Unit :=
  Dag.ofDoSValid Utwin twinLeader utwin_dosValid

/-- The slot of round `0` has both versions, and they conflict. -/
example : slotBlocks Dtwin 0 = {0, 4} ∧ Conflicting Dtwin 0 4 := by decide

/-- Their author is Byzantine, which is what `correct_single` — inherited
from the universe's non-equivocation — leaves room for. -/
example : (Dtwin.block 0).creator ∉ (Correct : Finset (Fin 4)) := by decide

/-- **Block `8` exposes the equivocation.** Its parents vote for both
versions. -/
example : ExposesEquivocation Dtwin 8 := by decide

/-- **So it does not cite the equivocator**, which is the leader clause's
second branch — here forced by the DoS condition rather than assumed. -/
example : Dtwin.leader ((Dtwin.block 8).round - 2) ∉ parentSet Dtwin 8 :=
  leader_not_parent_of_exposes (by decide) (by decide) (by decide)

/-- And the self-parent edge comes with the universe, so Validity needs
no hypothesis here. -/
example : SelfParented Dtwin := selfParented_ofDoSValid utwin_dosValid

/-- Anti-vacuity: the clause is not satisfied by an empty parent set —
block `8` has three parents, and one of them is its author's own. -/
example : parentSet Dtwin 8 = {1, 2, 3} ∧ (7 : Fin 9) ∈ (Dtwin.block 8).refs := by decide

end FinWhaleDoS

end LeanDagTest
