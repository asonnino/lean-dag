import LeanDag.Validators
import LeanDag.Causality

/-!
# Minnow — the commit rule `crs*`, as the paper defines it

The partially synchronous variant, S-Minnow (`minnow.md` §1). Only what
a counterexample needs is modelled: the communication component's notion
of a valid DAG, and Definition 9's pattern `Ps*`.

**Validity is the paper's, not the core's.** A vertex carries edges to
`2f + 1` vertices of the round below by distinct processes, and nothing
more. In particular there is **no self-parent condition**: section 2 of
the paper asks only
that "vertices are valid only if they reference at least `2f + 1` valid
vertices issued in the previous round by distinct processes". Reusing
the core's `ValidWrt` would impose an edge the protocol does not, and
would change which DAGs the counterexample is drawn from.

**Equivocation is admitted, of faulty processes only.** Section 2 of the
paper says that if a *faulty* process issues two valid vertices in one
round, correct processes hold both and choose one to point at. So a slot
may carry no vertex, one, or several — but a correct process follows its
algorithm, which issues one vertex a round, and `correct_single` records
that. It is the core's `no_equivocation` with its correctness guard
intact; what Minnow drops relative to the arcs of `report.md` §17 and
§18 is validity's self-parent clause, not this.

**Trusted core of the arc: definitions only.** No theorem lives in this
file.
-/

namespace LeanDag

namespace Minnow

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}

/-- **Validity, as Minnow's communication component defines it**: every
edge sits in the round below, no two edges share a process, and a
non-genesis vertex carries `2f + 1` of them. No self-parent. -/
structure ValidHere (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Prop where
  /-- Every edge points to the round immediately below. -/
  predecessor : ∀ i ∈ b.refs, (blk i).round + 1 = b.round
  /-- No two edges share a process. -/
  distinct_creators : ∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j
  /-- A non-genesis vertex carries `2f + 1` edges by distinct processes. -/
  quorum : 0 < b.round → quorumCard Validator ≤ (creators blk b).card

instance (blk : BlockId → Block Validator BlockId Payload)
    (b : Block Validator BlockId Payload) : Decidable (ValidHere blk b) :=
  decidable_of_iff
    ((∀ i ∈ b.refs, (blk i).round + 1 = b.round) ∧
      (∀ i ∈ b.refs, ∀ j ∈ b.refs, (blk i).creator = (blk j).creator → i = j) ∧
      (0 < b.round → quorumCard Validator ≤ (creators blk b).card))
    ⟨fun h => ⟨h.1, h.2.1, h.2.2⟩, fun h => ⟨h.predecessor, h.distinct_creators, h.quorum⟩⟩

/-- A DAG the communication component can build. Equivocating vertices
are admitted: a faulty process may issue two, and both are held. -/
structure Dag (Validator BlockId Payload : Type*) [Fintype Validator]
    [DecidableEq Validator] [Faults Validator] where
  /-- Which vertices exist. -/
  ids : Finset BlockId
  /-- What each id denotes. -/
  block : BlockId → Block Validator BlockId Payload
  /-- The DAG is closed under edges. -/
  complete : ∀ i ∈ ids, ∀ j ∈ (block i).refs, j ∈ ids
  /-- Every vertex is valid. -/
  valid : ∀ i ∈ ids, ValidHere block (block i)
  /-- **Only a faulty process issues two vertices in one round.** Section
  2 of the paper admits equivocating vertices into the DAG, but a correct
  process follows its algorithm, which issues one vertex a round. -/
  correct_single : ∀ i ∈ ids, ∀ j ∈ ids,
    (block i).creator ∈ (Correct : Finset Validator) →
    (block i).creator = (block j).creator →
    (block i).round = (block j).round → i = j

variable {D : Dag Validator BlockId Payload}

/-- The vertices of a round. -/
def verticesAt (D : Dag Validator BlockId Payload) (r : ℕ) : Finset BlockId :=
  D.ids.filter (fun b => (D.block b).round = r)

/-- The causal past of `v`, `v` included. -/
def cone (D : Dag Validator BlockId Payload) (v : BlockId) : Finset BlockId :=
  historyFrom D.block v

/-- `u ⇝ v`: `u` lies in the causal past of `v`. -/
def Reaches (D : Dag Validator BlockId Payload) (v u : BlockId) : Prop :=
  u ∈ cone D v

instance (D : Dag Validator BlockId Payload) (v u : BlockId) :
    Decidable (Reaches D v u) := inferInstanceAs (Decidable (_ ∈ _))

/-- Neither vertex is in the other's causal past. -/
def Concurrent (D : Dag Validator BlockId Payload) (a b : BlockId) : Prop :=
  ¬ Reaches D a b ∧ ¬ Reaches D b a

instance (D : Dag Validator BlockId Payload) (a b : BlockId) :
    Decidable (Concurrent D a b) := inferInstanceAs (Decidable (_ ∧ _))

/-- **A slot**: a process and a round, as section 2 of the paper has it —
"a slot is a pair `(p, r)` that identifies a proposal … but there may be
no, or many such vertices if `p` is faulty". -/
abbrev Slot (Validator : Type*) := Validator × ℕ

/-- The vertices occupying a slot. -/
def slotBlocks (D : Dag Validator BlockId Payload) (s : Slot Validator) : Finset BlockId :=
  D.ids.filter (fun b => (D.block b).creator = s.1 ∧ (D.block b).round = s.2)

/-- The processes with a vertex of round `r` carrying an edge to `l`. -/
def pointers (D : Dag Validator BlockId Payload) (l : BlockId) (r : ℕ) : Finset Validator :=
  creatorsOf D.block ((verticesAt D r).filter (fun q => l ∈ (D.block q).refs))

/-- **Quorum**, the first clause of `Φ*s`: `l` is pointed to by `2f + 1`
vertices of the round above, issued by distinct processes. -/
def Quorum (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  quorumCard Validator ≤ (pointers D l ((D.block l).round + 1)).card

instance (D : Dag Validator BlockId Payload) (l : BlockId) :
    Decidable (Quorum D l) := inferInstanceAs (Decidable (_ ≤ _))

/-- **Skip**, the escape in the second clause: `2f + 1` of the round above
carry no edge to `l`, counted by **distinct process**, none of whose
round-above vertices points at `l`.

Definition 9 writes "there are `2f + 1` vertices", but the quorum clause
two lines above counts "vertices issued by distinct processes", and every
other quorum in the paper is over processes. `report.md` §19.3 is why the
vertex reading cannot be meant: under it a vertex may be committed and
skipped at once. -/
def Skipped (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  quorumCard Validator ≤
    ((creatorsOf D.block (verticesAt D ((D.block l).round + 1)))
      \ pointers D l ((D.block l).round + 1)).card

instance (D : Dag Validator BlockId Payload) (l : BlockId) :
    Decidable (Skipped D l) := inferInstanceAs (Decidable (_ ≤ _))

/-- **Skip, counted by vertex** — Definition 9 at the letter. Kept only
to state what that reading costs; `Skipped` is what the rule is taken to
mean. -/
def SkippedByVertex (D : Dag Validator BlockId Payload) (l : BlockId) : Prop :=
  quorumCard Validator ≤ ((verticesAt D ((D.block l).round + 1)).filter
    (fun q => l ∉ (D.block q).refs)).card

instance (D : Dag Validator BlockId Payload) (l : BlockId) :
    Decidable (SkippedByVertex D l) := inferInstanceAs (Decidable (_ ≤ _))

/-- **`crs*`** (Definition 9), by recursion on the position in `leaders`.
`CommittedAt D L k l` is the pattern `Ps*` enabled for the vertex `l`
occupying the `k`-th leader slot: a quorum points to it, and every
earlier slot is *resolved* — some vertex of that slot lies in `l`'s
causal past, or is concurrent with `l` and either committed or skipped.

The existential over `v` is the paper's: "there is a vertex `v′` in slot
`s′` in `D` such that …". One vertex of a slot resolving it is what makes
`minnow.md` §3 possible. -/
def CommittedAt (D : Dag Validator BlockId Payload) (L : ℕ → Slot Validator) :
    ℕ → BlockId → Prop
  | 0, l => Quorum D l
  | (k + 1), l =>
      Quorum D l ∧
      ∀ j ≤ k, ∃ v ∈ slotBlocks D (L j),
        Reaches D l v ∨ (Concurrent D l v ∧ (CommittedAt D L j v ∨ Skipped D v))

end Minnow

end LeanDag
