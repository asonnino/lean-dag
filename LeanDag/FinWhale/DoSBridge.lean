import LeanDag.FinWhale.Protocol
import LeanDag.DoS.Exposure

/-!
# A DoS-valid Mysticeti universe is a FinWhale DAG

`FinWhale.ValidHere` and the core's `ValidWrt` differ in two clauses:
FinWhale adds the leader clause, and drops the self-parent edge that the
core requires and the paper's block structure has (`finwhale.md` §1).

Under the denial-of-service condition of `dos-equivocation-and-growth.md`
the difference vanishes, in the useful direction. `DoSValid` says a block
may not cite an author its own causal history convicts of equivocating,
and that is the leader clause with three of its four narrowings removed:
it holds of every author, at unbounded depth, permanently. So a
`BlockUniverse` satisfying it is a FinWhale DAG at any leader schedule,
with the self-parent edge thrown in — and every result of this arc
applies to it.

Two things follow beyond the construction. `SelfParented` becomes a
theorem, so Theorem 26 (Validity) loses its one remaining hypothesis. And
the DAG and the universe are the *same object*, so the `ids_eq` and
`block_eq` conditions every liveness result carries are `rfl` — a `Run`
built this way names one execution rather than two and an equation
between them.

**What this does not claim.** `DoSValid` is strictly stronger than what
FinWhale specifies: the protocol admits a DAG that cites an equivocating
non-leader, and this file says nothing about such a DAG. What it gives is
that a deployment running FinWhale over a DoS-protected DAG — which is
the deployment one would want, by the storage bound of
`dos-equivocation-and-growth.md` §5 — gets the whole arc for free.
-/

namespace LeanDag

namespace FinWhale

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator] [P : Params Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}

omit P in
/-- **The DoS condition implies the leader clause.** If a block's parents
are not leader-consistent, the two conflicting versions they reference
are both in its causal history, so the leader is exposed in it — and an
exposed author may not be cited. -/
theorem leaderClause_of_dosValid (hdos : DoSValid U) (leader : ℕ → Validator)
    {b : BlockId} (hb : b ∈ U.ids) :
    2 ≤ (U.block b).round →
    (∀ i ∈ (U.block b).refs, ∀ j ∈ (U.block b).refs, ∀ x ∈ (U.block i).refs,
        ∀ y ∈ (U.block j).refs, (U.block x).creator = leader ((U.block b).round - 2) →
        (U.block y).creator = leader ((U.block b).round - 2) → x = y)
      ∨ (∀ i ∈ (U.block b).refs, (U.block i).creator ≠ leader ((U.block b).round - 2)) := by
  intro _
  by_cases hcons : ∀ i ∈ (U.block b).refs, ∀ j ∈ (U.block b).refs, ∀ x ∈ (U.block i).refs,
      ∀ y ∈ (U.block j).refs, (U.block x).creator = leader ((U.block b).round - 2) →
      (U.block y).creator = leader ((U.block b).round - 2) → x = y
  · exact Or.inl hcons
  · refine Or.inr ?_
    push Not at hcons
    obtain ⟨i, hi, j, hj, x, hx, y, hy, hxc, hyc, hne⟩ := hcons
    have hxh : x ∈ history U b :=
      (mem_history_iff hb).2 (Reaches.trans (Reaches.single hi) (Reaches.single hx))
    have hyh : y ∈ history U b :=
      (mem_history_iff hb).2 (Reaches.trans (Reaches.single hj) (Reaches.single hy))
    have hround : (U.block x).round = (U.block y).round := by
      have h1 := U.round_of_mem_refs hb hi
      have h2 := U.round_of_mem_refs hb hj
      have h3 := U.round_of_mem_refs (U.refs_subset hb hi) hx
      have h4 := U.round_of_mem_refs (U.refs_subset hb hj) hy
      omega
    intro k hk hkc
    exact hdos b hb k hk (hkc ▸ ⟨x, hxh, y, hyh, hne, hxc, hyc, hround⟩)

/-- **The construction.** A DoS-valid universe, read as a FinWhale DAG at
a given leader schedule. Three validity clauses are the core's, the
fourth is the theorem above, and non-equivocation is the universe's. -/
def Dag.ofDoSValid (U : BlockUniverse Validator BlockId Payload) (leader : ℕ → Validator)
    (hdos : DoSValid U) : Dag Validator BlockId Payload where
  ids := U.ids
  block := U.block
  leader := leader
  complete := U.complete
  valid := fun i hi =>
    { predecessor := (U.valid i hi).predecessor
      distinct_creators := (U.valid i hi).distinct_creators
      quorum := (U.valid i hi).quorum
      leader_clause := leaderClause_of_dosValid hdos leader hi }
  correct_single := U.no_equivocation

@[simp] theorem ofDoSValid_ids {leader : ℕ → Validator} (hdos : DoSValid U) :
    (Dag.ofDoSValid U leader hdos).ids = U.ids := rfl

@[simp] theorem ofDoSValid_block {leader : ℕ → Validator} (hdos : DoSValid U) :
    (Dag.ofDoSValid U leader hdos).block = U.block := rfl

@[simp] theorem ofDoSValid_leader {leader : ℕ → Validator} (hdos : DoSValid U) :
    (Dag.ofDoSValid U leader hdos).leader = leader := rfl

/-- **And the self-parent edge comes with it**, which the FinWhale model
drops and Validity asks for. Theorem 26 needs no hypothesis here. -/
theorem selfParented_ofDoSValid {leader : ℕ → Validator} (hdos : DoSValid U) :
    SelfParented (Dag.ofDoSValid U leader hdos) :=
  fun b hb hr => (U.valid b hb).self_parent hr

omit P in
/-- **A parent set of reliable authors is never obstructed.** No correct
validator is ever exposed, so the condition costs a builder nothing that
builds on correct validators' blocks.

This is where the A1′ corner is and is not. A validator holding the
round-`(r−1)` blocks of every correct validator has `n − f` unobstructed
authors and can always build. The corner is the case where it has not yet
received them — which is why the paper states A1′ as a condition on
advancement rather than on validity, and why no validity rule can
discharge it. -/
theorem not_exposed_of_correct_parents {b : BlockId} (hb : b ∈ U.ids)
    (h : ∀ i ∈ (U.block b).refs, (U.block i).creator ∈ (Correct : Finset Validator)) :
    ∀ i ∈ (U.block b).refs, ¬ ExposedIn U b (U.block i).creator :=
  fun i hi hexp => hexp.not_correct hb (h i hi)


/-- **A run over a DoS-valid universe.** The same data a `Run` asks for,
less three: the DAG *is* the universe, so `ids_eq` and `block_eq` are
`rfl`, and the self-parent edge is the core's. -/
def Run.ofDoSValid [LinearOrder BlockId] (U : BlockUniverse Validator BlockId Payload)
    (leader : ℕ → Validator) (hdos : DoSValid U)
    (horizon : ℕ) (rounds_le : ∀ b ∈ U.ids, (U.block b).round ≤ horizon)
    (paceHorizon : ℕ) (pace : PaceCore U (Correct : Finset Validator) paceHorizon)
    (rounds_advance : ∀ u ∈ (Correct : Finset Validator), ∀ n ≤ pace.top u, n ≤ pace.built u n)
    (stable : ℕ) (gst_le : pace.gst ≤ stable) (liveHorizon : ℕ)
    (commits : CommitsCorrectLeaders (Dag.ofDoSValid U leader hdos) stable liveHorizon)
    (live_le : liveHorizon ≤ paceHorizon) (roundRobin : RoundRobin leader)
    (choose : BlockId → ℕ → Option BlockId)
    (chooseSound : ChooseSound (Dag.ofDoSValid U leader hdos) choose) :
    Run Validator BlockId Payload where
  dag := Dag.ofDoSValid U leader hdos
  paced := U
  ids_eq := rfl
  block_eq := rfl
  horizon := horizon
  rounds_le := rounds_le
  paceHorizon := paceHorizon
  pace := pace
  rounds_advance := rounds_advance
  stable := stable
  gst_le := gst_le
  liveHorizon := liveHorizon
  commits := commits
  live_le := live_le
  roundRobin := roundRobin
  selfParented := selfParented_ofDoSValid hdos
  choose := choose
  chooseSound := chooseSound

end FinWhale

end LeanDag
