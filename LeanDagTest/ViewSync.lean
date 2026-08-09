import LeanDag.ViewSync
import LeanDagTest.Partial
import LeanDagTest.Quantitative

/-!
# View convergence, witnessed

`ugrowSkewView` is `ugrowSkew` (`LeanDagTest/Partial.lean`) with its
`covers` field replaced by the two clauses that field conflates: a
view-level network guarantee and the protocol's referencing rule. The
holdings function is the honest one for that model — validator `v` holds
every block whose author built it at least `delay = 2` before time `t` —
so `converges` is a statement about *views* with no mention of references,
and `references` is a statement about *blocks* with no mention of the
network.

The point of the witness is that the split is satisfiable at the same
constants: drift `2`, `delay = 2`, `timeout = 4`, all tight
(`ugrowSkew_drift_tight`). Reference coverage then comes out through
`ViewSync.toTiming`, so nothing downstream is re-proved.
-/

namespace LeanDagTest

open LeanDag

/-- What `v` holds at time `t`. In this model the block `b` sits at round
`b / 4` with author `b % 4` and is built at time `(b % 4) + 4 * (b / 4)`,
which is `b` itself — so "built at least `delay` ago" is `b + 2 ≤ t`, and
a validator's own block is in hand the moment it is built, `b ≤ t`. Both
disjuncts are needed: the first is what `converges` moves between
validators, the second is what `holds_own` supplies. -/
def skewHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    b + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ b ≤ t)

/-- The view-level witness: `ugrowSkew` with `covers` split into
`converges` (network) and `references` (protocol). -/
def ugrowSkewView (N : ℕ) : ViewSync (Ugrow N) {1, 2, 3} N where
  blk v n := 4 * n + (v : ℕ)
  built v n := (v : ℕ) + 4 * n
  timeout _ := 4
  gst := 0
  delay := 2
  rounds_le := (ugrowSkew N).rounds_le
  blk_mem := (ugrowSkew N).blk_mem
  blk_creator := (ugrowSkew N).blk_creator
  blk_round := (ugrowSkew N).blk_round
  waits _ _ _ _ := by omega
  timeout_pos _ := by omega
  latest n := 3 + 4 * n
  built_le_latest v _ _ _ := by have := v.isLt; omega
  latest_mem _ _ := ⟨3, by decide, le_refl _⟩
  prompt _ _ _ _ := le_max_left _ _
  holds := skewHolds N
  holds_own v hv n hn := by
    have hv4 := v.isLt
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, Or.inr ⟨?_, by omega⟩⟩
    omega
  holds_mono v s t hst := by
    intro b hb
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t _ := by
    intro b hb
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, Or.inl (by omega)⟩
  references v hv n hn a ha har := by
    have hv4 := v.isLt
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [skewHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [ugrow_block, growBlock_round] at har
    simp only [ugrow_block, mem_growBlock_refs]
    omega

/-- **Reference coverage, from view convergence.** The witness satisfies
the view-level assumption, and `SynchronisedOn` follows — the derivation
of §6.8 with its network premise stated over views rather than over
references. -/
theorem ugrowSkewView_synchronised (N : ℕ) :
    SynchronisedOn (Ugrow N) {1, 2, 3} 0 :=
  (ugrowSkewView N).synchronisedOn_of_converges (by decide) (D := 2)
    (fun v hv w hw n _ _ => by
      obtain ⟨_, _⟩ := mem_T_bounds hv
      obtain ⟨_, _⟩ := mem_T_bounds hw
      show (w : ℕ) + 4 * n ≤ ((v : ℕ) + 4 * n) + 2
      omega)
    (le_refl 0) (fun n _ => by show 2 + 2 ≤ 4; omega)

/-- The reduction is definitional on the timing data, so every quantitative
result of `Timing.lean` reads off the view-level witness unchanged. -/
example (N : ℕ) : (ugrowSkewView N).toTiming.delay = 2 := rfl
example (N : ℕ) : (ugrowSkewView N).toTiming.built 1 0 = 1 := rfl

/-! ## Liveness on the foundation, on data

`Ugrow`'s round-robin schedule commits, and the whole chain — production,
coverage, the commit — runs off the view-level structure with no
`Delivery`, no `Live` and no `DeliversQuorum` anywhere. -/

-- Production comes from the structure itself.
example (N : ℕ) (hn : 2 ≤ N) : PopulatedOn (Ugrow N) {1, 2, 3} 2 :=
  (ugrowSkewView N).populatedOn hn

/-- A `{1,2,3}`-led slot commits, from view convergence and the wait
alone. -/
example (N : ℕ) (hlead : rrSlots.leader 3 ∈ ({1, 2, 3} : Finset (Fin 4)))
    (hN : rrSlots.slotRound 3 + 2 ≤ N) :
    ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) 3 L ∧
      Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) 3 (some L) :=
  (ugrowSkewView N).decided_of_leader_of_converges (S := rrSlots) (by decide)
    (by decide) (D₀ := 2)
    (fun v hv w hw => by
      obtain ⟨_, _⟩ := mem_T_bounds hv
      obtain ⟨_, _⟩ := mem_T_bounds hw
      show (w : ℕ) + 4 * 0 ≤ ((v : ℕ) + 4 * 0) + 2
      omega)
    (fun n => by show 2 + 2 ≤ 4; omega) (Nat.zero_le _) hN hlead

/-! ## The untimed variant, witnessed

`ugrowHonest` (`LeanDagTest/Partial.lean`) holds exactly the round-`n`
blocks not authored by validator `0` — the Byzantine one — so its views
are genuinely partial, and yet they converge on correct blocks. It
therefore satisfies both untimed clauses, and populates every round with
no `DeliversQuorum` anywhere. -/

theorem ugrowHonest_viewsConverge (N : ℕ) :
    ViewsConverge (ugrowHonest N) := by
  intro v _ w _ n b hb _
  exact hb

theorem ugrowHonest_holdsOwn (N : ℕ) : HoldsOwn (ugrowHonest N) := by
  intro v hv n b hb hbc hbr
  simp only [ugrowHonest, Finset.mem_filter, mem_blocksAt]
  refine ⟨⟨hb, hbr⟩, ?_⟩
  -- `v` is correct, so `v ≠ 0`, so `b` is not a multiple of four
  have : ((Ugrow N).block b).creator = v := hbc
  simp only [ugrow_block] at this
  have hv0 : (v : ℕ) ≠ 0 := by
    have hall : ∀ x : Fin 4, x ∈ (Correct : Finset (Fin 4)) → (x : ℕ) ≠ 0 := by
      decide
    exact hall v hv
  have : b % 4 = (v : ℕ) := by
    have := congrArg (fun (x : Fin 4) => (x : ℕ)) this
    simpa using this
  omega

/-- `Live` over the partial-view delivery — the same universe, so
production is immediate. -/
theorem ugrowHonest_live (N : ℕ) : Live (Ugrow N) (ugrowHonest N) N where
  genesis := ugrow_populated (Nat.zero_le N)
  builds _ hr v hv _ := ugrow_populated hr v hv

/-- **Production with no N1**, on data: every round populated, from
untimed view convergence and nothing else about the network. -/
example (N : ℕ) : ∀ r ≤ N, Populated (Ugrow N) r :=
  populated_of_viewsConverge (ugrowHonest_live N)
    (ugrowHonest_viewsConverge N) (ugrowHonest_holdsOwn N)

#print axioms ugrowSkewView_synchronised
#print axioms LeanDag.ViewSync.commits_recur_of_converges
#print axioms LeanDag.ViewSync.all_decided_below_of_converges
#print axioms LeanDag.ViewSync.covers_of_converges

end LeanDagTest
