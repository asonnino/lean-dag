import LeanDagTest.Catchup

/-!
# The collapse, exhibited from a large spread

`ugrowCatchPace` runs at the collapse bound from the start, so it cannot
show the mechanism *working*. This model can: the round-`0`
spread is `10` — more than three times the collapsed bound — because the laggard
starts late and GST has not yet arrived; at every round from `1` on the
spread is exactly `Δ + proc = 3`, the collapse bound of
`drift_collapse`, met with equality.

The run: validators `1` and `2` enter round `0` at times `0` and `1`,
the laggard `3` at time `10`; GST is `12`. Before GST the network
delivers nothing, so catch-up binds nobody — the large spread is
admissible precisely because no evidence has crossed. The first round-`1`
round-`0` blocks reach everyone at `14`, which is the earliest the
leaders can build round `1` --- a validator cannot reference what it has
not received (`holds_closed`). Those round-`1` blocks reach the laggard
at `16`, catch-up forces its round-`1` entry by `17`, and its own `waits`
floor (`10 + 5`) is met with room. From then on the laggard builds at the
catch-up deadline, the leaders as soon as their references arrive, and
the spread neither grows past `3` nor shrinks below it.

This also settles the coexistence question: `catchup` and `waits` are
jointly satisfiable *from* a large spread, not only near synchrony —
the timeout floor of the laggard and the catch-up deadline imposed by
the leaders' blocks meet, here with no slack at all.
-/

namespace LeanDagTest

open LeanDag

attribute [local instance 2000] rrSlots

/-- Entry times: the laggard `3` starts round `0` nine ticks after `1`;
from round `1` on, the leaders build at `14 + 5(n−1)` --- as early as
their own references allow --- and the laggard is pinned by catch-up at
`17 + 5(n−1)`. Validator `0` is Byzantine and outside `T`; its times
follow validator `1`. -/
def lagBuilt (v : Fin 4) : ℕ → ℕ
  | 0 => if (v : ℕ) = 3 then 10 else (v : ℕ) - 1
  | n + 1 => (if (v : ℕ) = 3 then 17 else 14) + 5 * n

@[simp] theorem lagBuilt_zero (v : Fin 4) :
    lagBuilt v 0 = if (v : ℕ) = 3 then 10 else (v : ℕ) - 1 := rfl
@[simp] theorem lagBuilt_succ (v : Fin 4) (n : ℕ) :
    lagBuilt v (n + 1) = (if (v : ℕ) = 3 then 17 else 14) + 5 * n := rfl

/-- When block `b` was built by its author. -/
def lagStamp (b : ℕ) : ℕ := lagBuilt ⟨b % 4, by omega⟩ (b / 4)

/-- What `v` holds at `t`: nothing crosses before GST (`12`), a block
arrives `delay = 2` after the later of its build and GST, and one's own
block is in hand at once. Since a build waits for the round below to
arrive, holdings are causally closed. -/
def lagHolds (N : ℕ) (v : Fin 4) (t : ℕ) : Finset ℕ :=
  (Finset.range (4 * (N + 1))).filter fun b =>
    max (lagStamp b) 12 + 2 ≤ t ∨ (b % 4 = (v : ℕ) ∧ lagStamp b ≤ t)

/-- **A `ViewPace` from a spread of `10`.** Every clause is proved for
the run described in the module docstring; the laggard's `waits` floor
and its catch-up deadline coincide at every round — the coexistence of
the floor and the trunk's catch-up rule, witnessed with no slack. -/
def ugrowLag (N : ℕ) : ViewPace (Ugrow N) {1, 2, 3} N where
  top _ := N
  built := lagBuilt
  timeout _ := 5
  gst := 12
  delay := 2
  proc := 1
  rounds_le b hb := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  built_of_le_top v hv n hn := rrUniverse_populatedOn _ _ _ _ _ _ hn v hv
  le_top_of_built _ _ b hb _ := by
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round]; omega
  waits v hv n _ := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    by_cases h : (v : ℕ) = 3
    · cases n <;> simp only [lagBuilt_zero, lagBuilt_succ, if_pos h] <;> omega
    · cases n <;> simp only [lagBuilt_zero, lagBuilt_succ, if_neg h] <;> omega
  timeout_pos _ := by omega
  latest n := 12 + 5 * n
  built_le_latest v hv n _ := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    cases n <;> simp only [lagBuilt_zero, lagBuilt_succ] <;> split <;> omega
  holds_closed v hv t b hb j hj := by
    obtain ⟨hv1, hv3⟩ := mem_T_bounds hv
    have hv4 := v.isLt
    simp only [lagHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    simp only [ugrow_block, mem_growBlock_refs] at hj
    -- `j` sits one round below `b`
    have hjb : j / 4 + 1 = b / 4 := by omega
    obtain ⟨m, hm⟩ : ∃ m, j / 4 = m := ⟨j / 4, rfl⟩
    have hbm : b / 4 = m + 1 := by omega
    have hsj : lagStamp j = lagBuilt ⟨j % 4, by omega⟩ m := by
      simp only [lagStamp, hm]
    have hsb : lagStamp b = lagBuilt ⟨b % 4, by omega⟩ (m + 1) := by
      simp only [lagStamp, hbm]
    -- the round below is stamped at least five earlier, and `b`'s own
    -- build waits for it
    have hjub : lagStamp j ≤ 12 + 5 * m := by
      rw [hsj]
      cases m with
      | zero => simp only [lagBuilt_zero]; split <;> omega
      | succ p => simp only [lagBuilt_succ]; split <;> omega
    have hblb : 14 + 5 * m ≤ lagStamp b := by
      rw [hsb]; simp only [lagBuilt_succ]; split <;> omega
    have h1 := le_max_left (lagStamp b) 12
    have h2 := le_max_right (lagStamp b) 12
    have hle : max (lagStamp j) 12 ≤ 12 + 5 * m := max_le (by omega) (by omega)
    refine ⟨by omega, Or.inl ?_⟩
    rcases hb.2 with h | ⟨_, h⟩ <;> omega
  refs_held v hv n b hb hbc hbr := by
    obtain ⟨hv1, hv3⟩ := mem_T_bounds hv
    have hv4 := v.isLt
    intro j hj
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    simp only [ugrow_block, mem_growBlock_refs] at hj
    simp only [lagHolds, Finset.mem_filter, Finset.mem_range]
    have hjn : j / 4 = n := by omega
    have hsj : lagStamp j = lagBuilt ⟨j % 4, by omega⟩ n := by
      simp only [lagStamp, hjn]
    have hjub : lagStamp j ≤ 12 + 5 * n := by
      rw [hsj]
      cases n with
      | zero => simp only [lagBuilt_zero]; split <;> omega
      | succ p => simp only [lagBuilt_succ]; split <;> omega
    have hvlb : 14 + 5 * n ≤ lagBuilt v (n + 1) := by
      simp only [lagBuilt_succ]; split <;> omega
    have hle : max (lagStamp j) 12 ≤ 12 + 5 * n := max_le (by omega) (by omega)
    exact ⟨by omega, Or.inl (by omega)⟩
  holds := lagHolds N
  holds_sub _ _ := by
    simp only [lagHolds, ugrow_ids]; exact Finset.filter_subset _ _
  holds_own v hv n _ b hb hbc hbr := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    have hv4 := v.isLt
    simp only [ugrow_ids, Finset.mem_range] at hb
    simp only [ugrow_block, rrBlock_round] at hbr
    have hb4 : b % 4 = (v : ℕ) := by
      have := congrArg (fun (x : Fin 4) => (x : ℕ)) hbc
      simpa [ugrow_block] using this
    have hstamp : lagStamp b = lagBuilt v n := by
      have hfin : (⟨b % 4, by omega⟩ : Fin 4) = v := Fin.ext hb4
      simp only [lagStamp]
      rw [hbr, hfin]
    simp only [lagHolds, Finset.mem_filter, Finset.mem_range]
    exact ⟨hb, Or.inr ⟨hb4, by rw [hstamp]⟩⟩
  holds_mono v s t hst := by
    intro b hb
    simp only [lagHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    exact ⟨hb.1, by omega⟩
  converges v _ w _ t ht := by
    intro b hb
    simp only [lagHolds, Finset.mem_filter, Finset.mem_range] at hb ⊢
    refine ⟨hb.1, Or.inl ?_⟩
    rcases hb.2 with h | ⟨_, h⟩
    · omega
    · have hle : max (lagStamp b) 12 ≤ t := max_le h ht
      omega
  references v hv n hn c hc hcc hcr a ha har := by
    obtain ⟨h1, h3⟩ := mem_T_bounds hv
    simp only [ugrow_ids, Finset.mem_range] at hc
    simp only [lagHolds, Finset.mem_filter, Finset.mem_range] at ha
    simp only [ugrow_block, rrBlock_round] at har hcr
    simp only [ugrow_block, mem_growBlock_refs]
    omega
  advances _ _ _ hn _ _ := hn
  catchup v hv n hn b hb hbT hbr t _ hheld := by
    obtain ⟨hv1, hv3⟩ := mem_T_bounds hv
    obtain ⟨hu1, hu3⟩ := mem_T_bounds hbT
    set u := ((Ugrow N).block b).creator with hu
    have hb4 : b % 4 = (u : ℕ) := by simp [hu, ugrow_block]
    simp only [ugrow_block, rrBlock_round] at hbr
    have hstamp : lagStamp b = lagBuilt u n := by
      have hfin : (⟨b % 4, by omega⟩ : Fin 4) = u := Fin.ext hb4
      simp only [lagStamp]
      rw [hbr, hfin]
    refine ⟨hn, ?_⟩
    simp only [lagHolds, Finset.mem_filter, Finset.mem_range, hb4, hstamp] at hheld
    rcases hheld.2 with h | ⟨huv, h⟩
    · -- arrival: the deadline covers the laggard exactly
      cases n with
      | zero =>
          have hL : lagBuilt v 0 ≤ 10 := by
            simp only [lagBuilt_zero]; split <;> omega
          have h12 := le_max_right (lagBuilt u 0) 12
          omega
      | succ n =>
          have hL : lagBuilt v (n + 1) ≤ 17 + 5 * n := by
            simp only [lagBuilt_succ]; split <;> omega
          have hU : 14 + 5 * n ≤ lagBuilt u (n + 1) := by
            simp only [lagBuilt_succ]; split <;> omega
          have hm := le_max_left (lagBuilt u (n + 1)) 12
          omega
    · -- own copy: `u = v`
      have huv' : u = v := Fin.ext (by omega)
      rw [huv'] at h
      omega

/-- **The collapse, on data.** The spread is `10` at round `0` and
exactly `Δ + proc = 3` at every round from `1` on — five times the
collapsed bound, gone in one post-GST round, and never returning. -/
theorem ugrowLag_collapse (N : ℕ) :
    lagBuilt 3 0 = lagBuilt 1 0 + 10 ∧
      ∀ n, lagBuilt 3 (n + 1) = lagBuilt 1 (n + 1) + 3 := by
  refine ⟨by decide, fun n => ?_⟩
  rw [lagBuilt_succ, lagBuilt_succ,
    if_pos (show ((3 : Fin 4) : ℕ) = 3 by decide),
    if_neg (show ¬((1 : Fin 4) : ℕ) = 3 by decide)]
  omega

/-- The collapsed spread agrees with `drift_collapse`'s bound: from
round `1` on, every pair of reliable validators is within `Δ + proc`. -/
example (N : ℕ) {n : ℕ} (hn : n + 1 ≤ N) :
    ∀ v ∈ ({1, 2, 3} : Finset (Fin 4)), ∀ w ∈ ({1, 2, 3} : Finset (Fin 4)),
      (ugrowLag N).built v (n + 1) ≤ (ugrowLag N).built w (n + 1) + 3 := by
  refine (ugrowLag N).drift_collapse hn (fun u _ => hn) (fun u hu => ?_)
  show (12 : ℕ) ≤ lagBuilt u (n + 1)
  simp only [lagBuilt_succ]
  split <;> omega

/-- **The commit, from the collapsed spread.** Slot `5` sits at round
`15 ≥ 12 = GST`; it is committed at timeout `5 = 2Δ + proc`, with the
round-`0` spread of `10` appearing in no hypothesis. -/
theorem ugrowLag_decided (N : ℕ) (hN : rrSlots.slotRound 5 + 2 ≤ N) :
    ∃ L, IsLeaderBlock (S := rrSlots) (Ugrow N) 5 L ∧
      Decided (S := rrSlots) (Ugrow N) (View.full (Ugrow N)) 5 (some L) :=
  (ugrowLag N).decided_of_wait (R := 12) (by decide)
    (le_refl 12) (fun n _ => by change 2 * 2 + 1 ≤ 5; omega)
    (by simp only [rrSlots_slotRound]; omega) hN (by decide)

#print axioms ugrowLag_collapse
#print axioms ugrowLag_decided

end LeanDagTest
