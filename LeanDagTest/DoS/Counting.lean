import LeanDagTest.DoS.Acceptance
import LeanDag.DoS.Counting

/-!
# The counting bounds on concrete DAGs

`dos-equivocation-and-growth.md` §5, D5, D6, D19a, D19b.

Two models, because the bounds have different hypotheses. `Model.lean`'s `U3`
is a three-round DAG with no equivocation anywhere, so both bounds apply to it
at once — and the upper one is **exactly attained**, which is what makes it
worth checking rather than assuming. `Umerge` has an equivocation, so the
upper bound is unavailable at the universe level and the results have to be
applied where equivocation-freedom actually holds: to individual histories.

That contrast is the point of proving the counting lemma over an arbitrary
`Finset` (§8's design point). Equivocation-freedom is a property of the set
being counted, and in `Umerge` the sets disagree: `history Umerge 6` is free of
it, `history Umerge 9` is not, and `Umerge.ids` is not.
-/

open LeanDag

/-! ## Both bounds at once, on a DAG without equivocation

`U3` holds twelve blocks over rounds 0, 1, 2 — four per round, one per
validator. -/

theorem u3_equivFree : EquivFree U3 U3.ids := by decide

example : U3.ids.card = 12 := by decide
example : ∀ i ∈ U3.ids, (U3.block i).round ≤ 2 := by decide

/-- **D6.** A block at round 2 forces at least `(2f+1)·2 + 1 = 7` blocks. -/
example : ((Fintype.card (Fin 4) - Faults.f (Fin 4))) * 2 + 1 ≤ U3.ids.card :=
  card_ids_ge_of_round (i := 8) (by decide) (by decide)

/-- **D5.** And without equivocation there are at most `(3f+1)·3 = 12`. -/
example : U3.ids.card ≤ (Fintype.card (Fin 4)) * (2 + 1) :=
  card_le_of_equivFree u3_equivFree (by decide)

/-- The two together, and the upper bound is **tight**: `U3` attains it
exactly, so the `r+1` is not slack and `3f+1` is not a rounding. -/
example : ((Fintype.card (Fin 4) - Faults.f (Fin 4))) * 2 + 1 ≤ U3.ids.card ∧
    U3.ids.card ≤ (Fintype.card (Fin 4)) * (2 + 1) :=
  card_ids_bounds u3_equivFree (i := 8) (by decide) (by decide) (by decide)

example : (Fintype.card (Fin 4)) * (2 + 1) = 12 := by decide

/-! ## With an equivocation, the universe-level bound is gone

`Umerge` is not equivocation-free — blocks `0` and `4` share an author and a
round — so D5 simply does not apply to `Umerge.ids`. This is the situation the
DoS question is about, and it is why C1 is needed at all. -/

example : ¬ EquivFree Umerge Umerge.ids := by decide

-- D6 still applies: it never mentions equivocation.
example : ((Fintype.card (Fin 4) - Faults.f (Fin 4))) * 3 + 1 ≤ Umerge.ids.card :=
  card_ids_ge_of_round (i := 12) (by decide) (by decide)

example : Umerge.ids.card = 13 := by decide

/-! ## D19a — where equivocation-freedom does hold

Below the merge nothing is exposed, so the histories there are bounded. Above
it they are not — and by D11 that is the same fact as validator 0 being
excluded. -/

example : ∀ X : Fin 4, ¬ ExposedIn Umerge 6 X := by decide

/-- **D19a applied.** `|H(6)| = 4`, against a bound of `4 * 2 = 8`. -/
example : (history Umerge 6).card ≤ (Fintype.card (Fin 4)) * ((Umerge.block 6).round + 1) :=
  card_history_le_of_not_exposed (by decide) (by decide)

example : (history Umerge 6).card = 4 ∧ (Umerge.block 6).round = 1 := by decide

-- At the merge the hypothesis fails, exactly as D11 says it must.
example : EquivFree Umerge (history Umerge 9) ↔ ∀ X : Fin 4, ¬ ExposedIn Umerge 9 X :=
  equivFree_history_iff

example : ¬ EquivFree Umerge (history Umerge 9) := by decide

/-! ## D19b — a block is clean about what it references

Block `9` references block `6`, authored by validator 1. So validator 1's
contribution to `H(9)` is bounded by `round 9 + 1 = 3` — and it is exactly 3,
blocks `9`, `6` and `1`, one per round. The bound is attained.

Validator 0 is the contrast, and the shape of its contribution is what matters
rather than the size: two blocks at *one* round. -/

example : (6 : Fin 13) ∈ (Umerge.block 9).refs ∧ (Umerge.block 6).creator = 1 := by decide

example : ((history Umerge 9).filter
      (fun j => (Umerge.block j).creator = (Umerge.block 6).creator)).card
    ≤ (Umerge.block 9).round + 1 :=
  card_filter_creator_le_of_mem_refs umerge_dosValid (by decide) (by decide)

-- Exactly 3, one per round: the bound is attained, not merely respected.
example : ((history Umerge 9).filter (fun j => (Umerge.block j).creator = 1)).card = 3 := by decide
example : ∀ n, (historyBlocksOf Umerge 9 1 n).card ≤ 1 :=
  not_exposedIn_iff_card_le_one.mp (by decide)

/-- The contrast, and it is the whole of D19b. Validator 0 puts **two blocks at
one round** into `H(9)` — which is what D19b forbids of a referenced author —
and it can, precisely because `9` does not reference it. Nothing here bounds
that count as the DAG grows, and closing that gap is C1. -/
example : (historyBlocksOf Umerge 9 0 0).card = 2 := by decide

example : ∀ i ∈ (Umerge.block 9).refs, (Umerge.block i).creator ≠ 0 := by decide

/-! ## The bridge, end to end

D2 plus D19a: a bound on histories is a bound on what a validator stores. Here
the accepted set is the singleton frontier `{6}`, whose generated view is
`H(6)` itself. -/

theorem umerge_accepted_six : Accepted Umerge {6} 1 where
  subset_ids := by decide
  round_eq := by decide
  inj := by decide

example : (View.ofAccepted umerge_accepted_six).ids = history Umerge 6 := by decide

example : (View.ofAccepted umerge_accepted_six).ids.card ≤ (Fintype.card (Fin 4)) * 4 :=
  View.card_ofAccepted_le umerge_accepted_six (by decide)

#print axioms u3_equivFree
#print axioms umerge_accepted_six
