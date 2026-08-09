import LeanDag.GC.Window
import LeanDag.DoS.Novelty

/-!
# The quorum route: N1 and what it supports

The development's original network assumption for **production**, kept
here rather than in the main line.

The main development obtains production from view convergence
(`ViewGrowth.populatedOn`, §6.9), and every result that needs it takes
`PopulatedOn` or `Populated` as a hypothesis rather than naming a route.
N1 is one way to discharge that hypothesis — historically the first, and
still the weakest and most implementable of the three, since it promises
a quorum only when one already exists. It is separated from the main line
so that a reader meets one network assumption there, not two.

```
N1 (DeliversQuorum) + P8 (Live)  ──L1──▶  Populated
                                             │
     view convergence ──ViewGrowth.populatedOn┘
     untimed views  ──populated_of_viewsConverge┘
```

Nothing in `LeanDag` outside this file depends on it. The results below
are the route itself (N1, L1), its repackaging, its transfer through a
garbage-collection cut, and the two statements that bundle it with the
DoS storage bound.
-/

namespace LeanDag

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable {D : Delivery U} {G N : ℕ}

/-! ## N1 and L1 -/

/-- **Asynchrony.** A quorum that exists is eventually held. Stated
conditionally — existence first, holding second — because unconditionally it
would assert the very block production L1 sets out to prove.

No round bound: this is what holds *before* GST too, and it is all L1 needs.
Contrast `EventuallyDelivers`, which demands the *whole* correct round and
only from `R`. -/
def DeliversQuorum (D : Delivery U) : Prop :=
  ∀ n, (Fintype.card Validator - F.f) ≤ (authorsAt U n).card →
    ∀ v ∈ (Correct : Finset Validator),
      (Fintype.card Validator - F.f) ≤ (creatorsOf U.block (D.accepted v n)).card
omit [DecidableEq BlockId] in
/-- **L1 — no stall.** Under `Live U D N` and `DeliversQuorum D`, every
correct validator has a block
at every round up to the horizon.

Induction on the round. The base is `genesis`. The step goes in two hops now
that `builds` is view-relative: the induction hypothesis makes `Correct` a
subset of `authorsAt U r`, so a quorum *exists*; `DeliversQuorum` turns that
into each correct validator *holding* a quorum; and only then does `builds`
apply.

That second hop is the content of question 2. Without it the theorem would be
claiming validators build on blocks they may never have received.

L1 is the **only** result where the horizon does real work. Its whole job is
to turn the growth assumption into the local `Populated` facts L4 consumes —
which is why L4 itself never mentions `N` (`liveness.md` §4.4). -/
theorem no_stall {D : Delivery U} (H : Live U D N) (hd : DeliversQuorum D) :
    ∀ r ≤ N, Populated U r := by
  intro r
  induction r with
  | zero => intro _; exact H.genesis
  | succ r ih =>
      intro hr v hv
      exact H.builds r (by omega) v hv
        (hd r (card_authorsAt_of_populated (ih (by omega))) v hv)

omit [DecidableEq BlockId] in
/-- L1 in the form L0 consumes: under `Live U D N` **every** round up to the
horizon carries a quorum of authors, not merely every round below some
frontier. -/
theorem card_authorsAt_of_live {D : Delivery U} (H : Live U D N)
    (hd : DeliversQuorum D) {r : ℕ} (hr : r ≤ N) :
    (Fintype.card Validator - F.f) ≤ (authorsAt U r).card :=
  card_authorsAt_of_populated (no_stall H hd r hr)
/-! ## G5's transfer lemmas — the assumptions, through a cut -/

theorem deliversQuorum_chopD (hd : DeliversQuorum D) :
    DeliversQuorum (chopD D G) := by
  intro m hq v hv
  rw [authorsAt_chop] at hq
  have h := hd (G + m) hq v hv
  rw [chopD_accepted, chop_block_eq, creatorsOf_chopBlock]
  exact h

theorem live_chopD {N : ℕ} (H : Live U D N) (hd : DeliversQuorum D)
    (hG : G ≤ N) : Live (chop U G) (chopD D G) (N - G) where
  genesis := by
    intro v hv
    obtain ⟨b, hb, hbc, hbr⟩ := no_stall H hd G hG v hv
    refine ⟨b, mem_chop_ids.mpr ⟨hb, by omega⟩, ?_, ?_⟩
    · rw [chop_block_eq, chopBlock_creator]; exact hbc
    · rw [chop_block_eq, chopBlock_round]; omega
  builds := by
    intro r hr v hv hq
    rw [chopD_accepted, chop_block_eq, creatorsOf_chopBlock] at hq
    obtain ⟨b, hb, hbc, hbr⟩ := H.builds (G + r) (by omega) v hv hq
    refine ⟨b, mem_chop_ids.mpr ⟨hb, by omega⟩, ?_, ?_⟩
    · rw [chop_block_eq, chopBlock_creator]; exact hbc
    · rw [chop_block_eq, chopBlock_round]; omega
/-! ## The DoS capstones, bundling growth with the storage bound -/

/-- **The composed statement — DoS resistance in one theorem.** One set of
hypotheses — growth (`Live`), quorum delivery, post-`R` delivery, the
*enforceable* budget, and the reference discipline — supports liveness and
linear storage **simultaneously**: no correct validator ever stalls, and no
correct validator's retained view grows faster than
`|Correct|·(f·κ+1) + f·κ` per round. The two conclusions do not compete:
liveness never needs a Byzantine block (D15b, and post-`R` the quorum is
derivable from the correct set alone,
`card_creators_accepted_of_eventuallyDelivers`), and by C3″ enforcing the
budget never defers a correct one. -/
theorem no_stall_and_card_viewUpto_le' {κ R N : ℕ} (H : Live U D N)
    (hd : DeliversQuorum D) (hED : EventuallyDelivers D R)
    (hbyz : ByzBudget D κ) (hra : RefsAccepted D) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n, R + 1 ≤ n →
        (viewUpto D v n).card ≤ (viewUpto D v (R + 1)).card +
          (n - (R + 1)) *
            ((Correct : Finset Validator).card * (F.f * κ + 1) + F.f * κ) :=
  ⟨no_stall H hd, fun _v hv _n hn => card_viewUpto_le' hbyz hED hra hv hn⟩

/-- **The capstone, unconditional.** `EventuallyDelivers` is gone: growth
plus quorum delivery give liveness (L1 is asynchrony-only), and the
enforceable budget plus the reference discipline give linear storage from
round 0 — DoS resistance under full asynchrony, in one theorem. -/
theorem no_stall_and_card_viewUpto_le {κ N : ℕ} (H : Live U D N)
    (hd : DeliversQuorum D) (hbyz : ByzBudget D κ) (hra : RefsAccepted D) :
    (∀ r ≤ N, Populated U r) ∧
      ∀ v ∈ (Correct : Finset Validator), ∀ n,
        (viewUpto D v n).card ≤
          (Correct : Finset Validator).card * (n + 1) +
            ((Correct : Finset Validator).card * F.f +
              n * ((Correct : Finset Validator).card * (F.f * κ))) :=
  ⟨no_stall H hd, fun _v hv n => card_viewUpto_le hbyz hra hv n⟩

end LeanDag
