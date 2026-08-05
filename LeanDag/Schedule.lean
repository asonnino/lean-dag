import LeanDag.Mysticeti

/-!
# Leader schedules

`Slots` is the interface every downstream theorem indexes by: slots are
numbered by `ℕ`, and `slotRound`/`leader` say where each one sits and who
proposes it. It is not, however, what anyone wants to *write*. This file
supplies the constructor that concrete schedules are built from.

Every deployed schedule is **uniform**: `m` leaders in every `p`-th round.
That case has a closed form, `slotRound k = p * (k / m)`, and needs no
flattening machinery — `Slots.uniform` proves the three class fields once so
that no instance ever faces them.

| | `p` | `m` | `slotRound k` |
|---|---|---|---|
| the original single-leader schedule | 3 | 1 | `3k` |
| pipelined, one leader per round | 1 | 1 | `k` |
| pipelined, `m` leaders per round | 1 | `m` | `k / m` |

The first row is the conservativity check: `uniformSingle 3` satisfies the old
three-round spacing condition (`uniformSingle_spacing`), and under it every
later slot is eligible to anchor every earlier one
(`uniformSingle_eligible_of_lt`), so the generalised `Decided` has exactly the
old constructors available and no derivation is lost.

An irregular schedule — an arbitrary assignment of validators to rounds — is
not covered here; it needs the flattening of a per-round `List Validator`,
which is left for later.
-/

namespace LeanDag

namespace Slots

variable {Validator : Type*}

/-- **The uniform schedule**: `m` leaders in every `p`-th round, slot `k`
proposed by `elect k`.

`hblock` is the one real condition — the `m` proposers sharing a round are
distinct validators. Round-robin `elect k = k % n` satisfies it whenever
`m ≤ n`. Without it a single block would be the candidate for two slots and
the ledger would deliver it twice. -/
@[reducible]
def uniform (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (elect : ℕ → Validator)
    (hblock : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂) :
    Slots Validator where
  slotRound k := p * (k / m)
  leader k := elect k
  mono := fun _ _ hab => Nat.mul_le_mul_left p (Nat.div_le_div_right hab)
  unbounded := fun n => ⟨m * n, by
    rw [Nat.mul_div_cancel_left n hm]
    exact Nat.le_mul_of_pos_left n hp⟩
  keyed := by
    intro k₁ k₂ h
    simp only [Prod.mk.injEq] at h
    exact hblock k₁ k₂ (Nat.eq_of_mul_eq_mul_left hp h.1) h.2

section

variable {p m : ℕ} {hp : 0 < p} {hm : 0 < m} {elect : ℕ → Validator}
  {hblock : ∀ k₁ k₂, k₁ / m = k₂ / m → elect k₁ = elect k₂ → k₁ = k₂}

@[simp]
theorem uniform_slotRound (k : ℕ) :
    (uniform p m hp hm elect hblock).slotRound k = p * (k / m) := rfl

@[simp]
theorem uniform_leader (k : ℕ) :
    (uniform p m hp hm elect hblock).leader k = elect k := rfl

end

/-- With one leader per round the distinctness condition is vacuous: slots in
a round are the round, so no two of them share it. -/
theorem one_hblock (elect : ℕ → Validator) :
    ∀ k₁ k₂ : ℕ, k₁ / 1 = k₂ / 1 → elect k₁ = elect k₂ → k₁ = k₂ :=
  fun _ _ h _ => by simpa using h

/-- **One leader every `p` rounds.** `p = 3` is the schedule the development
had before pipelining; `p = 1` is pipelined single-leader. -/
@[reducible]
def uniformSingle (p : ℕ) (hp : 0 < p) (elect : ℕ → Validator) : Slots Validator :=
  uniform p 1 hp Nat.one_pos elect (one_hblock elect)

@[simp]
theorem uniformSingle_slotRound {p : ℕ} {hp : 0 < p} {elect : ℕ → Validator} (k : ℕ) :
    (uniformSingle p hp elect).slotRound k = p * k := by
  simp

/-! ### Conservativity

`uniformSingle 3` is the schedule the development had before pipelining. The
two results below are what "the generalisation loses nothing" means
concretely. -/

variable (elect : ℕ → Validator)

/-- **The old `spacing` field, recovered.** Consecutive slots of
`uniformSingle 3` really are three rounds apart, so the schedule the
development used before pipelining is an instance of the weakened class. -/
theorem uniformSingle_spacing (k : ℕ) :
    (uniformSingle 3 (by omega) elect).slotRound k + 3 ≤
      (uniformSingle 3 (by omega) elect).slotRound (k + 1) := by
  simp only [uniformSingle_slotRound]
  omega

/-- Feeding `uniformSingle_spacing` to `eligible_of_lt_of_spacing` gives the
other half of conservativity — under this schedule every later slot may anchor
an earlier one, so the generalised `Decided` offers exactly the constructors
the old one did. Stated for an *instance* of the schedule rather than for the
term, which is how callers meet it. -/
example [S : Slots Validator] (hsp : ∀ k, S.slotRound k = 3 * k) {k j : ℕ} (h : k < j) :
    Eligible Validator k j :=
  eligible_of_lt_of_spacing (fun k => by simp [hsp]; omega) h

end Slots

end LeanDag
