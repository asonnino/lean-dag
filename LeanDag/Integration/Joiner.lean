import LeanDag.Integration.ScheduleShape
import LeanDag.Adaptive.Run

/-!
# I9 — the joiner and the adaptive schedule

The sharpest question in the integration arc. §13's adaptive schedule
is a function of the committed verdicts; §9's garbage collection prunes
those verdicts below a horizon. A validator that joins from the
truncation therefore may not hold what the policy reads — and if it
computes a *different* schedule, §13's uniqueness theorem does not
reach it, because `adaptiveRun_agree` quantifies over runs of one
policy over **one** universe. The joiner's run is over a different
universe, under a re-indexed schedule.

The question has a deployment analogue: Hammerhead recomputes its
schedule from committed sub-DAGs, which a pruned node lacks.

The decomposition here follows the shape the question forces. Two
schedule transformers are in play — `Slots.chop` (re-index from a base
slot, rebase rounds) and `slotsOf` (replace the leaders by an
assignment) — and the joiner's schedule is the first applied to the
second, while the schedule it can *compute for itself* is the second
applied to the first. **I9 is the statement that these coincide**, and
that is exactly what `HorizonStable` buys: a policy whose output on the
truncation is its output on the original, shifted.

The two halves:

* `slotsChop_slotsOf` — the transformers commute, unconditionally, at
  the level of what a schedule *is* (rounds and leaders). No policy
  hypothesis: this is arithmetic.
* `HorizonStable`, and the assignment agreement that follows from it —
  the policy half, which is a genuine restriction on policies and the
  deployment obligation the arc is looking for.
-/

namespace LeanDag

namespace Integration

variable {Validator : Type*} [Fintype Validator] [DecidableEq Validator]
variable [F : Faults Validator]
variable {BlockId : Type*} [DecidableEq BlockId] {Payload : Type*}
variable {U : BlockUniverse Validator BlockId Payload}
variable [S : Slots Validator] {G d : ℕ}

/-! ## The schedule transformers commute -/

/-- Truncation preserves one-leader-per-round. Injectivity of the
rebased rounds needs the base-slot condition: the subtraction is
faithful above the cut, and monotonicity carries `hd` to every slot at
or above `d`. -/
theorem injective_slotRound_chop (hd : G ≤ S.slotRound d)
    (hinj : Function.Injective S.slotRound) :
    Function.Injective (S.chop G d hd).slotRound := by
  intro k₁ k₂ h
  simp only [Slots.chop_slotRound] at h
  have h₁ := le_slotRound_add S hd k₁
  have h₂ := le_slotRound_add S hd k₂
  have : S.slotRound (d + k₁) = S.slotRound (d + k₂) := by omega
  have := hinj this
  omega

/-- **The transformers commute.** Truncating an adaptive schedule and
adapting a truncated one give the same rounds and the same leaders,
provided the assignment used in the truncation is the original one
shifted past the base slot.

This is unconditional — no policy hypothesis appears. It says the two
*constructions* agree; whether a joiner can actually produce the
shifted assignment is the separate question `HorizonStable` answers. -/
theorem slotsChop_slotsOf (hd : G ≤ S.slotRound d)
    (hinj : Function.Injective S.slotRound) (a : ℕ → Validator)
    (hd' : G ≤ (slotsOf hinj a).slotRound d) (k : ℕ) :
    ((slotsOf hinj a).chop G d hd').slotRound k
        = (slotsOf (S := S.chop G d hd)
            (injective_slotRound_chop hd hinj) (fun m => a (d + m))).slotRound k
      ∧ ((slotsOf hinj a).chop G d hd').leader k
        = (slotsOf (S := S.chop G d hd)
            (injective_slotRound_chop hd hinj) (fun m => a (d + m))).leader k :=
  ⟨rfl, rfl⟩

/-! ## The policy half

The schedule transformers commuting was arithmetic; whether a joiner
can *produce* the shifted assignment is a restriction on policies, and
it is the deployment obligation this section is looking for.

The obligation is stated on the joiner's **rule** — a bare
`pick`-shaped function — rather than on a whole `AdaptivePolicy`. That
is deliberate and loses nothing: `pick`'s type mentions no schedule, so
the rule is the part that can be compared across the re-indexing, while
an `AdaptivePolicy` is indexed by its `Slots` instance and a joiner's
policy therefore inhabits a different type from the network's. What
must agree is the leaders the two compute, and that is exactly what
comparing the rules says. -/

section Policy

variable {P : AdaptivePolicy Validator BlockId Payload}

/-- **Horizon-stability.** The joiner's rule, run on the truncation
with the joiner's own slot indices, returns what the network's policy
returns on the full history at the corresponding slot.

Read as a deployment obligation: *a validator that pruned below `G` and
re-indexed from `d` must still compute the leaders everyone else is
using.* A policy that reads arbitrarily far back into committed history
cannot satisfy this, which is the substantive content — such a policy
is incompatible with garbage collection, and saying so precisely is the
point of I9. -/
def HorizonStable (P : AdaptivePolicy Validator BlockId Payload) (d G : ℕ)
    (pick' : BlockUniverse Validator BlockId Payload →
      (ℕ → Option BlockId) → ℕ → Validator) : Prop :=
  ∀ (U : BlockUniverse Validator BlockId Payload) (v : ℕ → Option BlockId)
    (k : ℕ), pick' (chop U G) (fun m => v (d + m)) k = P.pick U v (d + k)

/-- **I9, the assignment half.** Under a horizon-stable rule a joiner
computes exactly the leaders the network is using: its assignment at
its own slot `k` is the full-history run's assignment at slot `d + k`.

Nothing here is about verdicts — it is the statement that the two
validators do not *disagree about who leads*, which is the premise any
agreement argument between them must have and the thing garbage
collection threatened. -/
theorem joiner_assign_agree {V : View Validator BlockId Payload U}
    {pick' : BlockUniverse Validator BlockId Payload →
      (ℕ → Option BlockId) → ℕ → Validator}
    (hs : HorizonStable P d G pick') (R : AdaptiveRun P U V) (k : ℕ) :
    pick' (chop U G) (fun m => R.vdct (d + m)) k = R.assign (d + k) := by
  rw [hs U R.vdct k, R.coherent (d + k)]

/-- The joiner's schedule *is* the network's, seen from another origin:
combining the assignment agreement with `slotsChop_slotsOf`, the two
`Slots` instances name the same leader at every slot. -/
theorem joiner_leader_agree {V : View Validator BlockId Payload U}
    (hd : G ≤ S.slotRound d) (hinj : Function.Injective S.slotRound)
    {pick' : BlockUniverse Validator BlockId Payload →
      (ℕ → Option BlockId) → ℕ → Validator}
    (hs : HorizonStable P d G pick') (R : AdaptiveRun P U V) (k : ℕ) :
    (slotsOf (S := S.chop G d hd) (injective_slotRound_chop hd hinj)
        (fun m => pick' (chop U G) (fun j => R.vdct (d + j)) m)).leader k
      = (slotsOf hinj R.assign).leader (d + k) := by
  simp only [slotsOf_leader]
  exact joiner_assign_agree hs R k

/-- The constant policy is horizon-stable exactly when the base slot is
the origin — which is the degenerate case, and the point is the
contrast. A rule that ignores verdicts still has to be *re-indexed* to
survive truncation; horizon-stability is not only about how far back a
policy reads, but about whether it is stated relative to the reader's
own slot numbering. -/
theorem horizonStable_const_zero {W : ℕ} {hW : 0 < W}
    {hinj : Function.Injective S.slotRound} :
    HorizonStable (AdaptivePolicy.const (BlockId := BlockId) (Payload := Payload)
      W hW hinj) 0 G (fun _ _ k => S.leader k) := by
  intro _ _ k
  show S.leader k = S.leader (0 + k)
  rw [Nat.zero_add]

/-! ## The epoch-alignment obligation

Horizon-stability aligns the *leaders*. The adaptive run also carries
an epoch structure — `epochOf W k = k / W`, with the policy reading
epochs `≤ e − 2` and verdicts bounded inside epoch windows — and that
structure is *not* invariant under re-indexing. A joiner's slot `k` is
the network's slot `d + k`, so the joiner's epoch `k / W` matches the
network's `(d + k) / W` only when the base slot falls on an epoch
boundary.

This is a second deployment obligation, independent of the policy: **a
garbage-collection base slot must be a multiple of the epoch width**.
Otherwise the two validators agree on who leads every slot and still
disagree about which epoch it belongs to — hence about which verdicts
the policy was entitled to read — and the fixpoint arguments of §13 do
not line up across the cut. -/

/-- **Epoch alignment.** When the base slot is a whole number of epochs,
the joiner's epoch numbering is the network's shifted by a constant,
and every epoch window corresponds. -/
theorem epochOf_add_of_dvd {W : ℕ} (hW : 0 < W) (hdvd : W ∣ d) (k : ℕ) :
    epochOf W (d + k) = d / W + epochOf W k := by
  obtain ⟨c, rfl⟩ := hdvd
  unfold epochOf
  rw [Nat.mul_div_cancel_left c hW, Nat.mul_add_div hW]

/-- Without alignment the correspondence fails: at `W = 2, d = 1` the
joiner's first two slots straddle the network's epoch boundary, so a
policy entitled to read epoch `0` on one side is reading part of epoch
`1` on the other. -/
example : epochOf 2 (1 + 1) ≠ 1 / 2 + epochOf 2 1 := by decide

end Policy

end Integration

end LeanDag
