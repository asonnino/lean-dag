import LeanDag.Barnacle.Model.Rule
import LeanDag.Schedule

/-!
# Barnacle: the schedule of a configuration

The paper's slot `(r, l)`, for `l` below the leader count, is led by
`GetLeader(r + l)` (`barnacle.md` §3). The leader function does not
depend on the count: across configurations only *which slots exist*
changes, and the leader of a slot that exists in two configurations is
the same validator in both. `Sched` is the `Slots` instance of one
configuration — `m` leaders in every pipelined round — built from the
core's `Slots.uniform`, so that the class obligations are discharged
once there.

`Slots.keyed` asks that the `m` leaders of a round be distinct
validators. `Keyed` is that obligation, stated of the leader function at
every count up to the cap, in the form `Slots.uniform` consumes; it is
implied by injectivity of `getLeader` on every window of `maxLeaders`
consecutive rounds (`Helpers/Schedule.lean`), which round-robin has
whenever `maxLeaders ≤ n`.

`Sched` is a `def`, never an instance: the arc's subject is several
schedules on one validator type, and every use names its own.

**Trusted core of the arc: definitions only.**
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type}

/-- **The leaders of a round are distinct**, at every count `m` up to `w`:
two slots of one round (`κ₁ / m = κ₂ / m`) with one leader are one slot.
Exactly the `hblock` obligation of `Slots.uniform`, and so exactly
`Slots.keyed` for the schedule below. -/
def Keyed (getLeader : ℕ → Validator) (w : ℕ) : Prop :=
  ∀ m, 0 < m → m ≤ w → ∀ κ₁ κ₂, κ₁ / m = κ₂ / m →
    getLeader (κ₁ / m + κ₁ % m) = getLeader (κ₂ / m + κ₂ % m) → κ₁ = κ₂

/-- **The schedule of a configuration with `m` leaders**: slot `κ` is
proposed at round `κ / m` with offset `κ % m`, led by
`getLeader (κ / m + κ % m)`. Pipelined, so `Slots.uniform` at period one.
Reducible, so that `simp` reads `slotRound` through
`Slots.uniform_slotRound`. -/
@[reducible] def Sched (getLeader : ℕ → Validator) {w : ℕ} (hk : Keyed getLeader w)
    (m : ℕ) (hm : 0 < m) (hmax : m ≤ w) : Slots Validator :=
  Slots.uniform 1 m Nat.one_pos hm (fun κ => getLeader (κ / m + κ % m)) (hk m hm hmax)

/-- Round-robin over `n` validators: round `r`'s first leader is `r % n`,
and slot `(r, l)` is led by `(r + l) % n`. The paper's `GetLeader`, and
the arc's witness schedule. -/
def roundRobin (n : ℕ) (hn : 0 < n) : ℕ → Fin n :=
  fun r => ⟨r % n, Nat.mod_lt r hn⟩

end Barnacle

end LeanDag
