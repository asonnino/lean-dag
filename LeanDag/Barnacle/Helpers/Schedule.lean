import LeanDag.Barnacle.Model.Schedule
import Mathlib.Data.Nat.ModEq

/-!
# Schedule helpers

Lemma infrastructure for `Model/Schedule.lean`; not part of the audit
surface. `WindowInjective` is the readable form of the distinctness
obligation — injectivity of the leader function on every window of `w`
consecutive rounds — and `keyed_of_windowInjective` derives the form
`Sched` consumes from it. Round-robin is shown window-injective, hence
keyed, at every `n`.
-/

namespace LeanDag

namespace Barnacle

variable {Validator : Type}

/-- `getLeader` is injective on every window of `w` consecutive naturals. -/
def WindowInjective (getLeader : ℕ → Validator) (w : ℕ) : Prop :=
  ∀ r l₁ l₂, l₁ < w → l₂ < w → getLeader (r + l₁) = getLeader (r + l₂) → l₁ = l₂

/-- Window-injectivity gives `Keyed`: two slots of one round with one
leader have equal offsets (both below `m ≤ w`), and a natural is its
quotient and remainder. -/
theorem keyed_of_windowInjective {getLeader : ℕ → Validator} {w : ℕ}
    (hwin : WindowInjective getLeader w) : Keyed getLeader w := by
  intro m hm hmax κ₁ κ₂ hdiv hel
  have hel' : getLeader (κ₂ / m + κ₁ % m) = getLeader (κ₂ / m + κ₂ % m) := by
    simpa [hdiv] using hel
  have hmod : κ₁ % m = κ₂ % m :=
    hwin (κ₂ / m) (κ₁ % m) (κ₂ % m) (lt_of_lt_of_le (Nat.mod_lt _ hm) hmax)
      (lt_of_lt_of_le (Nat.mod_lt _ hm) hmax) hel'
  calc κ₁ = m * (κ₁ / m) + κ₁ % m := (Nat.div_add_mod κ₁ m).symm
    _ = m * (κ₂ / m) + κ₂ % m := by rw [hdiv, hmod]
    _ = κ₂ := Nat.div_add_mod κ₂ m

/-- Round-robin is injective on every window of `n` consecutive rounds:
the residues `(r + l) % n` for `l < n` are distinct. -/
theorem roundRobin_windowInjective (n : ℕ) (hn : 0 < n) :
    WindowInjective (roundRobin n hn) n := by
  intro r l₁ l₂ h₁ h₂ h
  have h' : (r + l₁) % n = (r + l₂) % n := congrArg Fin.val h
  have hm : l₁ % n = l₂ % n := Nat.ModEq.add_left_cancel' r h'
  rwa [Nat.mod_eq_of_lt h₁, Nat.mod_eq_of_lt h₂] at hm

/-- Round-robin is keyed at every count up to `n`. -/
theorem roundRobin_keyed (n : ℕ) (hn : 0 < n) : Keyed (roundRobin n hn) n :=
  keyed_of_windowInjective (roundRobin_windowInjective n hn)

end Barnacle

end LeanDag

namespace LeanDag

namespace Barnacle

variable {Validator : Type}

/-- `Sched`'s round is the quotient by the count. -/
@[simp] theorem Sched_slotRound (getLeader : ℕ → Validator) {w : ℕ} (hk : Keyed getLeader w)
    (m : ℕ) (hm : 0 < m) (hmax : m ≤ w) (κ : ℕ) :
    (Sched getLeader hk m hm hmax).slotRound κ = κ / m := by
  simp

/-- `Sched`'s leader. -/
theorem Sched_leader (getLeader : ℕ → Validator) {w : ℕ} (hk : Keyed getLeader w)
    (m : ℕ) (hm : 0 < m) (hmax : m ≤ w) (κ : ℕ) :
    (Sched getLeader hk m hm hmax).leader κ = getLeader (κ / m + κ % m) := rfl

/-- Two schedules with equal counts are equal, whatever their proof
arguments — the transport every agreement argument needs, since a run's
count is a projection and cannot be substituted. -/
theorem Sched_congr (getLeader : ℕ → Validator) {w : ℕ} (hk : Keyed getLeader w)
    {m₁ m₂ : ℕ} (h : m₁ = m₂) (h₁ : 0 < m₁) (h₁' : m₁ ≤ w) (h₂ : 0 < m₂) (h₂' : m₂ ≤ w) :
    Sched getLeader hk m₁ h₁ h₁' = Sched getLeader hk m₂ h₂ h₂' := by
  subst h; rfl

end Barnacle

end LeanDag
