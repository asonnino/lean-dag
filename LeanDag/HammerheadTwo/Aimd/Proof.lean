import LeanDag.HammerheadTwo.Aimd.Statement

/-!
# HH7 — proof

Generated proof layer; not part of the audit surface. Case analysis on
the two branches of `update` and the guard of `rule`; the arithmetic
of `min`, `max`, truncated subtraction and `2 ^ backoff ≥ 1`.
-/

namespace LeanDag

namespace HammerheadTwo

namespace Aimd

theorem holds : Statement := by
  intro Validator BlockId Payload _ _ _ R P getLeader hk
  have hpow : ∀ b : ℕ, 1 ≤ 2 ^ b := fun b => Nat.one_le_two_pow
  refine ⟨?_, ⟨?_, ?_⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · -- HH7a: bounds.
    intro m backoff U A
    unfold rule
    split_ifs with hm
    · unfold update
      split_ifs
      · exact ⟨lt_min (Nat.succ_pos m) P.max_pos, Nat.min_le_right _ _⟩
      · exact ⟨lt_of_lt_of_le Nat.one_pos (le_max_right _ _),
          max_le (le_trans (Nat.sub_le _ _) hm.2) P.max_pos⟩
    · exact ⟨Nat.one_pos, P.max_pos⟩
  · -- HH7b: healthy, below the cap.
    intro m backoff h
    simp [update, Nat.min_eq_left h]
  · -- HH7b: at the cap.
    intro backoff
    simp [update]
  · -- HH7c: unhealthy, above the floor.
    intro m backoff h
    have := hpow backoff
    refine ⟨?_, rfl⟩
    simp only [update, if_false]
    exact max_lt (Nat.sub_lt (by omega) (by omega)) h
  · -- HH7c: the step.
    intro m backoff h
    simp only [update, if_false]
    exact Nat.max_eq_left (by omega)
  · -- HH7c: the floor.
    intro backoff
    have := hpow backoff
    simp only [update, if_false]
    rw [Nat.sub_eq_zero_of_le this]
    rfl
  · -- HH7d: the test.
    intro m backoff hm hmax U A
    unfold rule
    rw [dif_pos ⟨hm, hmax⟩]

end Aimd

end HammerheadTwo

end LeanDag
