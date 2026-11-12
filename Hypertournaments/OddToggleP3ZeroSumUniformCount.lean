import Hypertournaments.OddToggleP3UniformSourceCounting
import Hypertournaments.OddToggleP3ZeroSumCount

/-!
# Exact uniform counting on the p3 zero-sum transversal source code

The selected source coordinates consist of a zero-sum tuple of
m+1 group elements and one deleted coordinate. Their total number
is (m+1)*|G|^m, by the already kernel-proved zero-sum tuple count.

The punctured-source index maps these selected coordinates
injectively into the full potential-source index set. Applying
the generic finite fiber-counting identity gives the exact
cardinality of every prescribed selected-bit pattern. This
is the precise finite independence counting needed by the p3
random nonamalgamation argument.

This is a natural-number count; we do not claim a probability
measure or that any actual amalgamation fails in this module.
-/

namespace Hypertournaments

/-- The number of actual selected (zero-sum transversal,
deleted coordinate) source coordinates is exactly
(m+1)·|G|^m. -/
theorem p3ZeroSumSelectedSource_card
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (m : ℕ) :
    Fintype.card
      ({q : Fin (m+1) → G // (∑ i : Fin (m+1), q i) = 0} ×
        Fin (m+1)) =
      (m+1) * (Fintype.card G)^m := by
  classical
  rw [Fintype.card_prod, p3ZeroSumTuple_card]
  simp [mul_comm]

/-- Every selected zero-sum source bit pattern has exactly the
same full-assignment fiber cardinality, characterized by the
finite Boolean product equation. -/
theorem p3ZeroSumSelectedSource_exact_uniform_count
    {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]
    (m : ℕ)
    (target :
      ({q : Fin (m+1) → G // (∑ i : Fin (m+1), q i) = 0} ×
        Fin (m+1)) → Bool) :
    2 ^ (Fintype.card
      (Fin (m+1) × (Fin (m+1) → G))) =
      2 ^ ((m+1) * (Fintype.card G)^m) *
        Nat.card
          {values : (Fin (m+1) × (Fin (m+1) → G)) → Bool //
            (fun qi :
              {q : Fin (m+1) → G // (∑ i : Fin (m+1), q i) = 0} ×
                Fin (m+1) =>
              values (p3RandomSourceIndex m qi.1 qi.2)) = target} := by
  classical
  have h :=
    p3BoolRestriction_exact_fiber_count
      (fun qi :
        {q : Fin (m+1) → G // (∑ i : Fin (m+1), q i) = 0} ×
          Fin (m+1) =>
        p3RandomSourceIndex m qi.1 qi.2)
      (p3RandomSourceIndex_injective m) target
  rw [p3ZeroSumSelectedSource_card] at h
  exact h

end Hypertournaments
