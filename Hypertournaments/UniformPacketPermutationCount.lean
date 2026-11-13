import Lean.Elab.Tactic.Omega
import Hypertournaments.TwoPadPacketCount

/-!
# Uniform permutation and complement invariance of packet minority counts

For a Boolean packet of any finite length, the number of positive
entries is invariant under permutations of positions, and simultaneous
complementation replaces the positive count c by m-c. Therefore the
minority count is unchanged by any permutation, possibly followed
by simultaneous complementation.

This is exactly the Boolean last step needed after proving the
facet-relabeling law for intrinsic hypertournaments in all arities.
It does NOT itself assert the general geometric facet law.
-/

namespace Hypertournaments

/-- Permuting the coordinates of any Boolean packet preserves the
number of positive entries, uniformly in packet length. -/
theorem boolPacketPositiveCount_perm {m : ℕ}
    (bits : Fin m → Bool) (σ : Equiv.Perm (Fin m)) :
    boolPacketPositiveCount (fun i => bits (σ i)) =
      boolPacketPositiveCount bits := by
  simp only [boolPacketPositiveCount_eq_sum]
  exact Equiv.sum_comp σ (fun i : Fin m =>
    if bits i then (1 : ℕ) else 0)

/-- Complementing all Boolean entries replaces the positive count c
by m-c. This holds even at packet length zero. -/
theorem boolPacketPositiveCount_not {m : ℕ}
    (bits : Fin m → Bool) :
    boolPacketPositiveCount (fun i => !bits i) =
      m - boolPacketPositiveCount bits := by
  have hpoint (i : Fin m) :
      (if !bits i then (1 : ℕ) else 0) +
      (if bits i then (1 : ℕ) else 0) = 1 := by
    cases bits i <;> decide
  have hsum :
      boolPacketPositiveCount (fun i => !bits i) +
        boolPacketPositiveCount bits = m := by
    rw [boolPacketPositiveCount_eq_sum, boolPacketPositiveCount_eq_sum]
    rw [← Finset.sum_add_distrib]
    calc
      (∑ i : Fin m, ((if !bits i then (1 : ℕ) else 0) +
                        (if bits i then (1 : ℕ) else 0))) =
          ∑ _i : Fin m, (1 : ℕ) := by
        apply Finset.sum_congr
        · rfl
        · intro i _
          exact hpoint i
      _ = m := by simp
  omega

/-- The raw Boolean minority statistic is invariant under arbitrary
permutations, not only adjacent swaps. -/
theorem boolPacketMinority_perm {m : ℕ}
    (bits : Fin m → Bool) (σ : Equiv.Perm (Fin m)) :
    min (boolPacketPositiveCount (fun i => bits (σ i)))
          (m - boolPacketPositiveCount (fun i => bits (σ i))) =
      min (boolPacketPositiveCount bits)
          (m - boolPacketPositiveCount bits) := by
  rw [boolPacketPositiveCount_perm]

/-- A simultaneous complement and arbitrary permutation preserves
the minority count, uniformly in arity. -/
theorem boolPacketMinority_perm_complement {m : ℕ}
    (bits : Fin m → Bool) (σ : Equiv.Perm (Fin m)) :
    min (boolPacketPositiveCount (fun i => !(bits (σ i))))
          (m - boolPacketPositiveCount (fun i => !(bits (σ i)))) =
      min (boolPacketPositiveCount bits)
          (m - boolPacketPositiveCount bits) := by
  rw [boolPacketPositiveCount_not, boolPacketPositiveCount_perm]
  have hbound := boolPacketPositiveCount_le bits
  omega

end Hypertournaments
