import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3OccupancyExcess
import Hypertournaments.OddToggleP3ExplicitPotentials

/-!
# Actual p3 block occupancy counts exhaust the old vertex set

The old base consists of m contiguous blocks of t vertices.
For t>0, the quotient v.val/t is a genuine Fin m index.
The fibers of the block map partition every finite old subset U:
the sum of p3BlockOccupancy over all m indices equals |U|.

Combining this exact fiber-cardinality identity with the previously
proved arithmetic two-point excess bound, every old packet with
m+2 points meeting all m blocks has at most two nonsingleton blocks.
This bridges the abstract excess lemma to the actual constructed
old vertex set of the random p3 obstruction.
-/

namespace Hypertournaments

/-- The canonical block label of an old vertex, as a valid element
of Fin m. Positivity of the block size is an explicit premise. -/
def p3BlockLabel (m t : ℕ) (ht : 0 < t)
    (v : Fin (m*t)) : Fin m :=
  ⟨p3BlockNumber t v, by
    have hv : v.val < m*t := v.isLt
    change v.val / t < m
    exact (Nat.div_lt_iff_lt_mul ht).mpr hv⟩

/-- The block occupancy fibers form a partition: summing their
exact cardinalities counts each old vertex precisely once. -/
theorem p3BlockOccupancy_sum_eq_card
    (m t : ℕ) (ht : 0 < t)
    (U : Finset (Fin (m*t))) :
    (∑ i : Fin m, p3BlockOccupancy m t U i) = U.card := by
  classical
  have hfib :
      (∑ i : Fin m,
        (U.filter (fun v => p3BlockLabel m t ht v = i)).card) =
        U.card := by
    simpa using
      (Finset.sum_card_fiberwise_eq_card_filter
        U (Finset.univ : Finset (Fin m)) (p3BlockLabel m t ht))
  calc
    (∑ i : Fin m, p3BlockOccupancy m t U i) =
        ∑ i : Fin m,
          (U.filter (fun v => p3BlockLabel m t ht v = i)).card := by
      apply Finset.sum_congr rfl
      intro i _
      apply congrArg Finset.card
      ext v
      simp only [p3BlockOccupancy, Finset.mem_filter]
      simp [p3BlockLabel, p3BlockNumber, Fin.ext_iff]
    _ = U.card := hfib

/-- Exactly m+2 old vertices occupying all m blocks imply that
no more than two actual blocks are nonsingleton. -/
theorem p3ActualBlock_nonSingleton_le_two
    (m t : ℕ) (ht : 0 < t)
    (U : Finset (Fin (m*t)))
    (hsize : U.card = m+2)
    (hall : ∀ i : Fin m, 0 < p3BlockOccupancy m t U i) :
    (Finset.univ.filter
      (fun i : Fin m => 1 < p3BlockOccupancy m t U i)).card ≤ 2 := by
  apply p3AtMostTwoNonSingletonOfTwoExcess m
    (p3BlockOccupancy m t U) hall
  rw [p3BlockOccupancy_sum_eq_card m t ht U, hsize]

end Hypertournaments
