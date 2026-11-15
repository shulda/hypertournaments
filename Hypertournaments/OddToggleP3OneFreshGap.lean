import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP3ActualOccupancies

/-!
# Exact one-excess gap identity for a genuine p3 all-block old packet

An old set U of m+1 vertices meeting every one of m old blocks
has m positive occupancies, summing to m+1. Subtracting the
baseline one vertex per block leaves an exact TOTAL GAP of one:
   Σ_i (occupancy(i)-1) = 1.
This records more than merely bounding the number of doubled
blocks. In particular, every occupancy is at most two and the
unique excess, if present, occurs in exactly one block.

This is an unconditional actual-Finset input for the remaining
all-m-blocks-present one-fresh packet age geometry.
-/

namespace Hypertournaments

/-- The exact positive-block occupancy excess is one on any
genuine all-m-block old subset of size m+1. -/
theorem p3ActualOneFresh_gap_sum_eq_one
    (m t : ℕ) (ht : 0 < t)
    (U : Finset (Fin (m*t)))
    (hsize : U.card = m+1)
    (hall : ∀ i : Fin m, 0 < p3BlockOccupancy m t U i) :
    (∑ i : Fin m, (p3BlockOccupancy m t U i - 1)) = 1 := by
  classical
  let occ : Fin m → ℕ := p3BlockOccupancy m t U
  have hpoint (i : Fin m) : (occ i - 1) + 1 = occ i := by
    have hp : 0 < occ i := hall i
    omega
  have hsum :
      (∑ i : Fin m, (occ i - 1)) + m =
      (∑ i : Fin m, occ i) := by
    calc
      (∑ i : Fin m, (occ i - 1)) + m =
          ∑ i : Fin m, ((occ i - 1) + 1) := by
            rw [Finset.sum_add_distrib]
            simp
      _ = ∑ i : Fin m, occ i := by
          apply Finset.sum_congr rfl
          intro i _
          exact hpoint i
  have htotal : (∑ i : Fin m, occ i) = m+1 := by
    change (∑ i : Fin m, p3BlockOccupancy m t U i) = m+1
    rw [p3BlockOccupancy_sum_eq_card m t ht U, hsize]
  rw [htotal] at hsum
  change (∑ i : Fin m, (occ i - 1)) = 1
  omega

/-- Every occupied block of an actual m+1 old packet has either
one or two vertices; a triple occupancy would use two excess
vertices and contradict the exact gap sum. -/
theorem p3ActualOneFresh_occ_le_two
    (m t : ℕ) (ht : 0 < t)
    (U : Finset (Fin (m*t)))
    (hsize : U.card = m+1)
    (hall : ∀ i : Fin m, 0 < p3BlockOccupancy m t U i)
    (i : Fin m) :
    p3BlockOccupancy m t U i ≤ 2 := by
  classical
  have hsum := p3ActualOneFresh_gap_sum_eq_one
    m t ht U hsize hall
  have hsingle :
      p3BlockOccupancy m t U i - 1 ≤
        (∑ j : Fin m, (p3BlockOccupancy m t U j - 1)) := by
    let f : Fin m → ℕ :=
      fun j => p3BlockOccupancy m t U j - 1
    change f i ≤ ∑ j : Fin m, f j
    exact Finset.single_le_sum
      (fun j _ => Nat.zero_le (f j)) (Finset.mem_univ i)
  have hpos := hall i
  omega

end Hypertournaments
