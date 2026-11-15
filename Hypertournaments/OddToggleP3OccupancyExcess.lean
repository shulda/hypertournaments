import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP3SixBlockGeometry

/-!
# Excess budget for the actual p3 block-occupancy case split

If m blocks are all occupied by an old packet with m+2 points,
write occ(i) for the positive occupancy of each block.
The excess budget is exactly two. Hence at most two blocks
can have occupancy at least two.

This is the arithmetic part of the all-old protected-facet
selection lemma. The remaining concrete bridge sums the actual
Finset.filter fiber cardinalities and shows they equal the packet's
old-point count.
-/

namespace Hypertournaments

/-- In an m-block packet with all block occupancies positive and total
size m+2, at most two blocks are nonsingleton. No bounded-size
enumeration or nonstandard axiom is needed. -/
theorem p3AtMostTwoNonSingletonOfTwoExcess
    (m : ℕ) (occ : Fin m → ℕ)
    (hpositive : ∀ i : Fin m, 0 < occ i)
    (htotal : (∑ i : Fin m, occ i) = m+2) :
    (Finset.univ.filter (fun i : Fin m => 1 < occ i)).card ≤ 2 := by
  classical
  let bad : Finset (Fin m) :=
    Finset.univ.filter (fun i : Fin m => 1 < occ i)
  have hpoint (i : Fin m) :
      1 + (if 1 < occ i then (1 : ℕ) else 0) ≤ occ i := by
    by_cases hb : 1 < occ i
    · simp only [if_pos hb]
      omega
    · simp only [if_neg hb]
      have hp := hpositive i
      omega
  have hsum :
      (∑ i : Fin m, ((1 : ℕ) + if 1 < occ i then 1 else 0)) ≤
        ∑ i : Fin m, occ i := by
    apply Finset.sum_le_sum
    intro i _
    exact hpoint i
  have hfilter :
      (∑ i : Fin m, (if 1 < occ i then (1 : ℕ) else 0)) =
        bad.card := by
    calc
      (∑ i : Fin m, (if 1 < occ i then (1 : ℕ) else 0)) =
          ∑ i ∈ (Finset.univ.filter (fun i : Fin m => 1 < occ i)),
            (1 : ℕ) := by
              rw [Finset.sum_filter]
      _ = bad.card := by
        simp [bad]
  have hsumEq :
      (∑ i : Fin m, ((1 : ℕ) + if 1 < occ i then 1 else 0)) =
        m + bad.card := by
    rw [Finset.sum_add_distrib, hfilter]
    simp
  rw [hsumEq, htotal] at hsum
  simpa only [bad] using (show bad.card ≤ 2 by omega)

end Hypertournaments
