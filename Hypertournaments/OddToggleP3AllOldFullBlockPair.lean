import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3SortedBlockFibers
import Hypertournaments.OddToggleP3FirstSixSingletonPair
import Hypertournaments.OddToggleP3SingletonPositions

/-!
# Two genuine opposite-parity singleton facets in full old packets

For every old packet U of size m+2 meeting all m consecutive old
blocks, with m≥6 and t>0, the exact actual block occupancy fibers
have only two excess vertices. Therefore one of the first three
adjacent block pairs (0,1),(2,3),(4,5) is singleton in both blocks.
The canonical increasing enumeration of U has monotone numerical
block labels, and its fiber cardinalities agree with these
occupancies. The two singleton vertices thus occur at adjacent
sorted positions of opposite deletion parity.

This proves the mathematical POSITION half of the full old-block
p3 side-age argument on genuine canonical finite vertex subsets.
The raw-zero orientation facet transfer remains separate.
-/

namespace Hypertournaments

/-- A full m+2 old packet meeting every block contains two
consecutive singleton labels whose unique old vertices occupy
opposite-parity positions of its increasing enumeration. -/
theorem p3AllOldFullBlocks_two_singletons_oppositeParity
    (m t : ℕ) (hm : 6 ≤ m) (ht : 0 < t)
    (U : Finset (Fin (m*t)))
    (hU : U.card = m+2)
    (hall : ∀ i : Fin m, 0 < p3BlockOccupancy m t U i) :
    ∃ i j : Fin m,
      j.val = i.val + 1 ∧
      p3BlockOccupancy m t U i = 1 ∧
      p3BlockOccupancy m t U j = 1 ∧
      ∃ x y : Fin (m+2),
        p3BlockNumber t (U.orderEmbOfFin hU x) = i.val ∧
        p3BlockNumber t (U.orderEmbOfFin hU y) = j.val ∧
        decide (x.val%2=1) ≠ decide (y.val%2=1) := by
  classical
  let occ : Fin m → ℕ := p3BlockOccupancy m t U
  have hsum : (∑ a : Fin m, occ a) = m+2 := by
    change (∑ a : Fin m, p3BlockOccupancy m t U a) = m+2
    rw [p3BlockOccupancy_sum_eq_card m t ht U, hU]
  obtain ⟨q, hq0, hq1⟩ :=
    p3FirstSixSingletonPair_of_twoExcess m hm occ hall hsum
  let i : Fin m := ⟨2*q.val, by have hlt := q.isLt; omega⟩
  let j : Fin m := ⟨2*q.val+1, by have hlt := q.isLt; omega⟩
  have hstep : j.val = i.val + 1 := rfl
  have hi : p3BlockOccupancy m t U i = 1 := by
    have heq :
        p3FirstSixEmbedding m hm
          (⟨2*q.val, by omega⟩ : Fin 6) = i := by
      apply Fin.ext
      rfl
    rw [heq] at hq0
    exact hq0
  have hj : p3BlockOccupancy m t U j = 1 := by
    have heq :
        p3FirstSixEmbedding m hm
          (⟨2*q.val+1, by omega⟩ : Fin 6) = j := by
      apply Fin.ext
      rfl
    rw [heq] at hq1
    exact hq1
  let B : Fin (m+2) → ℕ :=
    fun x => p3BlockNumber t (U.orderEmbOfFin hU x)
  have hmono : Monotone B :=
    p3SortedOldPacket_block_monotone U hU
  have hcardi :
      (Finset.univ.filter (fun x : Fin (m+2) => B x = i.val)).card = 1 := by
    change (Finset.univ.filter
      (fun x : Fin (m+2) =>
        p3BlockNumber t (U.orderEmbOfFin hU x) = i.val)).card = 1
    rw [p3SortedOldPacket_fiber_card_eq_occupancy m t (m+2) U hU i]
    exact hi
  have hcardj :
      (Finset.univ.filter
        (fun x : Fin (m+2) => B x = i.val+1)).card = 1 := by
    change (Finset.univ.filter
      (fun x : Fin (m+2) =>
        p3BlockNumber t (U.orderEmbOfFin hU x) = j.val)).card = 1
    rw [p3SortedOldPacket_fiber_card_eq_occupancy m t (m+2) U hU j]
    exact hj
  obtain ⟨x, y, hx, hy, _, hpar⟩ :=
    p3ConsecutiveSingletonFibers_oppositeParity
      (m+2) B hmono i.val hcardi hcardj
  refine ⟨i, j, hstep, hi, hj, x, y, ?_, ?_, hpar⟩
  · exact hx
  · simpa only [hstep] using hy

end Hypertournaments
