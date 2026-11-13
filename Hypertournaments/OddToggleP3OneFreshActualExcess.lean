import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP3ProtectedTriple
import Hypertournaments.OddToggleP3ActualOccupancies

/-!
# Actual all-block p3 fresh-packet occupancy has only one excess

In a fresh-containing packet of an arity-(m+1) hypertournament
there are m+1 old vertices. If all m old blocks are occupied,
their exact finite fibers have total excess one, not two.
Consequently at most ONE block is nonsingleton, for every
positive block size and every genuine old subset U.

This is the starting finite-set bridge for the remaining
q=m occupied-block case. The protected-half singleton parity
positions and actual side raw-zero facet transfer remain separate.
-/

namespace Hypertournaments

/-- In an actual old subset U with m+1 vertices occupying all
m blocks, at most one block can have occupancy greater than one. -/
theorem p3ActualOneFresh_nonSingleton_le_one
    (m t : ℕ) (ht : 0 < t)
    (U : Finset (Fin (m*t)))
    (hsize : U.card = m+1)
    (hall : ∀ i : Fin m, 0 < p3BlockOccupancy m t U i) :
    (Finset.univ.filter
      (fun i : Fin m => 1 < p3BlockOccupancy m t U i)).card ≤ 1 := by
  apply p3NonSingleton_count_le_excess
    m 1 (p3BlockOccupancy m t U) hall
  rw [p3BlockOccupancy_sum_eq_card m t ht U, hsize]

/-- No two distinct old block labels can both be nonsingleton in
a concrete all-block one-fresh p3 packet. -/
theorem p3ActualOneFresh_no_two_double_blocks
    (m t : ℕ) (ht : 0 < t)
    (U : Finset (Fin (m*t)))
    (hsize : U.card = m+1)
    (hall : ∀ i : Fin m, 0 < p3BlockOccupancy m t U i)
    (i j : Fin m) (hij : i ≠ j)
    (hi : 1 < p3BlockOccupancy m t U i)
    (hj : 1 < p3BlockOccupancy m t U j) : False := by
  let bad : Finset (Fin m) :=
    Finset.univ.filter
      (fun b : Fin m => 1 < p3BlockOccupancy m t U b)
  have hbad : bad.card ≤ 1 :=
    p3ActualOneFresh_nonSingleton_le_one m t ht U hsize hall
  have hsubset : ({i,j} : Finset (Fin m)) ⊆ bad := by
    intro x hx
    have heq : x = i ∨ x = j := by simpa using hx
    rcases heq with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
  have htwo : ({i,j} : Finset (Fin m)).card = 2 := by
    simp [hij, Ne.symm hij]
  have hle := Finset.card_le_card hsubset
  omega

end Hypertournaments
