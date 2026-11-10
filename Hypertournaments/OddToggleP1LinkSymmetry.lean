import Hypertournaments.OddToggleP1CanonicalLinks

/-!
# The canonical p1 pair-link tables are symmetric

The one-point extensions have their new vertex at the last position,
so their n-orientations containing that vertex are indexed by
*unordered* pairs of omitted base points. The canonical link
functions must therefore be symmetric, including all four
pad/core combinations. These identities are needed for uniform
row-parity calculations and for the defect-graph support.
-/

namespace Hypertournaments

theorem p1CoreLeftSymBit_comm (i j : Fin 6) :
    p1CoreLeftSymBit i j = p1CoreLeftSymBit j i := by
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    simp only [p1CoreLeftSymBit, if_neg h, if_neg h']
    rw [min_comm, max_comm]

theorem p1CoreRightSymBit_comm (i j : Fin 6) :
    p1CoreRightSymBit i j = p1CoreRightSymBit j i := by
  by_cases h : i = j
  · subst j
    rfl
  · have h' : j ≠ i := Ne.symm h
    simp only [p1CoreRightSymBit, if_neg h, if_neg h']
    rw [min_comm, max_comm]

/-- The full normalized canonical link table is symmetric in
the two omitted base vertices, including all pad/core cases. -/
theorem p1CanonicalLink_comm
    (k : ℕ) (left : Bool)
    (v w : Fin (4*k+6)) :
    p1CanonicalLink k left v w = p1CanonicalLink k left w v := by
  by_cases hv : v.val < 4*k
  · by_cases hw : w.val < 4*k
    · simp [p1CanonicalLink, hv, hw]
    · simp [p1CanonicalLink, hv, hw]
  · by_cases hw : w.val < 4*k
    · simp [p1CanonicalLink, hv, hw]
    · cases left
      · simp only [p1CanonicalLink, hv, hw, dite_false, Bool.false_eq_true,
          ↓reduceIte]
        exact p1CoreRightSymBit_comm _ _
      · simp only [p1CanonicalLink, hv, hw, dite_false, Bool.true_eq_true,
          ↓reduceIte]
        exact p1CoreLeftSymBit_comm _ _

end Hypertournaments
