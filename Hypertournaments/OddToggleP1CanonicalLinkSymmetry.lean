import Hypertournaments.OddToggleP1CanonicalLinks

/-!
# Symmetry and diagonal of canonical p1 link matrices

The canonical left/right one-point sign tables depend on unordered
pairs of omitted base vertices. Their link table was defined by
cases according to whether the two vertices are auxiliary pads
or belong to the six-vertex core.

These elementary intrinsic table identities are useful for
replacing unordered-pair sums by row counts during the all-arity
side-admissibility argument. Neither is an AP or admissibility claim.
-/

namespace Hypertournaments

/-- The finite six-core left and right link tables are symmetric
since they depend only on the unordered pair of core vertices. -/
theorem p1CoreLeftSymBit_comm (x y : Fin 6) :
    p1CoreLeftSymBit x y = p1CoreLeftSymBit y x := by
  unfold p1CoreLeftSymBit
  by_cases h : x = y
  · subst y
    rfl
  · have h' : y ≠ x := Ne.symm h
    simp [h, h', min_comm, max_comm]

theorem p1CoreRightSymBit_comm (x y : Fin 6) :
    p1CoreRightSymBit x y = p1CoreRightSymBit y x := by
  unfold p1CoreRightSymBit
  by_cases h : x = y
  · subst y
    rfl
  · have h' : y ≠ x := Ne.symm h
    simp [h, h', min_comm, max_comm]

/-- Each p1 canonical side link table is symmetric in its two
omitted base vertices. -/
theorem p1CanonicalLink_symmetric
    (k : ℕ) (left : Bool)
    (v w : Fin (4*k+6)) :
    p1CanonicalLink k left v w =
      p1CanonicalLink k left w v := by
  by_cases hv : v.val < 4*k
  · by_cases hw : w.val < 4*k
    · simp [p1CanonicalLink, hv, hw]
    · simp [p1CanonicalLink, hv, hw]
  · by_cases hw : w.val < 4*k
    · simp [p1CanonicalLink, hv, hw]
    · have hleft : ∀ (x y : Fin 6),
          p1CoreLeftSymBit x y = p1CoreLeftSymBit y x :=
        p1CoreLeftSymBit_comm
      have hright : ∀ (x y : Fin 6),
          p1CoreRightSymBit x y = p1CoreRightSymBit y x :=
        p1CoreRightSymBit_comm
      simp only [p1CanonicalLink, dif_neg hv, dif_neg hw]
      cases left
      · exact hright _ _
      · exact hleft _ _

/-- Diagonal link entries are irrelevant to the missing-pair
construction and have been fixed to false on both sides. -/
theorem p1CanonicalLink_diagonal_false
    (k : ℕ) (left : Bool) (v : Fin (4*k+6)) :
    p1CanonicalLink k left v v = false := by
  by_cases hv : v.val < 4*k
  · simp [p1CanonicalLink, hv]
  · simp [p1CanonicalLink, hv, p1CoreLeftSymBit,
      p1CoreRightSymBit]

end Hypertournaments
