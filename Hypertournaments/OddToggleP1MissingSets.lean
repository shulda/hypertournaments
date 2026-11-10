import Hypertournaments.OddToggleP1ExplicitSides

/-!
# Exact one- and two-omission interpretations of p1 finite sign tables

The explicit p1 source tables are defined by a finite XOR of base
bits over missing old vertices, or of canonical link bits over
unordered pairs of omitted old vertices. This module proves that
the generic Finset definitions have exactly the desired concrete
meaning on the one-omission and two-omission subsets relevant to
actual n-facets.

No admissibility or AP theorem is asserted here.
-/

namespace Hypertournaments

/-- On a single missing old base vertex, the finite XOR is exactly
its prescribed raw base sign. -/
theorem p1BaseMissingBit_singleton
    (k : ℕ) (v : Fin (4*k+6)) :
    p1BaseMissingBit k ({v} : Finset (Fin (4*k+6))) =
      p1BaseVertexBit k v := by
  simp only [p1BaseMissingBit, Finset.filter_singleton]
  cases hv : p1BaseVertexBit k v <;> simp [hv]

/-- Deleting one vertex from the complete old base recovers its
prescribed base sign on the corresponding genuine n-subset. -/
theorem p1BaseSignTable_erase
    (k : ℕ) (v : Fin (4*k+6)) :
    p1BaseSignTable k
      ((Finset.univ : Finset (Fin (4*k+6))).erase v) =
      p1BaseVertexBit k v := by
  have hmissing :
      ((Finset.univ : Finset (Fin (4*k+6))) \
        (Finset.univ.erase v)) = {v} := by
    ext u
    simp [eq_comm]
  unfold p1BaseSignTable
  rw [hmissing]
  exact p1BaseMissingBit_singleton k v

/-- If exactly two distinct old base vertices are missing, their
finite XOR link contribution is exactly the corresponding
ordered canonical link bit. -/
theorem p1PairMissingBit_pair
    (k : ℕ) (left : Bool)
    (v w : Fin (4*k+6)) (hvw : v < w) :
    p1PairMissingBit k left ({v,w} : Finset (Fin (4*k+6))) =
      p1CanonicalLink k left v w := by
  have hvne : v ≠ w := ne_of_lt hvw
  have hwnot : ¬w < v := not_lt.mpr (le_of_lt hvw)
  unfold p1PairMissingBit
  cases hlink : p1CanonicalLink k left v w <;>
    simp [Finset.filter_insert, Finset.filter_singleton, hvw, hvne, hwnot, hlink]

end Hypertournaments
