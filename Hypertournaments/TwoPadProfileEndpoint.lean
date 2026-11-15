import Hypertournaments.TwoPadSlice

/-!
# Identical one-pad raw profiles give opposite normalized endpoint signs

For an ambient (n+3)-tuple, the first two facets are obtained by
deleting one of the two pad coordinates. Their normalized signs have
opposite parity factors (indices 0 and 1).

Consequently equality of the corresponding *raw* orientations is
equivalent to inequality of the normalized first two facets. This is
exactly what the finite-profile pigeonhole step supplies when two
pad vertices have the same one-pad mixed profile.

The statement and proof work in every arity, without a chosen vertex
order or any admissibility assumption.
-/

namespace Hypertournaments

/-- The first two normalized facet signs are opposite if and only
if the corresponding unnormalized orientations agree. -/
theorem normalized_first_two_opposite_iff_raw_equal
    {n : ℕ} {V : Type*}
    (D : Hyper (n + 2) V) (f : Fin (n + 3) ↪ V) :
    normalizedFacet D f 0 ≠ normalizedFacet D f 1 ↔
      D.orient (facet f 0) = D.orient (facet f 1) := by
  cases h0 : D.orient (facet f 0) <;>
    cases h1 : D.orient (facet f 1) <;>
      simp [normalizedFacet, h0, h1]

/-- A conveniently oriented implication used when a pair of equal
one-pad mixed profiles has been found by pigeonhole. -/
theorem normalized_first_two_opposite_of_raw_equal
    {n : ℕ} {V : Type*}
    (D : Hyper (n + 2) V) (f : Fin (n + 3) ↪ V)
    (heq : D.orient (facet f 0) = D.orient (facet f 1)) :
    normalizedFacet D f 0 ≠ normalizedFacet D f 1 :=
  (normalized_first_two_opposite_iff_raw_equal D f).mpr heq

end Hypertournaments
