import Hypertournaments.EvenSuspensionTwoThreeFacets
import Hypertournaments.CanonicalPacket

/-!
# Intrinsic facet orientations of increasing even-suspension packets

The raw set-sign calculations for pad counts 0,1,2,3 and >=4
are now connected to the *actual* n+2-orientation of each increasing
(n+3)-tuple's facets. The key bridge is that every facet of an
increasing tuple is increasing, and its underlying vertex set is
the parent vertex set with the deleted vertex removed.

No assertion about arbitrary-order packet local types is made here.
-/

namespace Hypertournaments

/-- Exact concrete raw orientation of every facet of an increasing
packet, read from the finite sign table after erasing its vertex. -/
theorem Hyper.evenSuspension_orient_increasingFacet
    {n m k : ℕ} (A : Hyper n (Fin k))
    (f : Fin (n + 3) ↪o Fin (m + k))
    (i : Fin (n + 3)) :
    (A.evenSuspension m k).orient (facet f.toEmbedding i) =
      evenSuspensionSignTable m k A
        ((tupleVertices f.toEmbedding).erase (f i)) := by
  calc
    (A.evenSuspension m k).orient (facet f.toEmbedding i) =
        evenSuspensionSignTable m k A
          (tupleVertices (facet f.toEmbedding i)) :=
      fromOrderedSigns_facet_increasing
        (evenSuspensionSignTable m k A) f i
    _ = evenSuspensionSignTable m k A
        ((tupleVertices f.toEmbedding).erase (f i)) := by
      simpa using congrArg (evenSuspensionSignTable m k A)
        (tupleVertices_facet_eq_erase f.toEmbedding i)

/-- For pad count <= 1 or >= 4 every raw facet orientation of an
increasing packet is positive. -/
theorem Hyper.evenSuspension_orient_increasingFacet_far
    {n m k : ℕ} (A : Hyper n (Fin k))
    (f : Fin (n + 3) ↪o Fin (m + k))
    (hcount :
      (evenPadProjection m k (tupleVertices f.toEmbedding)).card ≤ 1 ∨
      4 ≤ (evenPadProjection m k (tupleVertices f.toEmbedding)).card)
    (i : Fin (n + 3)) :
    (A.evenSuspension m k).orient (facet f.toEmbedding i) = true := by
  rw [A.evenSuspension_orient_increasingFacet f i]
  exact evenSuspensionSignTable_facet_positive
    m k A (tupleVertices f.toEmbedding) hcount (f i)

/-- For a three-pad packet, deleting any present pad reads exactly
the same old canonical n-sign for all three pad facets. -/
theorem Hyper.evenSuspension_orient_increasingFacet_pad_three
    {n m k : ℕ} (A : Hyper n (Fin k))
    (f : Fin (n + 3) ↪o Fin (m + k))
    (hthree :
      (evenPadProjection m k (tupleVertices f.toEmbedding)).card = 3)
    (p : Fin m)
    (hp : p ∈ evenPadProjection m k (tupleVertices f.toEmbedding))
    (i : Fin (n + 3)) (hi : f i = evenPadShift m k p) :
    (A.evenSuspension m k).orient (facet f.toEmbedding i) =
      A.canonicalSignTable
        (evenOldProjection m k (tupleVertices f.toEmbedding)) := by
  rw [A.evenSuspension_orient_increasingFacet f i, hi]
  exact evenSuspensionSignTable_erase_pad_three
    m k A (tupleVertices f.toEmbedding) hthree p hp

/-- All nonpad facet deletions of a three-pad packet are positive. -/
theorem Hyper.evenSuspension_orient_increasingFacet_nonpad_three
    {n m k : ℕ} (A : Hyper n (Fin k))
    (f : Fin (n + 3) ↪o Fin (m + k))
    (hthree :
      (evenPadProjection m k (tupleVertices f.toEmbedding)).card = 3)
    (i : Fin (n + 3))
    (hi : f i ∉ Set.range (evenPadShift m k)) :
    (A.evenSuspension m k).orient (facet f.toEmbedding i) = true := by
  rw [A.evenSuspension_orient_increasingFacet f i]
  exact evenSuspensionSignTable_erase_nonpad_three
    m k A (tupleVertices f.toEmbedding) hthree (f i) hi

/-- Both padding-vertex deletions of a two-pad packet are positive. -/
theorem Hyper.evenSuspension_orient_increasingFacet_pad_two
    {n m k : ℕ} (A : Hyper n (Fin k))
    (f : Fin (n + 3) ↪o Fin (m + k))
    (htwo :
      (evenPadProjection m k (tupleVertices f.toEmbedding)).card = 2)
    (p : Fin m)
    (hp : p ∈ evenPadProjection m k (tupleVertices f.toEmbedding))
    (i : Fin (n + 3)) (hi : f i = evenPadShift m k p) :
    (A.evenSuspension m k).orient (facet f.toEmbedding i) = true := by
  rw [A.evenSuspension_orient_increasingFacet f i, hi]
  exact evenSuspensionSignTable_erase_pad_two
    m k A (tupleVertices f.toEmbedding) htwo p hp

/-- In a two-pad packet, deleting an old vertex reads the old
source sign after deleting precisely that old vertex. -/
theorem Hyper.evenSuspension_orient_increasingFacet_old_two
    {n m k : ℕ} (A : Hyper n (Fin k))
    (f : Fin (n + 3) ↪o Fin (m + k))
    (htwo :
      (evenPadProjection m k (tupleVertices f.toEmbedding)).card = 2)
    (u : Fin k) (i : Fin (n + 3))
    (hi : f i = evenOldShift m k u) :
    (A.evenSuspension m k).orient (facet f.toEmbedding i) =
      A.canonicalSignTable
        ((evenOldProjection m k (tupleVertices f.toEmbedding)).erase u) := by
  rw [A.evenSuspension_orient_increasingFacet f i, hi]
  exact evenSuspensionSignTable_erase_old_two
    m k A (tupleVertices f.toEmbedding) htwo u

end Hypertournaments
