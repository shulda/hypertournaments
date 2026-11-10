import Hypertournaments.CanonicalSignPresentation
import Hypertournaments.CanonicalPacket

/-!
# Facet signs of arbitrary intrinsic hypertournaments in increasing coordinates

On an increasing (n+1)-tuple, the actual orientation of the i-th
n-facet equals the intrinsic canonical unordered sign on the
finite n-set obtained by erasing the i-th vertex. This is uniform
in arity and needs no admissibility or amalgamation premises.
-/

namespace Hypertournaments

theorem Hyper.orient_facet_eq_canonical_erase
    {n a : ℕ} (A : Hyper n (Fin a))
    (f : Fin (n+1) ↪o Fin a) (i : Fin (n+1)) :
    A.orient (facet f.toEmbedding i) =
      A.canonicalSignTable
        ((tupleVertices f.toEmbedding).erase (f i)) := by
  calc
    A.orient (facet f.toEmbedding i) =
        (Hyper.fromOrderedSigns A.canonicalSignTable).orient
          (facet f.toEmbedding i) :=
      (A.from_canonicalSignTable_orient
        (facet f.toEmbedding i)).symm
    _ = A.canonicalSignTable
          (tupleVertices (facet f.toEmbedding i)) :=
      fromOrderedSigns_facet_increasing A.canonicalSignTable f i
    _ = A.canonicalSignTable
          ((tupleVertices f.toEmbedding).erase (f i)) := by
      rw [tupleVertices_facet_eq_erase]

end Hypertournaments
