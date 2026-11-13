import Hypertournaments.CanonicalPacket
import Hypertournaments.CanonicalSignPresentation

/-!
# The genuine raw sign of an increasing intrinsic facet is its canonical finite-set sign

For any intrinsic hypertournament E and any strictly increasing
(n+1)-tuple f, each facet f minus its i-th vertex is itself
increasing. Therefore its genuine orientation, with the original
alternation law, is exactly the canonical sign table evaluated
on the literal underlying n-set (parent tuple vertices erase f(i)).

The proof reuses the kernel-certified complete canonical
presentation and the finite-set facet erasure lemma. This is
the precise general transport needed when turning actual
source-based mixed-facet signs into a forbidden raw local
packet, without silently assigning a preferred orientation.
-/

namespace Hypertournaments

/-- On an increasing genuine packet, the actual raw orientation
of every facet equals E's canonical sign on its underlying
finite set. -/
theorem Hyper.orderedFacet_orient_eq_canonicalSign
    {n a : ℕ} (E : Hyper n (Fin a))
    (f : Fin (n+1) ↪o Fin a) (i : Fin (n+1)) :
    E.orient (facet f.toEmbedding i) =
      E.canonicalSignTable (tupleVertices (facet f.toEmbedding i)) := by
  calc
    E.orient (facet f.toEmbedding i) =
        (Hyper.fromOrderedSigns E.canonicalSignTable).orient
          (facet f.toEmbedding i) :=
      (E.from_canonicalSignTable_orient (facet f.toEmbedding i)).symm
    _ = E.canonicalSignTable (tupleVertices (facet f.toEmbedding i)) :=
      fromOrderedSigns_facet_increasing E.canonicalSignTable f i

/-- The raw packet at a deleted position reads the exact
intrinsic canonical sign on the parent finite set with that
actual vertex removed. -/
theorem Hyper.orderedFacet_orient_eq_canonical_erase
    {n a : ℕ} (E : Hyper n (Fin a))
    (f : Fin (n+1) ↪o Fin a) (i : Fin (n+1)) :
    E.orient (facet f.toEmbedding i) =
      E.canonicalSignTable
        ((tupleVertices f.toEmbedding).erase (f i)) := by
  calc
    E.orient (facet f.toEmbedding i) =
        E.canonicalSignTable (tupleVertices (facet f.toEmbedding i)) :=
      E.orderedFacet_orient_eq_canonicalSign f i
    _ = E.canonicalSignTable
          ((tupleVertices f.toEmbedding).erase (f i)) := by
      exact congrArg E.canonicalSignTable
        (tupleVertices_facet_eq_erase f.toEmbedding i)

end Hypertournaments
