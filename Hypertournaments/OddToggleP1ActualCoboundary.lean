import Hypertournaments.OddToggleP1RawCountParity
import Hypertournaments.CanonicalSignPresentation
import Hypertournaments.CanonicalPacket
import Hypertournaments.Cochain

/-!
# The actual homogeneous indicator is an unordered simplex coboundary

In arity n=4k+5, a packet in the exceptional toggle-zero switching
class is homogeneous (local index zero) iff the parity of its actual
raw facet orientations is odd. Here we identify that raw-facet sum
exactly with the unsigned simplicial coboundary of the source
canonical sign table on its underlying unordered (n+1)-set.

The order is used to enumerate the finite set, but the resulting
coboundary statement is about intrinsic hypertournament orientations.
This is the missing indicator-equals-coboundary bridge required by
the p1 zero-or-two principle; remaining proof is to align the
phase comparison on all doubly erased (n+2)-tuples.
-/

namespace Hypertournaments

/-- On an actual increasing tuple of arbitrary arity, the unsigned
coboundary of its canonical source sign table is the F₂ sum of its
actual unnormalized facet orientations. -/
theorem Hyper.p1CanonicalRawFacetSum
    {n a : ℕ} (A : Hyper n (Fin a))
    (f : Fin (n+1) ↪o Fin a) :
    coboundary (fun Q => p1BitToZMod (A.canonicalSignTable Q))
      (tupleVertices f.toEmbedding) =
      ((boolPacketPositiveCount
        (fun i : Fin (n+1) =>
          A.orient (facet f.toEmbedding i)) : ℕ) : ZMod 2) := by
  have hsign (i : Fin (n+1)) :
      A.canonicalSignTable
          ((tupleVertices f.toEmbedding).erase (f i)) =
        A.orient (facet f.toEmbedding i) := by
    have hv :
        (tupleVertices f.toEmbedding).erase (f i) =
          tupleVertices (facet f.toEmbedding i) := by
      simpa using (tupleVertices_facet_eq_erase f.toEmbedding i).symm
    rw [hv]
    calc
      A.canonicalSignTable (tupleVertices (facet f.toEmbedding i)) =
          (Hyper.fromOrderedSigns A.canonicalSignTable).orient
            (facet f.toEmbedding i) :=
        (fromOrderedSigns_facet_increasing A.canonicalSignTable f i).symm
      _ = A.orient (facet f.toEmbedding i) :=
        A.from_canonicalSignTable_orient (facet f.toEmbedding i)
  unfold coboundary
  change (∑ v ∈ (Finset.univ.image f.toEmbedding),
      p1BitToZMod
        (A.canonicalSignTable
          ((tupleVertices f.toEmbedding).erase v))) =
    ((boolPacketPositiveCount
      (fun i : Fin (n+1) => A.orient (facet f.toEmbedding i)) : ℕ) :
      ZMod 2)
  have hinj : Set.InjOn
      (f.toEmbedding : Fin (n+1) → Fin a)
      (↑(Finset.univ : Finset (Fin (n+1)))) := by
    intro i _ j _ heq
    exact f.injective heq
  have hsum :
      (∑ v ∈ (Finset.univ.image f.toEmbedding),
        p1BitToZMod
          (A.canonicalSignTable
            ((tupleVertices f.toEmbedding).erase v))) =
      ∑ i : Fin (n+1),
        p1BitToZMod
          (A.canonicalSignTable
            ((tupleVertices f.toEmbedding).erase (f i))) := by
    simpa using
      (Finset.sum_image
        (s := (Finset.univ : Finset (Fin (n+1))))
        (g := (f.toEmbedding : Fin (n+1) → Fin a))
        (f := fun v : Fin a =>
          p1BitToZMod
            (A.canonicalSignTable
              ((tupleVertices f.toEmbedding).erase v)))
        hinj)
  rw [hsum, p1BoolPacketPositiveCount_toZMod]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsign i]

/-- Complete pointwise indicator/coboundary identity for the
exceptional n≡1 (mod4) family, on every actual increasing packet.
No unspecified parity or geometric premise remains at this level. -/
theorem Hyper.p1Toggle_typeZero_indicator_eq_coboundary
    (k a : ℕ) (A : Hyper (4*k+5) (Fin a))
    (f : Fin (4*k+6) ↪o Fin a)
    (hallowed :
      localIndex A f.toEmbedding ∈
        toggleZero (switchingAllowed (4*k+5))) :
    p1BitToZMod (decide (localIndex A f.toEmbedding = 0)) =
      coboundary (fun Q => p1BitToZMod (A.canonicalSignTable Q))
        (tupleVertices f.toEmbedding) := by
  calc
    p1BitToZMod (decide (localIndex A f.toEmbedding = 0)) =
        ((boolPacketPositiveCount
          (fun i : Fin (4*k+6) =>
            A.orient (facet f.toEmbedding i)) : ℕ) : ZMod 2) :=
      A.p1Toggle_typeZero_iff_rawFacetParityOne k f.toEmbedding hallowed
    _ = coboundary
          (fun Q => p1BitToZMod (A.canonicalSignTable Q))
          (tupleVertices f.toEmbedding) :=
      (A.p1CanonicalRawFacetSum f).symm

end Hypertournaments
