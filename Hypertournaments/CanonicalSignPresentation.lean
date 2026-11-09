import Hypertournaments.CanonicalOrientationRecovery

/-!
# Presenting arbitrary intrinsic hypertournaments by finite sign tables

Every intrinsic n-hypertournament on Fin k is exactly recovered by
recording its orientation on the increasing enumerations of the
n-element vertex subsets. The sign table's values on other subset
sizes are dummy values and do not enter any n-tuple orientation.

This gives the inverse presentation interface to
`Hyper.fromOrderedSigns`, uniformly in n. It is intended for the
even and odd two-coordinate suspension constructions, whose
orientation tables are most conveniently specified on unordered
(n+2)-sets with one chosen canonical order.

No extra order is added to the hypertournament language; the order
on Fin k is used only for the sign-table presentation.
-/

namespace Hypertournaments

/-- The canonical Boolean sign table of an intrinsic n-hypertournament
on Fin k; only its values on n-element sets are mathematically used. -/
def Hyper.canonicalSignTable
    {n k : ℕ} (A : Hyper n (Fin k))
    (Q : Finset (Fin k)) : Bool :=
  if hQ : Q.card = n then
    A.orient (Q.orderEmbOfFin hQ).toEmbedding
  else false

/-- The sign assigned to a genuine n-set is exactly the orientation
of its unique increasing enumeration. -/
theorem Hyper.canonicalSignTable_at
    {n k : ℕ} (A : Hyper n (Fin k))
    (Q : Finset (Fin k)) (hQ : Q.card = n) :
    A.canonicalSignTable Q =
      A.orient (Q.orderEmbOfFin hQ).toEmbedding := by
  simp [Hyper.canonicalSignTable, hQ]

/-- Canonical presentation recovers all ordered injective n-tuple
orientations of an arbitrary intrinsic n-hypertournament. -/
theorem Hyper.from_canonicalSignTable_orient
    {n k : ℕ} (A : Hyper n (Fin k)) :
    ∀ f : Fin n ↪ Fin k,
      (Hyper.fromOrderedSigns A.canonicalSignTable).orient f =
        A.orient f := by
  apply orientations_equal_of_canonical
    (Hyper.fromOrderedSigns A.canonicalSignTable) A
  intro Q hQ
  let g : Fin n ↪o Fin k := Q.orderEmbOfFin hQ
  have hmono : StrictMono (g : Fin n → Fin k) := g.strictMono
  have hvertices : tupleVertices g.toEmbedding = Q := by
    change (Finset.univ.image (Q.orderEmbOfFin hQ)) = Q
    exact Finset.image_orderEmbOfFin_univ Q hQ
  calc
    (Hyper.fromOrderedSigns A.canonicalSignTable).orient g.toEmbedding =
        A.canonicalSignTable (tupleVertices g.toEmbedding) :=
      fromOrderedSigns_orient_strictMono A.canonicalSignTable
        g.toEmbedding hmono
    _ = A.canonicalSignTable Q := by rw [hvertices]
    _ = A.orient g.toEmbedding := A.canonicalSignTable_at Q hQ

end Hypertournaments
