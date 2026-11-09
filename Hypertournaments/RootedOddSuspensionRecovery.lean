import Hypertournaments.RootedOddSuspensionSigns
import Hypertournaments.EvenSuspensionRecovery
import Hypertournaments.TwoPadOrdinaryAPTransfer

/-!
# Exact intrinsic source orientation recovery for rooted odd suspension

The rooted odd suspension differs from the unrooted even
construction only on facets containing three pads. On any
two-pad packet its sign table reads precisely the old n-sign.
The two-pad tuple is increasing on increasing source tuples,
and arbitrary old coordinate orders follow by the all-arity
canonical-orientation recovery lemma.

The final theorem discharges the exact CanonicalTwoPadSideRecovery
premise for BOTH sides of an ordinary canonical one-point span,
with an arbitrary common choice of root. No order is imposed on a
hypothetical amalgam.
-/

namespace Hypertournaments

theorem rootedOddSuspension_orient_increasing_twoPads
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (root : Fin k) (x y : Fin m) (hxy : x < y)
    (t : Fin n ↪o Fin k) :
    (A.rootedOddSuspension m k root).orient
      (evenPaddedTuple m k x y hxy t.toEmbedding) =
      A.orient t.toEmbedding := by
  let f : Fin (n + 2) ↪ Fin (m + k) :=
    evenPaddedTuple m k x y hxy t.toEmbedding
  have hmono : StrictMono (f : Fin (n + 2) → Fin (m + k)) :=
    evenPaddedTuple_strictMono m k x y hxy t
  have hsource :
      A.canonicalSignTable (tupleVertices t.toEmbedding) =
        A.orient t.toEmbedding := by
    calc
      A.canonicalSignTable (tupleVertices t.toEmbedding) =
          (Hyper.fromOrderedSigns A.canonicalSignTable).orient
            t.toEmbedding :=
        (fromOrderedSigns_orient_strictMono
          A.canonicalSignTable t.toEmbedding t.strictMono).symm
      _ = A.orient t.toEmbedding :=
        A.from_canonicalSignTable_orient t.toEmbedding
  calc
    (A.rootedOddSuspension m k root).orient f =
        rootedOddSuspensionSignTable m k A root (tupleVertices f) :=
      fromOrderedSigns_orient_strictMono
        (rootedOddSuspensionSignTable m k A root) f hmono
    _ = rootedOddSuspensionSignTable m k A root
          (evenPaddedPacket m k x y (tupleVertices t.toEmbedding)) := by
      rw [evenPaddedTuple_vertices]
    _ = A.canonicalSignTable (tupleVertices t.toEmbedding) :=
      rootedOddSuspensionSignTable_twoPads m k A root x y _
        (ne_of_lt hxy)
    _ = A.orient t.toEmbedding := hsource

theorem rootedOddSuspension_orient_twoPads
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (root : Fin k) (x y : Fin m) (hxy : x < y)
    (t : Fin n ↪ Fin k) :
    (A.rootedOddSuspension m k root).orient
      (evenPaddedTuple m k x y hxy t) = A.orient t := by
  have hc :
      ∀ (Q : Finset (Fin k)) (hQ : Q.card = n),
        (A.rootedOddSuspension m k root).orient
          (evenPaddedTuple m k x y hxy
            (Q.orderEmbOfFin hQ).toEmbedding) =
          A.orient (Q.orderEmbOfFin hQ).toEmbedding := by
    intro Q hQ
    exact rootedOddSuspension_orient_increasing_twoPads
      m k A root x y hxy (Q.orderEmbOfFin hQ)
  exact twoPad_source_recovery_of_canonical
    A (A.rootedOddSuspension m k root) (evenOldShift m k)
    (evenPadShift m k x) (evenPadShift m k y)
    (evenPadShift_not_mem_old m k x)
    (evenPadShift_not_mem_old m k y)
    (fun he => (ne_of_lt hxy) ((evenPadShift m k).injective he))
    hc t

theorem canonical_twoPad_recovery_rootedOddSuspension
    {n a m : ℕ}
    (L R : Hyper n (Fin (a + 1))) (root : Fin (a + 1)) :
    CanonicalTwoPadSideRecovery n a m L R
      (L.rootedOddSuspension m (a + 1) root)
      (R.rootedOddSuspension m (a + 1) root) := by
  constructor
  · intro x y hxy t
    change (L.rootedOddSuspension m (a + 1) root).orient
      (evenPaddedTuple m (a + 1) x y hxy t) = L.orient t
    exact rootedOddSuspension_orient_twoPads m (a + 1)
      L root x y hxy t
  · intro x y hxy t
    change (R.rootedOddSuspension m (a + 1) root).orient
      (evenPaddedTuple m (a + 1) x y hxy t) = R.orient t
    exact rootedOddSuspension_orient_twoPads m (a + 1)
      R root x y hxy t

end Hypertournaments
