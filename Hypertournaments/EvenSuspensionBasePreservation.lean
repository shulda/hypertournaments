import Hypertournaments.EvenSuspensionBaseCompatibility
import Hypertournaments.CanonicalSignTableNaturality

/-!
# Even two-pad suspension respects genuine one-point spans

The even-suspension sign table is functorial under inclusion of a
common old base into a one-point extension. The proof first matches
the *actual* pad and old finite-set projections under castSucc, then
uses canonical source-sign naturality and the order-preserving
presentation bridge. The resulting statement is intrinsic: it
preserves all injective ordered (n+2)-tuples and is not merely an
auxiliary order or sign-table identity.

This supplies the common-base-preservation premise required by the
ordinary AP reflection. High-arity admissibility remains separate.
-/

namespace Hypertournaments

/-- The actual even-suspension sign table on the common base is
preserved when we add one last old vertex on the source side. -/
theorem evenSuspensionSignTable_image_base
    {n a m : ℕ}
    (A : Hyper n (Fin a)) (B : Hyper n (Fin (a + 1)))
    (hAB : Preserves A B (onePointBaseEmbedding a))
    (Q : Finset (Fin (m + a))) :
    evenSuspensionSignTable m (a + 1) B
      (Q.image (onePointBaseEmbedding (m + a))) =
    evenSuspensionSignTable m a A Q := by
  have hOldEmbedding :
      (Fin.castSuccOrderEmb : Fin a ↪o Fin (a + 1)).toEmbedding =
        onePointBaseEmbedding a := by
    ext u
    rfl
  have hsrc :
      Preserves A B
        (Fin.castSuccOrderEmb : Fin a ↪o Fin (a + 1)).toEmbedding := by
    rw [hOldEmbedding]
    exact hAB
  have hcan :
      B.canonicalSignTable
        ((evenOldProjection m a Q).image (onePointBaseEmbedding a)) =
        A.canonicalSignTable (evenOldProjection m a Q) := by
    calc
      B.canonicalSignTable
          ((evenOldProjection m a Q).image (onePointBaseEmbedding a)) =
        B.canonicalSignTable
          ((evenOldProjection m a Q).image
            (Fin.castSuccOrderEmb : Fin a ↪o Fin (a + 1))) := by
          congr 1
      _ = A.canonicalSignTable (evenOldProjection m a Q) :=
        Hyper.canonicalSignTable_image_orderEmbedding
          A B (Fin.castSuccOrderEmb : Fin a ↪o Fin (a + 1))
          hsrc (evenOldProjection m a Q)
  unfold evenSuspensionSignTable
  rw [evenPadProjection_image_base m a Q,
      evenOldProjection_image_base m a Q, hcan]

/-- Exact orientation preservation of a *genuine* even suspended
common base in a suspended one-point extension. All tuple orders,
not just increasing ones, are respected. -/
theorem Hyper.evenSuspension_preserves_base
    {n a m : ℕ}
    (A : Hyper n (Fin a)) (B : Hyper n (Fin (a + 1)))
    (hAB : Preserves A B (onePointBaseEmbedding a)) :
    Preserves (A.evenSuspension m a) (B.evenSuspension m (a + 1))
      (onePointBaseEmbedding (m + a)) := by
  have htable :
      ∀ Q : Finset (Fin (m + a)),
        evenSuspensionSignTable m (a + 1) B
          (Q.image
            (Fin.castSuccOrderEmb : Fin (m + a) ↪o Fin (m + a + 1))) =
        evenSuspensionSignTable m a A Q := by
    intro Q
    calc
      evenSuspensionSignTable m (a + 1) B
          (Q.image
            (Fin.castSuccOrderEmb : Fin (m + a) ↪o Fin (m + a + 1))) =
        evenSuspensionSignTable m (a + 1) B
          (Q.image (onePointBaseEmbedding (m + a))) := by
          congr 1
      _ = evenSuspensionSignTable m a A Q :=
        evenSuspensionSignTable_image_base A B hAB Q
  have hp :=
    fromOrderedSigns_preserves
      (Fin.castSuccOrderEmb : Fin (m + a) ↪o Fin (m + a + 1))
      (evenSuspensionSignTable m a A)
      (evenSuspensionSignTable m (a + 1) B)
      htable
  have hHighEmbedding :
      (Fin.castSuccOrderEmb : Fin (m + a) ↪o Fin (m + a + 1)).toEmbedding =
        onePointBaseEmbedding (m + a) := by
    ext u
    rfl
  change Preserves
    (Hyper.fromOrderedSigns (evenSuspensionSignTable m a A))
    (Hyper.fromOrderedSigns (evenSuspensionSignTable m (a + 1) B))
    (onePointBaseEmbedding (m + a))
  rw [← hHighEmbedding]
  exact hp

end Hypertournaments
