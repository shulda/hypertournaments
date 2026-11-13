import Mathlib.Tactic.Ext
import Hypertournaments.RootedOddSuspensionSigns
import Hypertournaments.EvenSuspensionBaseCompatibility
import Hypertournaments.CanonicalSignTableNaturality

/-!
# Rooted odd suspension preserves the common one-point base

If A embeds into a one-point extension B by adjoining the final
old vertex, a distinguished root r in A is carried to its canonical
image in B. The root potential signs of all old finite subsets are
then exactly preserved, including the dummy wrong-sized table
entries. Together with exact pad/old projection naturality this
shows that the rooted odd suspension preserves the actual
(n+2)-orientation of the padded common base.

No odd-arity local-type admissibility is assumed or claimed.
-/

namespace Hypertournaments

/-- The root potential is natural under canonical source base
inclusion, if the distinguished root is inherited. -/
theorem rootedOddPotentialSignTable_image_base
    {n a : ℕ} (A : Hyper n (Fin a))
    (B : Hyper n (Fin (a + 1)))
    (root : Fin a)
    (hAB : Preserves A B (onePointBaseEmbedding a))
    (F : Finset (Fin a)) :
    rootedOddPotentialSignTable B (onePointBaseEmbedding a root)
      (F.image (onePointBaseEmbedding a)) =
      rootedOddPotentialSignTable A root F := by
  classical
  let e : Fin a ↪ Fin (a + 1) := onePointBaseEmbedding a
  have hOldEmbedding :
      (Fin.castSuccOrderEmb : Fin a ↪o Fin (a + 1)).toEmbedding = e := by
    ext u
    rfl
  have hsrc :
      Preserves A B
        (Fin.castSuccOrderEmb : Fin a ↪o Fin (a + 1)).toEmbedding := by
    rw [hOldEmbedding]
    exact hAB
  have hcan (G : Finset (Fin a)) :
      B.canonicalSignTable (G.image e) = A.canonicalSignTable G := by
    calc
      B.canonicalSignTable (G.image e) =
        B.canonicalSignTable
          (G.image (Fin.castSuccOrderEmb : Fin a ↪o Fin (a + 1))) := by
            congr 1
      _ = A.canonicalSignTable G :=
        Hyper.canonicalSignTable_image_orderEmbedding A B
          (Fin.castSuccOrderEmb : Fin a ↪o Fin (a + 1))
          hsrc G
  have hroot : e root ∈ F.image e ↔ root ∈ F := by
    constructor
    · intro hx
      obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hx
      have hvr : v = root := e.injective heq
      simpa [hvr] using hv
    · intro hr
      exact Finset.mem_image.mpr ⟨root, hr, rfl⟩
  have hinsert :
      insert (e root) (F.image e) = (insert root F).image e := by
    rw [Finset.image_insert]
  change rootedOddPotentialSignTable B (e root) (F.image e) =
    rootedOddPotentialSignTable A root F
  unfold rootedOddPotentialSignTable
  by_cases hr : root ∈ F
  · have hr' : e root ∈ F.image e := hroot.mpr hr
    simp [hr, hr']
  · have hr' : e root ∉ F.image e := by
      intro he
      exact hr (hroot.mp he)
    simp only [if_neg hr', if_neg hr]
    rw [hinsert]
    exact hcan (insert root F)

/-- The actual root-aware odd sign table commutes with inclusion of
a padded common base into a padded one-point extension. -/
theorem rootedOddSuspensionSignTable_image_base
    {n a m : ℕ}
    (A : Hyper n (Fin a)) (B : Hyper n (Fin (a + 1)))
    (root : Fin a)
    (hAB : Preserves A B (onePointBaseEmbedding a))
    (Q : Finset (Fin (m + a))) :
    rootedOddSuspensionSignTable m (a + 1) B
        (onePointBaseEmbedding a root)
        (Q.image (onePointBaseEmbedding (m + a))) =
      rootedOddSuspensionSignTable m a A root Q := by
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
  have hpot :=
    rootedOddPotentialSignTable_image_base
      A B root hAB (evenOldProjection m a Q)
  unfold rootedOddSuspensionSignTable
  rw [evenPadProjection_image_base m a Q,
      evenOldProjection_image_base m a Q]
  by_cases htwo : (evenPadProjection m a Q).card = 2
  · simp [htwo, hcan]
  · by_cases hthree : (evenPadProjection m a Q).card = 3
    · simp [htwo, hthree, hpot]
    · simp [htwo, hthree]

/-- Intrinsic preservation of every high orientation on the common
padded base of a rooted one-point span. -/
theorem Hyper.rootedOddSuspension_preserves_base
    {n a m : ℕ}
    (A : Hyper n (Fin a)) (B : Hyper n (Fin (a + 1)))
    (root : Fin a)
    (hAB : Preserves A B (onePointBaseEmbedding a)) :
    Preserves (A.rootedOddSuspension m a root)
      (B.rootedOddSuspension m (a + 1) (onePointBaseEmbedding a root))
      (onePointBaseEmbedding (m + a)) := by
  have htable :
      ∀ Q : Finset (Fin (m + a)),
        rootedOddSuspensionSignTable m (a + 1) B
          (onePointBaseEmbedding a root)
          (Q.image
            (Fin.castSuccOrderEmb : Fin (m + a) ↪o Fin (m + a + 1))) =
        rootedOddSuspensionSignTable m a A root Q := by
    intro Q
    calc
      rootedOddSuspensionSignTable m (a + 1) B
          (onePointBaseEmbedding a root)
          (Q.image
            (Fin.castSuccOrderEmb : Fin (m + a) ↪o Fin (m + a + 1))) =
        rootedOddSuspensionSignTable m (a + 1) B
          (onePointBaseEmbedding a root)
          (Q.image (onePointBaseEmbedding (m + a))) := by
          congr 1
      _ = rootedOddSuspensionSignTable m a A root Q :=
        rootedOddSuspensionSignTable_image_base A B root hAB Q
  have hp :=
    fromOrderedSigns_preserves (n := n + 2)
      (Fin.castSuccOrderEmb : Fin (m + a) ↪o Fin (m + a + 1))
      (rootedOddSuspensionSignTable m a A root)
      (rootedOddSuspensionSignTable m (a + 1) B
        (onePointBaseEmbedding a root))
      htable
  have hHighEmbedding :
      (Fin.castSuccOrderEmb : Fin (m + a) ↪o Fin (m + a + 1)).toEmbedding =
        onePointBaseEmbedding (m + a) := by
    ext u
    rfl
  change Preserves
    (Hyper.fromOrderedSigns (rootedOddSuspensionSignTable m a A root))
    (Hyper.fromOrderedSigns
      (rootedOddSuspensionSignTable m (a + 1) B
        (onePointBaseEmbedding a root)))
    (onePointBaseEmbedding (m + a))
  rw [← hHighEmbedding]
  exact hp

end Hypertournaments
