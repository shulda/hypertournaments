import Hypertournaments.Obstruction

/-!
# The identification branch of ordinary one-point amalgamation

If embeddings agree on the old base and identify the two new points,
they coincide on every vertex and hence force equal orientations.
-/

namespace Hypertournaments

theorem onePoint_embeddings_equal {a d : ℕ}
    (i j : Fin (a + 1) ↪ Fin d)
    (hbase : ∀ x : Fin a, i x.castSucc = j x.castSucc)
    (hlast : i (Fin.last a) = j (Fin.last a)) : i = j := by
  ext x
  rcases x.eq_castSucc_or_eq_last with ⟨y, rfl⟩ | rfl
  · exact congrArg Fin.val (hbase y)
  · exact congrArg Fin.val hlast

/-- If the new points are identified, the two sides agree on
every oriented n-tuple. -/
theorem onePoint_orientations_equal_of_identification
    {n a d : ℕ} (L R : Hyper n (Fin (a + 1)))
    (D : Hyper n (Fin d))
    (i j : Fin (a + 1) ↪ Fin d)
    (hbase : ∀ x : Fin a, i x.castSucc = j x.castSucc)
    (hlast : i (Fin.last a) = j (Fin.last a))
    (hL : Preserves L D i) (hR : Preserves R D j) :
    ∀ t : Fin n ↪ Fin (a + 1), L.orient t = R.orient t := by
  have hmaps : i = j := onePoint_embeddings_equal i j hbase hlast
  intro t
  calc
    L.orient t = D.orient (t.trans i) := (hL t).symm
    _ = D.orient (t.trans j) := by rw [hmaps]
    _ = R.orient t := hR t

/-- Different one-point extensions cannot identify their new
vertices in an ordinary amalgam. -/
theorem onePoint_points_distinct_of_orient_disagree
    {n a d : ℕ} (L R : Hyper n (Fin (a + 1)))
    (D : Hyper n (Fin d))
    (i j : Fin (a + 1) ↪ Fin d)
    (hbase : ∀ x : Fin a, i x.castSucc = j x.castSucc)
    (hL : Preserves L D i) (hR : Preserves R D j)
    (hdisagree : ∃ t : Fin n ↪ Fin (a + 1), L.orient t ≠ R.orient t) :
    i (Fin.last a) ≠ j (Fin.last a) := by
  intro hlast
  obtain ⟨t, ht⟩ := hdisagree
  exact ht (onePoint_orientations_equal_of_identification L R D i j
    hbase hlast hL hR t)

/-- To refute ordinary AP using a one-point diagram with
different sides, it suffices to rule out the distinct-new-vertex
case. The identification case is already impossible by alternation
and preservation of orientations. -/
theorem not_hasAP_of_onePoint_no_distinct
    {n a : ℕ} {S : Set ℕ}
    (A : Hyper n (Fin a))
    (L R : Hyper n (Fin (a + 1)))
    (hA : Admissible S A) (hL : Admissible S L)
    (hR : Admissible S R)
    (hAL : Preserves A L (onePointBaseEmbedding a))
    (hAR : Preserves A R (onePointBaseEmbedding a))
    (hdisagree : ∃ t : Fin n ↪ Fin (a + 1), L.orient t ≠ R.orient t)
    (hNoDistinct :
      ∀ (d : ℕ) (D : Hyper n (Fin d))
        (i j : Fin (a + 1) ↪ Fin d),
        Admissible S D →
        Preserves L D i → Preserves R D j →
        (∀ x : Fin a, i ((onePointBaseEmbedding a) x) =
          j ((onePointBaseEmbedding a) x)) →
        i (Fin.last a) ≠ j (Fin.last a) → False) :
    ¬ HasAP n S := by
  apply not_hasAP_of_no_onePoint_amalgam A L R hA hL hR hAL hAR
  intro ham
  rcases ham with ⟨d, D, i, j, hD, hi, hj, hbase⟩
  have hbase' : ∀ x : Fin a, i x.castSucc = j x.castSucc := by
    intro x
    exact hbase x
  have hne := onePoint_points_distinct_of_orient_disagree
    L R D i j hbase' hi hj hdisagree
  exact hNoDistinct d D i j hD hi hj hbase hne

end Hypertournaments
