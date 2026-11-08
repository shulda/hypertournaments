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
  · exact hbase y
  · exact hlast

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

end Hypertournaments
