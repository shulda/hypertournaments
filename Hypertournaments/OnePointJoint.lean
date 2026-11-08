import Hypertournaments.Identification

/-!
# Joint numbering of a one-point amalgam

For an ordinary one-point amalgam with *distinct* new vertices,
the union of the two images has a canonical numbering
0,...,a-1 (base), a (left new vertex), a+1 (right new vertex).
This lemma constructs its injection into the ambient amalgam,
without assuming strong amalgamation or surjectivity.

Its purpose is to work on a fixed finite number of vertices when
applying explicit finite non-amalgamation certificates.
-/

namespace Hypertournaments

/-- The left inclusion of the original a+1 vertices into the
canonical union with two new vertices. -/
def leftJointInclusion (a : ℕ) : Fin (a + 1) ↪ Fin (a + 2) :=
  Fin.castSuccEmb

/-- The right inclusion fixes the old a vertices and sends the
right new vertex to the final position, skipping the left one. -/
def rightJointInclusion (a : ℕ) : Fin (a + 1) ↪ Fin (a + 2) :=
  Fin.succAboveEmb (Fin.castSucc (Fin.last a))

theorem rightJointInclusion_old (a : ℕ) (x : Fin a) :
    rightJointInclusion a x.castSucc = x.castSucc.castSucc := by
  change (Fin.last a).castSucc.succAbove x.castSucc = x.castSucc.castSucc
  exact Fin.succAbove_castSucc_of_lt _ _ x.castSucc_lt_last

theorem rightJointInclusion_new (a : ℕ) :
    rightJointInclusion a (Fin.last a) = Fin.last (a + 1) := by
  change (Fin.last a).castSucc.succAbove (Fin.last a) = Fin.last (a + 1)
  rw [Fin.succAbove_castSucc_self]
  rfl

/-- Two embeddings of one-point extensions which agree on the base
and have distinct new vertices factor through an injection of
the canonical (a+2)-vertex union. -/
theorem exists_joint_embedding
    (a d : ℕ) (i j : Fin (a + 1) ↪ Fin d)
    (hbase : ∀ x : Fin a, i x.castSucc = j x.castSucc)
    (hne : i (Fin.last a) ≠ j (Fin.last a)) :
    ∃ h : Fin (a + 2) ↪ Fin d,
      (leftJointInclusion a).trans h = i ∧
      (rightJointInclusion a).trans h = j := by
  have hnot : j (Fin.last a) ∉ Set.range i := by
    rintro ⟨x, hx⟩
    rcases x.eq_castSucc_or_eq_last with ⟨y, rfl⟩ | rfl
    · have hcontr : j y.castSucc = j (Fin.last a) := by
        calc
          j y.castSucc = i y.castSucc := (hbase y).symm
          _ = j (Fin.last a) := hx
      exact Fin.castSucc_ne_last y (j.injective hcontr)
    · exact hne hx
  let h : Fin (a + 2) ↪ Fin d := Fin.Embedding.snoc i hnot
  refine ⟨h, ?_, ?_⟩
  · ext x
    change (h x.castSucc).val = (i x).val
    exact congrArg Fin.val (Fin.Embedding.snoc_castSucc (x := i) (ha := hnot))
  · ext x
    rcases x.eq_castSucc_or_eq_last with ⟨y, rfl⟩ | rfl
    · change (h (rightJointInclusion a y.castSucc)).val = (j y.castSucc).val
      rw [rightJointInclusion_old]
      calc
        (h y.castSucc.castSucc).val = (i y.castSucc).val :=
          congrArg Fin.val (Fin.Embedding.snoc_castSucc (x := i) (ha := hnot))
        _ = (j y.castSucc).val := congrArg Fin.val (hbase y)
    · change (h (rightJointInclusion a (Fin.last a))).val =
          (j (Fin.last a)).val
      rw [rightJointInclusion_new]
      exact congrArg Fin.val (Fin.Embedding.snoc_last (x := i) (ha := hnot))

end Hypertournaments
