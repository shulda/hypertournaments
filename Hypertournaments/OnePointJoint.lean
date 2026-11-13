import Mathlib.Data.Fin.Tuple.Embedding
import Mathlib.Tactic.Ext
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

/-- Once different new points are assumed, ordinary AP can be
refuted on the canonical finite union with a+2 vertices. -/
theorem not_hasAP_of_no_joint
    {n a : ℕ} {S : Set ℕ}
    (A : Hyper n (Fin a))
    (L R : Hyper n (Fin (a + 1)))
    (hA : Admissible S A) (hL : Admissible S L)
    (hR : Admissible S R)
    (hAL : Preserves A L (onePointBaseEmbedding a))
    (hAR : Preserves A R (onePointBaseEmbedding a))
    (hdisagree : ∃ t : Fin n ↪ Fin (a + 1),
      L.orient t ≠ R.orient t)
    (hNoJoint :
      ∀ (E : Hyper n (Fin (a + 2))),
        Admissible S E →
        Preserves L E (leftJointInclusion a) →
        Preserves R E (rightJointInclusion a) → False) :
    ¬ HasAP n S := by
  apply not_hasAP_of_onePoint_no_distinct
    A L R hA hL hR hAL hAR hdisagree
  intro d D i j hD hi hj hbase hdistinct
  obtain ⟨h, hleft, hright⟩ :=
    exists_joint_embedding a d i j hbase hdistinct
  let E : Hyper n (Fin (a + 2)) := D.pullback h
  have hE : Admissible S E := admissible_pullback D h hD
  have hEL : Preserves L E (leftJointInclusion a) := by
    intro t
    change D.orient ((t.trans (leftJointInclusion a)).trans h) =
      L.orient t
    have ht :
        (t.trans (leftJointInclusion a)).trans h = t.trans i := by
      ext x
      exact congrArg Fin.val (DFunLike.congr_fun hleft (t x))
    rw [ht]
    exact hi t
  have hER : Preserves R E (rightJointInclusion a) := by
    intro t
    change D.orient ((t.trans (rightJointInclusion a)).trans h) =
      R.orient t
    have ht :
        (t.trans (rightJointInclusion a)).trans h = t.trans j := by
      ext x
      exact congrArg Fin.val (DFunLike.congr_fun hright (t x))
    rw [ht]
    exact hj t
  exact hNoJoint E hE hEL hER

end Hypertournaments
