import Hypertournaments.CanonicalPacket
import Hypertournaments.OddToggleP1Homogeneous
import Mathlib.Data.Fin.Tuple.Embedding

/-!
# Lower-arity links covered by homogeneous packets

Source: `tex_hypertournaments` at `64a392aa2b0e497c297f1218be3f1a8761bae18d`,
`obs:strict-constrained-hierarchy`. The sign of a set is the parity of its
least omitted vertex. Every packet consisting of the first `r` vertices and
one later vertex then has all normalized facet values zero.
-/

namespace Hypertournaments.StrictConstraint

private def coverSigns {m : ℕ} (Q : Finset (Fin m)) : Bool :=
  if h : Qᶜ.Nonempty then decide ((Qᶜ.min' h).val % 2 = 1) else false

/-- The lower-arity link used in the one-point extension construction. -/
def homogeneousCoverLink (r m : ℕ) : Hyper r (Fin m) :=
  Hyper.fromOrderedSigns coverSigns

private def coverTuple {r m : ℕ} (hm : r + 1 ≤ m) (x : Fin m) (hx : r ≤ x.val) :
    Fin (r + 1) ↪ Fin m :=
  Fin.Embedding.snoc (Fin.castLEEmb (by omega : r ≤ m)) (by
    rintro ⟨i, hi⟩
    have he := congrArg Fin.val hi
    change i.val = x.val at he
    have := i.isLt
    omega)

private theorem coverTuple_old {r m : ℕ} (hm : r + 1 ≤ m) (x : Fin m)
    (hx : r ≤ x.val) (i : Fin r) :
    coverTuple hm x hx i.castSucc = Fin.castLEEmb (by omega : r ≤ m) i :=
  Fin.Embedding.snoc_castSucc

private theorem coverTuple_last {r m : ℕ} (hm : r + 1 ≤ m) (x : Fin m)
    (hx : r ≤ x.val) : coverTuple hm x hx (Fin.last r) = x :=
  Fin.Embedding.snoc_last

private theorem coverTuple_val {r m : ℕ} (hm : r + 1 ≤ m) (x : Fin m)
    (hx : r ≤ x.val) (i : Fin (r + 1)) :
    (coverTuple hm x hx i).val = if i.val < r then i.val else x.val := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [coverTuple_last]
  · rw [coverTuple_old]
    simp [j.isLt]

private theorem coverTuple_strictMono {r m : ℕ} (hm : r + 1 ≤ m) (x : Fin m)
    (hx : r ≤ x.val) : StrictMono (coverTuple hm x hx : Fin (r + 1) → Fin m) := by
  intro i j hij
  change (coverTuple hm x hx i).val < (coverTuple hm x hx j).val
  rw [coverTuple_val, coverTuple_val]
  by_cases hj : j.val < r
  · have hi : i.val < r := lt_trans hij hj
    simp only [hi, hj, ↓reduceIte]
    exact hij
  · have hi : i.val < r := by have := j.isLt; change i.val < j.val at hij; omega
    simp only [hi, hj, ↓reduceIte]
    omega

private theorem earlier_mem_coverFacet {r m : ℕ} (hm : r + 1 ≤ m) (x : Fin m)
    (hx : r ≤ x.val) (i : Fin (r + 1)) (z : Fin m) (hz : z.val < i.val) :
    z ∈ tupleVertices (facet (coverTuple hm x hx) i) := by
  rw [tupleVertices_facet_eq_erase]
  have hzr : z.val < r := by have := i.isLt; omega
  have hold : coverTuple hm x hx (⟨z.val, hzr⟩ : Fin r).castSucc = z := by
    rw [coverTuple_old]
    rfl
  apply Finset.mem_erase.mpr
  constructor
  · intro he
    have hi := (coverTuple hm x hx).injective (he.symm.trans hold.symm)
    have hv := congrArg Fin.val hi
    simp only [Fin.val_castSucc] at hv
    omega
  · exact Finset.mem_image.mpr ⟨(⟨z.val, hzr⟩ : Fin r).castSucc, Finset.mem_univ _, hold⟩

private theorem index_not_mem_coverFacet {r m : ℕ} (hm : r + 1 ≤ m) (x : Fin m)
    (hx : r ≤ x.val) (i : Fin (r + 1)) :
    (Fin.castLEEmb hm i) ∉ tupleVertices (facet (coverTuple hm x hx) i) := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · intro h
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp h
    have hf : facet (coverTuple hm x hx) (Fin.last r) j =
        Fin.castLEEmb (by omega : r ≤ m) j := by
      simp only [facet, Function.Embedding.trans_apply, Fin.succAboveEmb_apply,
        Fin.succAbove_last, coverTuple_old]
    rw [hf] at hj
    have hv := congrArg Fin.val hj
    change j.val = r at hv
    have := j.isLt
    omega
  · rw [tupleVertices_facet_eq_erase]
    have he : Fin.castLEEmb hm j.castSucc = coverTuple hm x hx j.castSucc := by
      rw [coverTuple_old]
      rfl
    rw [he]
    exact Finset.notMem_erase _ _

private theorem coverSigns_facet {r m : ℕ} (hm : r + 1 ≤ m) (x : Fin m)
    (hx : r ≤ x.val) (i : Fin (r + 1)) :
    coverSigns (tupleVertices (facet (coverTuple hm x hx) i)) =
      decide (i.val % 2 = 1) := by
  let Q := tupleVertices (facet (coverTuple hm x hx) i)
  have hi : Fin.castLEEmb hm i ∈ Qᶜ :=
    Finset.mem_compl.mpr (index_not_mem_coverFacet hm x hx i)
  have hne : Qᶜ.Nonempty := ⟨_, hi⟩
  have hmin : Qᶜ.min' hne = Fin.castLEEmb hm i := by
    apply le_antisymm
    · exact Finset.min'_le _ _ hi
    · apply Finset.le_min'
      intro z hz
      change i.val ≤ z.val
      by_contra hlt
      have hmem := earlier_mem_coverFacet hm x hx i z (by omega)
      exact Finset.mem_compl.mp hz hmem
  change (if h : Qᶜ.Nonempty then decide ((Qᶜ.min' h).val % 2 = 1) else false) = _
  rw [dite_eq_left hne, hmin]
  rfl

private theorem coverTuple_localIndex {r m : ℕ} (hm : r + 1 ≤ m) (x : Fin m)
    (hx : r ≤ x.val) :
    localIndex (homogeneousCoverLink r m) (coverTuple hm x hx) = 0 := by
  rw [localIndex_zero_iff_normalized_constant]
  refine ⟨false, ?_⟩
  intro i
  unfold normalizedFacet
  change ((Hyper.fromOrderedSigns coverSigns).orient (facet (coverTuple hm x hx) i) ^^
    decide (i.val % 2 = 1)) = false
  have hfacet : StrictMono (facet (coverTuple hm x hx) i : Fin r → Fin m) := by
    intro a b hab
    exact coverTuple_strictMono hm x hx (Fin.strictMono_succAbove i hab)
  rw [fromOrderedSigns_orient_strictMono coverSigns _ hfacet]
  rw [coverSigns_facet]
  simp

/-- Every vertex belongs to a homogeneous `(r+1)`-packet in the link. -/
theorem homogeneousCoverLink_cover {r m : ℕ} (hm : r + 1 ≤ m) (v : Fin m) :
    ∃ f : Fin (r + 1) ↪ Fin m,
      v ∈ tupleVertices f ∧ localIndex (homogeneousCoverLink r m) f = 0 := by
  by_cases hv : v.val < r
  · let x : Fin m := ⟨r, by omega⟩
    let f := coverTuple hm x (by rfl : r ≤ x.val)
    refine ⟨f, ?_, coverTuple_localIndex hm x (by rfl)⟩
    refine Finset.mem_image.mpr ⟨(⟨v.val, hv⟩ : Fin r).castSucc, Finset.mem_univ _, ?_⟩
    rw [coverTuple_old]
    rfl
  · let f := coverTuple hm v (by omega)
    exact ⟨f, Finset.mem_image.mpr ⟨Fin.last r, Finset.mem_univ _, coverTuple_last hm v _⟩,
      coverTuple_localIndex hm v _⟩

/-- Existential formulation of the covering-link construction. -/
theorem exists_homogeneous_cover_link {r m : ℕ} (hm : r + 1 ≤ m) :
    ∃ L : Hyper r (Fin m), ∀ v : Fin m,
      ∃ f : Fin (r + 1) ↪ Fin m, v ∈ tupleVertices f ∧ localIndex L f = 0 :=
  ⟨homogeneousCoverLink r m, homogeneousCoverLink_cover hm⟩

end Hypertournaments.StrictConstraint
