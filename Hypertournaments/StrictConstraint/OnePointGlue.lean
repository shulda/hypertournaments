import Hypertournaments.CanonicalSignPresentation
import Hypertournaments.OnePointLink
import Mathlib.Data.Finset.Preimage
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Prescribing one new vertex link

An arbitrary hypertournament and an arbitrary orientation of one lower arity
can be glued as the old part and the link at a new vertex. We first put the
new vertex first in an auxiliary order, then reindex it to the last vertex.
No auxiliary order occurs in either preservation equation.
-/

namespace Hypertournaments.StrictConstraint

private theorem zero_not_mem_succRange (m : ℕ) :
    (0 : Fin (m + 1)) ∉ Set.range (Fin.succEmb m) := by
  simp [Fin.succEmb]

theorem last_not_mem_castSuccRange (m : ℕ) :
    Fin.last m ∉ Set.range (Fin.castSuccEmb (n := m)) := by
  rintro ⟨x, hx⟩
  exact Fin.castSucc_ne_last x hx

private noncomputable def glueSigns {r m : ℕ} (A : Hyper (r + 1) (Fin m))
    (L : Hyper r (Fin m)) (Q : Finset (Fin (m + 1))) : Bool :=
  if 0 ∈ Q then
    L.canonicalSignTable (Q.preimage (Fin.succEmb m) (Fin.succEmb m).injective.injOn)
  else
    A.canonicalSignTable (Q.preimage (Fin.succEmb m) (Fin.succEmb m).injective.injOn)

private theorem glueSigns_old {r m : ℕ} (A : Hyper (r + 1) (Fin m))
    (L : Hyper r (Fin m)) (Q : Finset (Fin m)) :
    glueSigns A L (Q.image (Fin.succOrderEmb m)) = A.canonicalSignTable Q := by
  have hmap : Q.image (Fin.succOrderEmb m) = Q.map (Fin.succEmb m) := by
    ext x
    simp
  rw [hmap]
  have hzero : (0 : Fin (m + 1)) ∉ Q.map (Fin.succEmb m) := by
    simp [Fin.succEmb]
  simp only [glueSigns, hzero, ↓reduceIte]
  rw [Finset.preimage_map]

private theorem glue_old {r m : ℕ} (A : Hyper (r + 1) (Fin m))
    (L : Hyper r (Fin m)) :
    Preserves A (Hyper.fromOrderedSigns (glueSigns A L)) (Fin.succEmb m) := by
  have h := fromOrderedSigns_preserves (n := r + 1) (Fin.succOrderEmb m)
    A.canonicalSignTable (glueSigns A L) (glueSigns_old A L)
  intro t
  exact (h t).trans (A.from_canonicalSignTable_orient t)

private theorem rootTuple_strictMono {r m : ℕ} (t : Fin r ↪o Fin m) :
    StrictMono (onePointTuple (Fin.succEmb m) 0 (zero_not_mem_succRange m)
      t.toEmbedding) := by
  intro i
  refine Fin.cases ?_ (fun i => ?_) i
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact (lt_irrefl _ h).elim
    · intro _
      exact Fin.succ_pos _
  · intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · intro h
      exact (not_lt_of_ge (Fin.zero_le _) h).elim
    · intro h
      exact Fin.succ_lt_succ_iff.mpr (t.strictMono (Fin.succ_lt_succ_iff.mp h))

private theorem rootTuple_preimage {r m : ℕ} (t : Fin r ↪ Fin m) :
    (tupleVertices (onePointTuple (Fin.succEmb m) 0 (zero_not_mem_succRange m) t)).preimage
      (Fin.succEmb m) (Fin.succEmb m).injective.injOn = tupleVertices t := by
  ext x
  simp only [Finset.mem_preimage, tupleVertices, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi⟩
    revert hi
    refine Fin.cases ?_ (fun j => ?_) i
    · intro hi
      exact (Fin.succ_ne_zero x hi.symm).elim
    · intro hi
      exact ⟨j, Fin.succ_injective _ hi⟩
  · rintro ⟨i, hi⟩
    refine ⟨i.succ, ?_⟩
    simp [hi]

private theorem glue_root_canonical {r m : ℕ} (A : Hyper (r + 1) (Fin m))
    (L : Hyper r (Fin m)) (t : Fin r ↪o Fin m) :
    (Hyper.fromOrderedSigns (glueSigns A L)).orient
      (onePointTuple (Fin.succEmb m) 0 (zero_not_mem_succRange m) t.toEmbedding) =
      L.orient t.toEmbedding := by
  let f := onePointTuple (Fin.succEmb m) 0 (zero_not_mem_succRange m) t.toEmbedding
  rw [fromOrderedSigns_orient_strictMono _ _ (rootTuple_strictMono t)]
  have hz : (0 : Fin (m + 1)) ∈ tupleVertices f :=
    Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
  change (if 0 ∈ tupleVertices f then _ else _) = _
  rw [ite_eq_left hz, rootTuple_preimage]
  calc
    L.canonicalSignTable (tupleVertices t.toEmbedding) =
        (Hyper.fromOrderedSigns L.canonicalSignTable).orient t.toEmbedding :=
      (fromOrderedSigns_orient_strictMono _ _ t.strictMono).symm
    _ = L.orient t.toEmbedding := L.from_canonicalSignTable_orient _

private theorem glue_root {r m : ℕ} (A : Hyper (r + 1) (Fin m))
    (L : Hyper r (Fin m)) (t : Fin r ↪ Fin m) :
    (Hyper.fromOrderedSigns (glueSigns A L)).orient
      (onePointTuple (Fin.succEmb m) 0 (zero_not_mem_succRange m) t) =
      L.orient t := by
  exact orientations_equal_of_canonical
    ((Hyper.fromOrderedSigns (glueSigns A L)).onePointSlice
      (Fin.succEmb m) 0 (zero_not_mem_succRange m)) L
    (fun Q hQ => glue_root_canonical A L (Q.orderEmbOfFin hQ)) t

private def rootReindex (m : ℕ) : Equiv.Perm (Fin (m + 1)) :=
  (finSuccEquivLast (n := m)).trans (finSuccEquiv m).symm

private theorem rootReindex_last (m : ℕ) : rootReindex m (Fin.last m) = 0 := by
  simp [rootReindex]

private theorem rootReindex_old {m : ℕ} (x : Fin m) :
    rootReindex m x.castSucc = x.succ := by
  simp [rootReindex]

/-- An arbitrary old orientation and arbitrary prescribed root link extend
simultaneously to a genuine one-point hypertournament extension. -/
theorem exists_onePoint_glue {r m : ℕ} (A : Hyper (r + 1) (Fin m))
    (L : Hyper r (Fin m)) :
    ∃ E : Hyper (r + 1) (Fin (m + 1)),
      Preserves A E (Fin.castSuccEmb (n := m)) ∧
      ∀ t : Fin r ↪ Fin m,
        E.orient (onePointTuple (Fin.castSuccEmb (n := m)) (Fin.last m)
          (last_not_mem_castSuccRange m) t) = L.orient t := by
  let E₀ : Hyper (r + 1) (Fin (m + 1)) := Hyper.fromOrderedSigns (glueSigns A L)
  refine ⟨E₀.pullback (rootReindex m).toEmbedding, ?_, ?_⟩
  · intro t
    change E₀.orient ((t.trans (Fin.castSuccEmb (n := m))).trans (rootReindex m).toEmbedding) = _
    have ht : (t.trans (Fin.castSuccEmb (n := m))).trans (rootReindex m).toEmbedding =
        t.trans (Fin.succEmb m) := by
      apply Function.Embedding.ext
      intro i
      exact rootReindex_old (t i)
    rw [ht]
    exact glue_old A L t
  · intro t
    change E₀.orient ((onePointTuple (Fin.castSuccEmb (n := m)) (Fin.last m)
      (last_not_mem_castSuccRange m) t).trans (rootReindex m).toEmbedding) = _
    have ht : (onePointTuple (Fin.castSuccEmb (n := m)) (Fin.last m)
        (last_not_mem_castSuccRange m) t).trans (rootReindex m).toEmbedding =
          onePointTuple (Fin.succEmb m) 0 (zero_not_mem_succRange m) t := by
      apply Function.Embedding.ext
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact rootReindex_last m
      · exact rootReindex_old (t j)
    rw [ht]
    exact glue_root A L t

end Hypertournaments.StrictConstraint
