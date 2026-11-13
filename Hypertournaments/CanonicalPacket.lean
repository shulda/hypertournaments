import Mathlib.Tactic.Ext
import Hypertournaments.FinitePresentation
import Hypertournaments.LocalTypes

/-!
# Canonical local-packet counting for increasing tuples

Avoid factorially many reorderings when checking an explicit sign
table. These are general mathematical lemmas and not assumptions
about the finite seed.
-/

namespace Hypertournaments

/-- Each facet of an increasing (n+1)-tuple is an increasing n-tuple. -/
theorem fromOrderedSigns_facet_increasing
    {n : ℕ} {V : Type*} [LinearOrder V]
    (signs : Finset V → Bool) (f : Fin (n + 1) ↪o V)
    (i : Fin (n + 1)) :
    (Hyper.fromOrderedSigns signs).orient (facet f.toEmbedding i) =
      signs (tupleVertices (facet f.toEmbedding i)) := by
  have hf : StrictMono (facet f.toEmbedding i : Fin n → V) := by
    exact f.strictMono.comp (Fin.strictMono_succAbove i)
  exact fromOrderedSigns_orient_strictMono signs _ hf

/-- A computable count of positive normalized facet signs for an
increasing (n+1)-tuple, using just table entries. -/
def increasingPacketPositiveCount
    {n : ℕ} {V : Type*} [LinearOrder V]
    (signs : Finset V → Bool) (f : Fin (n + 1) ↪o V) : ℕ :=
  (Finset.univ.filter (fun i : Fin (n + 1) =>
    Bool.xor (signs (tupleVertices (facet f.toEmbedding i)))
             (decide (i.val % 2 = 1)) = true)).card

theorem positiveFacetCount_ordered_sign
    {n : ℕ} {V : Type*} [LinearOrder V]
    (signs : Finset V → Bool) (f : Fin (n + 1) ↪o V) :
    positiveFacetCount (Hyper.fromOrderedSigns signs) f.toEmbedding =
      increasingPacketPositiveCount signs f := by
  have hfacet (i : Fin (n + 1)) :
      normalizedFacet (Hyper.fromOrderedSigns signs) f.toEmbedding i =
        Bool.xor (signs (tupleVertices (facet f.toEmbedding i)))
          (decide (i.val % 2 = 1)) := by
    unfold normalizedFacet
    rw [fromOrderedSigns_facet_increasing signs f i]
  unfold positiveFacetCount increasingPacketPositiveCount
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hfacet i]

/-- Local type index on an increasing tuple can be computed directly
from the sign table, with no sorting-permutation evaluation. -/
theorem localIndex_ordered_sign
    {n : ℕ} {V : Type*} [LinearOrder V]
    (signs : Finset V → Bool) (f : Fin (n + 1) ↪o V) :
    localIndex (Hyper.fromOrderedSigns signs) f.toEmbedding =
      min (increasingPacketPositiveCount signs f)
          (n + 1 - increasingPacketPositiveCount signs f) := by
  unfold localIndex
  rw [positiveFacetCount_ordered_sign signs f]

/-- A canonical five-set check directly against a four-ary sign
table, without rebuilding the full intrinsic orientation. -/
def canonicalSignCentral4At {k : ℕ}
    (signs : Finset (Fin k) → Bool) (Q : Finset (Fin k)) : Prop :=
  if h : Q.card = 5 then
    min (increasingPacketPositiveCount signs (Q.orderEmbOfFin h))
        (5 - increasingPacketPositiveCount signs (Q.orderEmbOfFin h)) = 2
  else True

/-- Deleting the i-th coordinate deletes exactly that vertex
from the underlying finite vertex set. -/
theorem tupleVertices_facet_eq_erase
    {n : ℕ} {V : Type*} [DecidableEq V]
    (f : Fin (n + 1) ↪ V) (i : Fin (n + 1)) :
    tupleVertices (facet f i) = (tupleVertices f).erase (f i) := by
  classical
  ext v
  simp only [tupleVertices, facet, Finset.mem_erase,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨?_, ⟨i.succAbove j, hj⟩⟩
    intro hv
    exact (Fin.succAbove_ne i j) (f.injective (hj.trans hv))
  · rintro ⟨hvi, j, hj⟩
    have hji : j ≠ i := by
      intro h
      subst j
      exact hvi hj.symm
    obtain ⟨k, hk⟩ := Fin.exists_succAbove_eq hji
    refine ⟨k, ?_⟩
    simpa [hk] using hj

/-- The index i of an increasing (n+1)-tuple is exactly the
number of its vertices below the i-th vertex. -/
theorem card_lt_tupleVertices_eq
    {n : ℕ} {V : Type*} [LinearOrder V]
    (f : Fin (n + 1) ↪o V) (i : Fin (n + 1)) :
    ((tupleVertices f.toEmbedding).filter (· < f i)).card = i.val := by
  classical
  have heq :
      (tupleVertices f.toEmbedding).filter (· < f i) =
        (Finset.univ.filter (fun j : Fin (n + 1) => j < i)).image f := by
    ext v
    simp only [tupleVertices, Finset.mem_filter,
      Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, (f.lt_iff_lt).mp hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, (f.lt_iff_lt).mpr hj⟩
  rw [heq, Finset.card_image_of_injective _ f.injective]
  change (Finset.univ.filter (fun j : Fin (n + 1) =>
    (j : ℕ) < (i : ℕ))).card = i.val
  rw [Fin.card_filter_val_lt]
  exact Nat.min_eq_right (Nat.le_of_lt i.isLt)

end Hypertournaments
