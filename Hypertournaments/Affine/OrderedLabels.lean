import Hypertournaments.Affine.Basic
import Hypertournaments.FinitePresentation
import Mathlib.Tactic.Ext

/-!
# Ordered presentations of arbitrary involution-labelled structures

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the final subsection, `Further potential constructions`.
Orders only present the labels; intrinsic preservation remains order-free.
-/

namespace Hypertournaments.Affine

universe u v w

/-- Read a subset table using the parity of the sorting permutation. -/
def Labelled.orderedLabel {n : ℕ} {Q : Type u} (P : Palette Q)
    {V : Type v} [LinearOrder V] (table : Finset V → Q) (t : Fin n ↪ V) : Q :=
  if (Tuple.sort (t : Fin n → V)).sign = 1 then table (tupleVertices t)
    else P.star (table (tupleVertices t))

/-- Every table of labels on unordered sets gives an intrinsic labelled structure. -/
def Labelled.fromOrderedLabels {n : ℕ} {Q : Type u} (P : Palette Q)
    {V : Type v} [LinearOrder V] (table : Finset V → Q) : Labelled n P V where
  label := Labelled.orderedLabel P table
  swap_label t i j hij := by
    change
      (if (Tuple.sort (fun x => t (Equiv.swap i j x))).sign = 1 then
        table (tupleVertices ((Equiv.swap i j).toEmbedding.trans t))
       else P.star (table (tupleVertices ((Equiv.swap i j).toEmbedding.trans t)))) =
      P.star (if (Tuple.sort (t : Fin n → V)).sign = 1 then table (tupleVertices t)
        else P.star (table (tupleVertices t)))
    rw [sort_swap_sign t i j hij, tupleVertices_swap]
    rcases Int.units_eq_one_or (Tuple.sort (t : Fin n → V)).sign with h | h <;>
      simp [h, Units.ext_iff]

/-- Increasing tuples read the table literally. -/
theorem fromOrderedLabels_label_strictMono {n : ℕ} {Q : Type u} (P : Palette Q)
    {V : Type v} [LinearOrder V] (table : Finset V → Q) (t : Fin n ↪ V)
    (ht : StrictMono (t : Fin n → V)) :
    (Labelled.fromOrderedLabels P table).label t = table (tupleVertices t) := by
  have hsort : Tuple.sort (t : Fin n → V) = Equiv.refl _ :=
    (Tuple.sort_eq_refl_iff_monotone).mpr ht.monotone
  simp [Labelled.fromOrderedLabels, Labelled.orderedLabel, hsort]

/-- Compatible table values suffice for preservation along an increasing injection. -/
theorem fromOrderedLabels_preserves {n : ℕ} {Q : Type u} (P : Palette Q)
    {V : Type v} {W : Type w} [LinearOrder V] [LinearOrder W]
    (e : V ↪o W) (s : Finset V → Q) (t : Finset W → Q)
    (h : ∀ S : Finset V, t (S.image e) = s S) :
    (Labelled.fromOrderedLabels (n := n) P s).Preserves
      (Labelled.fromOrderedLabels P t) e.toEmbedding := by
  intro f
  change Labelled.orderedLabel P t (f.trans e.toEmbedding) = Labelled.orderedLabel P s f
  unfold Labelled.orderedLabel
  rw [sort_map_orderEmbedding f e, tupleVertices_map_orderEmbedding f e, h (tupleVertices f)]

/-- Equality can be checked on the unique increasing tuple of each subset.
The carrier may be infinite and the palette may be empty. -/
theorem Labelled.labels_equal_of_canonical {n : ℕ} {Q : Type u} {P : Palette Q}
    {V : Type v} [LinearOrder V] (A B : Labelled n P V)
    (h : ∀ (S : Finset V) (hS : S.card = n),
      A.label (S.orderEmbOfFin hS).toEmbedding = B.label (S.orderEmbOfFin hS).toEmbedding) :
    ∀ f : Fin n ↪ V, A.label f = B.label f := by
  intro f
  let S := tupleVertices f
  have hS : S.card = n := by
    dsimp [S, tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  let g : Fin n ↪o V := S.orderEmbOfFin hS
  let τ := Tuple.sort (f : Fin n → V)
  have hmono : Monotone ((f : Fin n → V) ∘ τ) := Tuple.monotone_sort _
  have hinj : Function.Injective ((f : Fin n → V) ∘ τ) := f.injective.comp τ.injective
  have hsorted : (f : Fin n → V) ∘ τ = (g : Fin n → V) :=
    Finset.orderEmbOfFin_unique hS (fun i =>
      Finset.mem_image_of_mem _ (Finset.mem_univ _))
      (hmono.strictMono_of_injective hinj)
  have hreorder : τ.symm.toEmbedding.trans g.toEmbedding = f := by
    ext x
    change g (τ.symm x) = f x
    have hx := congrFun hsorted (τ.symm x)
    simpa only [Function.comp_apply, Equiv.apply_symm_apply] using hx.symm
  rw [← hreorder, A.label_perm, B.label_perm, h S hS]

/-- Canonical checks establish intrinsic preservation along any injection.
The target has no order hypothesis. -/
theorem Labelled.preserves_of_canonical {n : ℕ} {Q : Type u} {P : Palette Q}
    {V : Type v} {W : Type w} [LinearOrder V]
    (A : Labelled n P V) (B : Labelled n P W) (e : V ↪ W)
    (h : ∀ (S : Finset V) (hS : S.card = n),
      B.label ((S.orderEmbOfFin hS).toEmbedding.trans e) =
        A.label (S.orderEmbOfFin hS).toEmbedding) : A.Preserves B e :=
  (B.pullback e).labels_equal_of_canonical A h

/-- Only genuine n-subsets are read; the explicit fallback avoids a
nonemptiness assumption on the palette in the foundations. -/
def Labelled.canonicalTable {n : ℕ} {Q : Type u} {P : Palette Q}
    {V : Type v} [LinearOrder V] (A : Labelled n P V) (fallback : Q) (S : Finset V) : Q :=
  if hS : S.card = n then A.label (S.orderEmbOfFin hS).toEmbedding else fallback

theorem Labelled.canonicalTable_at {n : ℕ} {Q : Type u} {P : Palette Q}
    {V : Type v} [LinearOrder V] (A : Labelled n P V) (fallback : Q)
    (S : Finset V) (hS : S.card = n) :
    A.canonicalTable fallback S = A.label (S.orderEmbOfFin hS).toEmbedding := by
  simp only [Labelled.canonicalTable, dite_eq_left hS]

/-- Every arbitrary ordered tuple is recovered from the canonical table. -/
theorem Labelled.from_canonicalTable_label {n : ℕ} {Q : Type u} {P : Palette Q}
    {V : Type v} [LinearOrder V] (A : Labelled n P V) (fallback : Q) (f : Fin n ↪ V) :
    (Labelled.fromOrderedLabels P (A.canonicalTable fallback)).label f = A.label f := by
  apply Labelled.labels_equal_of_canonical _ A ?_ f
  intro S hS
  rw [fromOrderedLabels_label_strictMono P _ _ (S.orderEmbOfFin hS).strictMono]
  have hvertices : tupleVertices (S.orderEmbOfFin hS).toEmbedding = S :=
    Finset.image_orderEmbOfFin_univ S hS
  rw [hvertices, A.canonicalTable_at fallback S hS]

theorem Labelled.from_canonicalTable {n : ℕ} {Q : Type u} {P : Palette Q}
    {V : Type v} [LinearOrder V] (A : Labelled n P V) (fallback : Q) :
    Labelled.fromOrderedLabels P (A.canonicalTable fallback) = A :=
  Labelled.ext (A.from_canonicalTable_label fallback)

end Hypertournaments.Affine
