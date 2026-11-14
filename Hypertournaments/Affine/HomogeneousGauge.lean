import Hypertournaments.Affine.ConstantShift
import Mathlib.Order.Fin.Basic

/-!
# The signed drift of a homogeneous lower gauge

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". Homogeneity is on increasing lower
tuples in the source carrier. The target need not be ordered. Actual
ordinary alternation then recovers every other enumeration.
-/

universe u v w

namespace Hypertournaments.Affine

/-- Homogeneous lower facets give their exact signed drift on each increasing upper tuple. -/
theorem signedCoboundary_homogeneous_on_increasing
    {n : ℕ} {D : Type v} {W : Type w} [LinearOrder D]
    {G : Type u} [AddCommGroup G] (s : AlternatingCochain n W G)
    (e : D ↪ W) (b : G)
    (hs : ∀ t : Fin n ↪o D, s.label (t.toEmbedding.trans e) = b)
    (f : Fin (n + 1) ↪o D) :
    signedCoboundary s.label (f.toEmbedding.trans e) =
      if Even (n + 1) then 0 else b := by
  apply signedCoboundary_eq_of_facets
  intro i
  exact hs ((Fin.succAboveOrderEmb i).trans f)

/-- The homogeneous drift is an equality of genuine ordinary alternating structures,
so every enumeration follows from the increasing-tuple calculation. -/
theorem homogeneous_coboundary_pullback
    {n : ℕ} {D : Type v} {W : Type w} [LinearOrder D]
    {G : Type u} [AddCommGroup G] (s : AlternatingCochain n W G)
    (e : D ↪ W) (b : G)
    (hs : ∀ t : Fin n ↪o D, s.label (t.toEmbedding.trans e) = b) :
    (s.pullback e).coboundary (by intro _; rfl) =
      (constantLinear (n + 1) (if Even (n + 1) then 0 else b) :
        AlternatingCochain (n + 1) D G) := by
  apply Labelled.ext
  apply Labelled.labels_equal_of_canonical
  intro S hS
  change signedCoboundary s.label ((S.orderEmbOfFin hS).toEmbedding.trans e) = _
  rw [signedCoboundary_homogeneous_on_increasing s e b hs,
    constantLinear_label_strictMono _ _ (S.orderEmbOfFin hS).strictMono]

/-- In even upper degree, a homogeneous lower gauge has zero drift on all tuples. -/
theorem signedCoboundary_homogeneous_of_even
    {n : ℕ} {D : Type v} {W : Type w} [LinearOrder D]
    {G : Type u} [AddCommGroup G] (s : AlternatingCochain n W G)
    (e : D ↪ W) (b : G)
    (hs : ∀ t : Fin n ↪o D, s.label (t.toEmbedding.trans e) = b)
    (hn : Even (n + 1)) (f : Fin (n + 1) ↪ D) :
    signedCoboundary s.label (f.trans e) = 0 := by
  have h := congrArg (fun A : AlternatingCochain (n + 1) D G => A.label f)
    (homogeneous_coboundary_pullback s e b hs)
  change signedCoboundary s.label (f.trans e) = _ at h
  simpa [hn, constantLinear, Labelled.fromOrderedLabels, Labelled.orderedLabel] using h

/-- A homogeneous signed gauge is absorbed by the corresponding constant
source-potential shift. This is intrinsic preservation on every tuple. -/
theorem preserves_after_homogeneous_gauge
    {n : ℕ} {D : Type v} {W : Type w} [LinearOrder D]
    {G : Type u} [AddCommGroup G] {a : G}
    (p : Labelled (n + 1) (Palette.affine a) D)
    (q : Labelled (n + 1) (Palette.affine a) W)
    (s : AlternatingCochain n W G) (e : D ↪ W) (b : G)
    (hs : ∀ t : Fin n ↪o D, s.label (t.toEmbedding.trans e) = b)
    (hgauge : ∀ t : Fin (n + 1) ↪ D,
      q.label (t.trans e) = p.label t + signedCoboundary s.label (t.trans e)) :
    (p.affineAddLinear (constantLinear (n + 1)
      (if Even (n + 1) then 0 else b))).Preserves q e := by
  apply Labelled.preserves_of_canonical
  intro S hS
  rw [hgauge, signedCoboundary_homogeneous_on_increasing s e b hs]
  rw [Labelled.affineAddLinear_label,
    constantLinear_label_strictMono _ _ (S.orderEmbOfFin hS).strictMono]

/-- The opposite gauge equation gives the negative source shift used when
comparing an existing model with a newly chosen target potential. -/
theorem preserves_after_homogeneous_gauge_sub
    {n : ℕ} {D : Type v} {W : Type w} [LinearOrder D]
    {G : Type u} [AddCommGroup G] {a : G}
    (p : Labelled (n + 1) (Palette.affine a) D)
    (q : Labelled (n + 1) (Palette.affine a) W)
    (s : AlternatingCochain n W G) (e : D ↪ W) (b : G)
    (hs : ∀ t : Fin n ↪o D, s.label (t.toEmbedding.trans e) = b)
    (hgauge : ∀ t : Fin (n + 1) ↪ D,
      p.label t = q.label (t.trans e) + signedCoboundary s.label (t.trans e)) :
    (p.affineAddLinear (constantLinear (n + 1)
      (-(if Even (n + 1) then 0 else b)))).Preserves q e := by
  apply Labelled.preserves_of_canonical
  intro S hS
  rw [Labelled.affineAddLinear_label,
    constantLinear_label_strictMono _ _ (S.orderEmbOfFin hS).strictMono]
  have h := hgauge (S.orderEmbOfFin hS).toEmbedding
  rw [signedCoboundary_homogeneous_on_increasing s e b hs] at h
  simpa only [sub_eq_add_neg] using (eq_sub_iff_add_eq).mpr h.symm

end Hypertournaments.Affine
