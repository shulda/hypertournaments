import Hypertournaments.Affine.OrderedLabels
import Hypertournaments.Affine.SignedPermutation
import Hypertournaments.Affine.LinearOperations
import Hypertournaments.Affine.Data
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.SplitIfs

/-!
# Constant ordered cochains and harmless potential shifts

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". Constants refer to increasing tuples;
the other tuple values are recovered by ordinary alternation. The signed
coboundary of a constant is controlled by the actual arity parity.
-/

universe u v w

namespace Hypertournaments.Affine

/-- Equal facet values give the alternating sum of a single group element. -/
theorem signedCoboundary_eq_of_facets {n : ℕ} {V : Type v} {G : Type u}
    [AddCommGroup G] (φ : (Fin n ↪ V) → G) (f : Fin (n + 1) ↪ V) (b : G)
    (hb : ∀ i : Fin (n + 1), φ (facet f i) = b) :
    signedCoboundary φ f = if Even (n + 1) then 0 else b := by
  classical
  unfold signedCoboundary
  simp only [hb]
  rw [← Finset.sum_smul, Fin.sum_neg_one_pow]
  split_ifs <;> simp

/-- The ordinary alternating cochain taking value b on every increasing tuple. -/
def constantLinear (r : ℕ) {G : Type u} [AddCommGroup G] (b : G)
    {V : Type v} [LinearOrder V] : AlternatingCochain r V G :=
  Labelled.fromOrderedLabels (Palette.affine (0 : G)) (fun _ => b)

theorem constantLinear_label_strictMono {r : ℕ} {V : Type v} [LinearOrder V]
    {G : Type u} [AddCommGroup G] (b : G) (t : Fin r ↪ V)
    (ht : StrictMono (t : Fin r → V)) :
    (constantLinear r b : AlternatingCochain r V G).label t = b :=
  fromOrderedLabels_label_strictMono _ _ t ht

theorem signedCoboundary_constantLinear_increasing {r : ℕ} {V : Type v}
    [LinearOrder V] {G : Type u} [AddCommGroup G] (b : G) (f : Fin (r + 1) ↪o V) :
    signedCoboundary (constantLinear r b : AlternatingCochain r V G).label f.toEmbedding =
      if Even (r + 1) then 0 else b := by
  apply signedCoboundary_eq_of_facets
  intro i
  exact constantLinear_label_strictMono b _
    (f.strictMono.comp (Fin.strictMono_succAbove i))

/-- The constant-coboundary formula holds as equality of actual alternating structures. -/
theorem constantLinear_coboundary {r : ℕ} {V : Type v} [LinearOrder V]
    {G : Type u} [AddCommGroup G] (b : G) :
    (constantLinear r b : AlternatingCochain r V G).coboundary (by intro _; rfl) =
      constantLinear (r + 1) (if Even (r + 1) then 0 else b) := by
  apply Labelled.ext
  apply Labelled.labels_equal_of_canonical
  intro S hS
  rw [Labelled.coboundary_label,
    signedCoboundary_constantLinear_increasing b (S.orderEmbOfFin hS),
    constantLinear_label_strictMono _ _ (S.orderEmbOfFin hS).strictMono]

/-- In odd lower arity, the constant cochain is closed on every tuple. -/
theorem signedCoboundary_constantLinear_of_odd {r : ℕ} {V : Type v} [LinearOrder V]
    {G : Type u} [AddCommGroup G] (hr : Odd r) (b : G) (f : Fin (r + 1) ↪ V) :
    signedCoboundary (constantLinear r b : AlternatingCochain r V G).label f = 0 := by
  have heven : Even (r + 1) := by
    simpa only [Nat.even_add_one] using (Nat.not_even_iff_odd.mpr hr)
  have h := congrArg (fun A : AlternatingCochain (r + 1) V G => A.label f)
    (constantLinear_coboundary (V := V) (r := r) b)
  simpa [heven, constantLinear, Labelled.fromOrderedLabels, Labelled.orderedLabel] using h

/-- Shifting by an odd-degree constant changes no effective upper tuple value. -/
theorem signedCoboundary_affineAdd_constantLinear_of_odd
    {r : ℕ} {V : Type v} [LinearOrder V] {G : Type u} [AddCommGroup G]
    {a : G} (p : Labelled r (Palette.affine a) V) (hr : Odd r) (b : G)
    (f : Fin (r + 1) ↪ V) :
    signedCoboundary (p.affineAddLinear (constantLinear r b)).label f =
      signedCoboundary p.label f := by
  change signedCoboundary (fun t => p.label t + (constantLinear r b).label t) f = _
  rw [signedCoboundary_add, signedCoboundary_constantLinear_of_odd hr b, add_zero]

/-- A closed ordinary shift preserves the original raw potential equation. -/
theorem IsPotential.affineAddLinear_of_closed {r : ℕ} {Q : Type w} {G : Type u}
    [AddCommGroup G] {d : Data Q G} {V : Type v}
    {raw : Labelled (r + 1) d.palette V} {p : Labelled r (Palette.affine d.offset) V}
    (hp : IsPotential d raw p) (s : AlternatingCochain r V G)
    (hs : ∀ f : Fin (r + 1) ↪ V, signedCoboundary s.label f = 0) :
    IsPotential d raw (p.affineAddLinear s) := by
  intro f
  change signedCoboundary (fun t => p.label t + s.label t) f = _
  rw [signedCoboundary_add, hp f, hs f, add_zero]

/-- Any constant shift of odd degree preserves the same raw structure and effective labels. -/
theorem IsPotential.affineAdd_constantLinear_of_odd
    {r : ℕ} {Q : Type w} {G : Type u} [AddCommGroup G] {d : Data Q G}
    {V : Type v} [LinearOrder V] {raw : Labelled (r + 1) d.palette V}
    {p : Labelled r (Palette.affine d.offset) V} (hp : IsPotential d raw p)
    (hr : Odd r) (b : G) : IsPotential d raw (p.affineAddLinear (constantLinear r b)) :=
  hp.affineAddLinear_of_closed (constantLinear r b) (signedCoboundary_constantLinear_of_odd hr b)

end Hypertournaments.Affine
