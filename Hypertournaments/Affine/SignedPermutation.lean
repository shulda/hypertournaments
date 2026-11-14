import Hypertournaments.Affine.Basic
import Hypertournaments.Affine.SignedCoboundary
import Hypertournaments.GeneralAdjacentFacet
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Algebra.Module.NatInt
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ext
import Mathlib.Tactic.SplitIfs

/-!
# Signed affine coboundaries and coordinate permutations

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`Further potential constructions`. The alternating simplex coefficients
make the adjacent deleted facets cancel; the remaining affine offset is
the sum of the coefficients. There are no finiteness assumptions.
-/

namespace Hypertournaments.Affine

universe u v

/-- Ordinary alternating cochains are the affine palette with offset zero. -/
abbrev AlternatingCochain (n : ℕ) (V : Type v) (G : Type u) [AddCommGroup G] :=
  Labelled n (Palette.affine (0 : G)) V

private theorem affine_facet_swap_away {r : ℕ} {V : Type v} {G : Type u}
    [AddCommGroup G] {a : G} (A : Labelled r (Palette.affine a) V)
    (f : Fin (r + 1) ↪ V) (p : Fin r) (i : Fin (r + 1))
    (hil : i ≠ p.castSucc) (hir : i ≠ p.succ) :
    A.label (facet ((adjacentSwapCoord p).toEmbedding.trans f) i) =
      a - A.label (facet f i) := by
  have hlr : p.castSucc ≠ p.succ := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at h'
    exact Nat.ne_add_one _ h'
  obtain ⟨x, y, hxy, hcoord⟩ := exists_restricted_swap i p.castSucc p.succ hil hir hlr
  have hemb : facet ((adjacentSwapCoord p).toEmbedding.trans f) i =
      (Equiv.swap x y).toEmbedding.trans (facet f i) := by
    ext j
    exact congrArg f (hcoord j)
  rw [hemb, A.swap_label _ _ _ hxy, Palette.affine_star]

/-- Without a parity restriction, the new affine offset is the alternating
sum of the old offsets: zero in even upper arity and a in odd upper arity. -/
theorem signedCoboundary_adjacent {r : ℕ} {V : Type v} {G : Type u}
    [AddCommGroup G] {a : G} (A : Labelled r (Palette.affine a) V)
    (f : Fin (r + 1) ↪ V) (p : Fin r) :
    signedCoboundary A.label ((adjacentSwapCoord p).toEmbedding.trans f) =
      (if Even (r + 1) then 0 else a) - signedCoboundary A.label f := by
  classical
  let w : Fin (r + 1) → ℤ := fun i => (-1 : ℤ) ^ i.val
  let σ := adjacentSwapCoord p
  have hlr : p.castSucc ≠ p.succ := by
    intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castSucc, Fin.val_succ] at h'
    exact Nat.ne_add_one _ h'
  have hw : w p.succ = -w p.castSucc := by
    simp [w, pow_succ]
  have hterm (i : Fin (r + 1)) :
      w i • A.label (facet (σ.toEmbedding.trans f) i) =
        -(w (σ i) • A.label (facet f (σ i))) + w i • a -
          (if i = p.castSucc then w p.castSucc • a else 0) -
          (if i = p.succ then w p.succ • a else 0) := by
    by_cases hil : i = p.castSucc
    · subst i
      rw [show facet (σ.toEmbedding.trans f) p.castSucc = facet f p.succ from
        facet_adjacent_swap_left f p]
      simp [σ, adjacentSwapCoord, Equiv.swap_apply_left, hlr, hw]
    by_cases hir : i = p.succ
    · subst i
      rw [show facet (σ.toEmbedding.trans f) p.succ = facet f p.castSucc from
        facet_adjacent_swap_right f p]
      simp [σ, adjacentSwapCoord, Equiv.swap_apply_right, Ne.symm hlr, hw]
    have hfix : σ i = i := Equiv.swap_apply_of_ne_of_ne hil hir
    rw [hfix, affine_facet_swap_away A f p i hil hir]
    simp only [hil, hir, ite_false, sub_zero, smul_sub]
    abel
  have hsum := congrArg (fun h : Fin (r + 1) → G => ∑ i, h i) (funext hterm)
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hsum
  have hperm : (∑ i : Fin (r + 1), w (σ i) • A.label (facet f (σ i))) =
      ∑ i : Fin (r + 1), w i • A.label (facet f i) :=
    Fintype.sum_equiv σ _ _ (fun _ => rfl)
  rw [hperm] at hsum
  have hconst : (∑ i : Fin (r + 1), w i • a) = if Even (r + 1) then 0 else a := by
    rw [← Finset.sum_smul]
    simp only [w, Fin.sum_neg_one_pow]
    split_ifs <;> simp
  rw [hconst, hw, neg_zsmul] at hsum
  have hraw : (∑ i : Fin (r + 1), w i • A.label (facet f i)) =
      signedCoboundary A.label f := rfl
  rw [hraw] at hsum
  change signedCoboundary A.label (σ.toEmbedding.trans f) = _ at hsum
  change signedCoboundary A.label (σ.toEmbedding.trans f) = _
  rw [hsum]
  abel

/-- The source parity condition is precisely what retains the same affine offset. -/
theorem signedCoboundary_adjacent_same_offset {r : ℕ} {V : Type v} {G : Type u}
    [AddCommGroup G] {a : G} (A : Labelled r (Palette.affine a) V)
    (ha : Even (r + 1) → a = 0) (f : Fin (r + 1) ↪ V) (p : Fin r) :
    signedCoboundary A.label ((adjacentSwapCoord p).toEmbedding.trans f) =
      a - signedCoboundary A.label f := by
  rw [signedCoboundary_adjacent]
  by_cases h : Even (r + 1)
  · simp only [h, ite_true, ha h]
  · simp only [h, ite_false]

/-- Signed affine coboundaries satisfy the full permutation law in the
same affine palette exactly under the stated arity condition. -/
theorem signedCoboundary_label_perm {r : ℕ} {V : Type v} {G : Type u}
    [AddCommGroup G] {a : G} (A : Labelled r (Palette.affine a) V)
    (ha : Even (r + 1) → a = 0) (f : Fin (r + 1) ↪ V)
    (σ : Equiv.Perm (Fin (r + 1))) :
    signedCoboundary A.label (σ.toEmbedding.trans f) =
      if σ.sign = (1 : ℤˣ) then signedCoboundary A.label f
      else a - signedCoboundary A.label f := by
  let generators : Set (Equiv.Perm (Fin (r + 1))) :=
    Set.range (fun p : Fin r => adjacentSwapCoord p)
  have hgen : Submonoid.closure generators = ⊤ :=
    Equiv.Perm.mclosure_swap_castSucc_succ r
  have hall : ∀ τ : Equiv.Perm (Fin (r + 1)),
      τ ∈ Submonoid.closure generators → ∀ g : Fin (r + 1) ↪ V,
        signedCoboundary A.label (τ.toEmbedding.trans g) =
          if τ.sign = (1 : ℤˣ) then signedCoboundary A.label g
          else a - signedCoboundary A.label g := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
        obtain ⟨p, rfl⟩ := hx
        intro g
        have hlr : p.castSucc ≠ p.succ := by
          intro h
          have h' := congrArg Fin.val h
          simp only [Fin.val_castSucc, Fin.val_succ] at h'
          exact Nat.ne_add_one _ h'
        have hs : (adjacentSwapCoord p).sign ≠ (1 : ℤˣ) := by
          simp [adjacentSwapCoord, Equiv.Perm.sign_swap hlr, Units.ext_iff]
        rw [ite_eq_right hs]
        exact signedCoboundary_adjacent_same_offset A ha g p
    | one =>
        intro g
        have he : (1 : Equiv.Perm (Fin (r + 1))).toEmbedding.trans g = g := by
          ext i
          rfl
        simp [he]
    | mul x y hx hy ihx ihy =>
        intro g
        have he : (x * y).toEmbedding.trans g =
            y.toEmbedding.trans (x.toEmbedding.trans g) := by
          ext i
          rfl
        rw [he, ihy, ihx, Equiv.Perm.sign_mul]
        rcases Int.units_eq_one_or x.sign with hx | hx <;>
          rcases Int.units_eq_one_or y.sign with hy | hy <;>
          simp [hx, hy, Units.ext_iff]
  exact hall σ (by rw [hgen]; trivial) f

/-- The actual swap law for the affine coboundary. -/
theorem signedCoboundary_swap {r : ℕ} {V : Type v} {G : Type u}
    [AddCommGroup G] {a : G} (A : Labelled r (Palette.affine a) V)
    (ha : Even (r + 1) → a = 0) (f : Fin (r + 1) ↪ V)
    (i j : Fin (r + 1)) (hij : i ≠ j) :
    signedCoboundary A.label ((Equiv.swap i j).toEmbedding.trans f) =
      a - signedCoboundary A.label f := by
  have hs : (Equiv.swap i j).sign ≠ (1 : ℤˣ) := by
    rw [Equiv.Perm.sign_swap hij]
    decide
  simpa only [hs, ite_false] using signedCoboundary_label_perm A ha f (Equiv.swap i j)

/-- The signed coboundary is an actual affine-labelled structure. -/
def Labelled.coboundary {r : ℕ} {V : Type v} {G : Type u} [AddCommGroup G]
    {a : G} (A : Labelled r (Palette.affine a) V) (ha : Even (r + 1) → a = 0) :
    Labelled (r + 1) (Palette.affine a) V where
  label := signedCoboundary A.label
  swap_label f i j hij := signedCoboundary_swap A ha f i j hij

@[simp] theorem Labelled.coboundary_label {r : ℕ} {V : Type v} {G : Type u}
    [AddCommGroup G] {a : G} (A : Labelled r (Palette.affine a) V)
    (ha : Even (r + 1) → a = 0) (f : Fin (r + 1) ↪ V) :
    (A.coboundary ha).label f = signedCoboundary A.label f := rfl

theorem Labelled.coboundary_pullback {r : ℕ} {V : Type v} {W : Type*} {G : Type u}
    [AddCommGroup G] {a : G} (A : Labelled r (Palette.affine a) W)
    (ha : Even (r + 1) → a = 0) (e : V ↪ W) :
    (A.pullback e).coboundary ha = (A.coboundary ha).pullback e := by
  ext t
  rfl

theorem Labelled.Preserves.coboundary {r : ℕ} {V : Type v} {W : Type*} {G : Type u}
    [AddCommGroup G] {a : G} {A : Labelled r (Palette.affine a) V}
    {B : Labelled r (Palette.affine a) W} {e : V ↪ W} (he : A.Preserves B e)
    (ha : Even (r + 1) → a = 0) : (A.coboundary ha).Preserves (B.coboundary ha) e := by
  intro f
  change (∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val • B.label (facet (f.trans e) i)) = _
  apply Finset.sum_congr rfl
  intro i _
  exact congrArg (fun q => (-1 : ℤ) ^ i.val • q) (he (facet f i))

end Hypertournaments.Affine
