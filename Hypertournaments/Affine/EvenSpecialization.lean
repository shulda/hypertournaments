import Hypertournaments.Affine.FiberCoding
import Hypertournaments.Affine.SignedPermutation
import Hypertournaments.Affine.Potential
import Hypertournaments.EvenPotential
import Mathlib.Data.ZMod.Basic

/-!
# The original even hypertournaments as an affine specialization

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
"Further potential constructions". The Boolean palette maps bijectively to
the affine palette `g ↦ 1-g` on `ZMod 2`. Signed and unsigned coboundaries
coincide there, so all original tuple equations are recovered literally.
No original proof is replaced by this regression bridge.
-/

universe u v

namespace Hypertournaments.Affine

/-- The original two orientation labels. -/
def boolPalette : Palette Bool where
  star := Bool.not
  involutive_star b := by cases b <;> rfl

@[simp] theorem boolPalette_star (b : Bool) : boolPalette.star b = !b := rfl

theorem bool_zmod_roundtrip (b : Bool) : p3ZMod2ToBool (p1BitToZMod b) = b := by
  cases b <;> decide

/-- The actual affine data of the original even construction. -/
def evenData : Data Bool (ZMod 2) where
  palette := boolPalette
  offset := 1
  effective := p1BitToZMod
  map_star q := by cases q <;> decide
  onto x := ⟨p3ZMod2ToBool x, p3BitToZMod_roundtrip x⟩

@[simp] theorem evenData_palette : evenData.palette = boolPalette := rfl
@[simp] theorem evenData_offset : evenData.offset = (1 : ZMod 2) := rfl
@[simp] theorem evenData_effective (b : Bool) : evenData.effective b = p1BitToZMod b := rfl

/-- Every integral sign acts trivially on the two-element group. -/
theorem neg_one_pow_zsmul_zmod_two (n : ℕ) (x : ZMod 2) :
    (-1 : ℤ) ^ n • x = x := by
  induction n with
  | zero => simp
  | succ n ih =>
      simp only [pow_succ, mul_neg_one, neg_zsmul, ih, ZMod.neg_eq_self_mod_two]

/-- The new signed operator is literally the original unsigned tuple operator. -/
theorem signedCoboundary_eq_tupleCoboundary {n : ℕ} {V : Type u}
    (φ : (Fin n ↪ V) → ZMod 2) (f : Fin (n + 1) ↪ V) :
    signedCoboundary φ f = tupleCoboundary φ f := by
  simp only [signedCoboundary, tupleCoboundary, neg_one_pow_zsmul_zmod_two]

end Hypertournaments.Affine

namespace Hypertournaments

/-- The original orientation function is an actual Boolean-labelled structure. -/
def Hyper.toAffine {n : ℕ} {V : Type u} (A : Hyper n V) :
    Affine.Labelled n Affine.boolPalette V where
  label := A.orient
  swap_label := A.swap_flip

@[simp] theorem Hyper.toAffine_label {n : ℕ} {V : Type u} (A : Hyper n V)
    (t : Fin n ↪ V) : A.toAffine.label t = A.orient t := rfl

/-- The effective potential is the old orientation bit interpreted in ZMod 2. -/
def Hyper.toGroupAffine {n : ℕ} {V : Type u} (A : Hyper n V) :
    Affine.Labelled n (Affine.Palette.affine (1 : ZMod 2)) V :=
  Affine.evenData.effectiveLabelled A.toAffine

@[simp] theorem Hyper.toGroupAffine_label {n : ℕ} {V : Type u} (A : Hyper n V)
    (t : Fin n ↪ V) : A.toGroupAffine.label t = p1BitToZMod (A.orient t) := rfl

end Hypertournaments

namespace Hypertournaments.Affine

/-- Boolean palette structures recover the original hypertournament directly. -/
def Labelled.boolToHyper {n : ℕ} {V : Type u} (A : Labelled n boolPalette V) : Hyper n V where
  orient := A.label
  swap_flip := A.swap_label

@[simp] theorem Labelled.boolToHyper_toAffine {n : ℕ} {V : Type u}
    (A : Labelled n boolPalette V) : A.boolToHyper.toAffine = A := by
  apply Labelled.ext
  intro t
  rfl

/-- Every group-labelled affine potential recovers an actual Boolean orientation. -/
def Labelled.zmodTwoToHyper {n : ℕ} {V : Type u}
    (p : Labelled n (Palette.affine (1 : ZMod 2)) V) : Hyper n V where
  orient t := p3ZMod2ToBool (p.label t)
  swap_flip t i j hij := by
    apply p1BitToZMod_injective
    rw [p3BitToZMod_roundtrip, p1BitToZMod_not, p3BitToZMod_roundtrip,
      p.swap_label t i j hij, Palette.affine_star]
    simp only [sub_eq_add_neg, ZMod.neg_eq_self_mod_two, add_comm]

@[simp] theorem Labelled.zmodTwoToHyper_orient {n : ℕ} {V : Type u}
    (p : Labelled n (Palette.affine (1 : ZMod 2)) V) (t : Fin n ↪ V) :
    p.zmodTwoToHyper.orient t = p3ZMod2ToBool (p.label t) := rfl

@[simp] theorem Labelled.zmodTwoToHyper_toGroupAffine {n : ℕ} {V : Type u}
    (p : Labelled n (Palette.affine (1 : ZMod 2)) V) : p.zmodTwoToHyper.toGroupAffine = p := by
  apply Labelled.ext
  intro t
  exact p3BitToZMod_roundtrip (p.label t)

/-- Closedness in the new data is exactly the original evenness predicate. -/
theorem evenData_closed_iff_isEven {n : ℕ} {V : Type u} (A : Hyper n V) :
    Closed evenData A.toAffine ↔ A.IsEven := by
  unfold Closed Hyper.IsEven
  simp only [Hyper.toAffine_label, evenData_effective, signedCoboundary_eq_tupleCoboundary]

/-- A specified original potential and its group encoding have the same tuple equation. -/
theorem evenData_isPotential_iff {r : ℕ} {V : Type u} (A : Hyper (r + 1) V) (p : Hyper r V) :
    IsPotential evenData A.toAffine p.toGroupAffine ↔ Hypertournaments.IsPotential A p := by
  change (∀ t : Fin (r + 1) ↪ V,
    signedCoboundary (fun s => p1BitToZMod (p.orient s)) t = p1BitToZMod (A.orient t)) ↔ _
  simp only [signedCoboundary_eq_tupleCoboundary]
  rfl

/-- This direction includes every new group-labelled potential, not just named original ones. -/
theorem evenData_isPotential_iff_zmodTwoToHyper {r : ℕ} {V : Type u}
    (A : Hyper (r + 1) V) (p : Labelled r (Palette.affine (1 : ZMod 2)) V) :
    IsPotential evenData A.toAffine p ↔ Hypertournaments.IsPotential A p.zmodTwoToHyper := by
  have h := evenData_isPotential_iff A p.zmodTwoToHyper
  simpa only [Labelled.zmodTwoToHyper_toGroupAffine] using h

/-- The original order-free embedding condition is unchanged. -/
theorem preserves_toAffine_iff {n : ℕ} {V : Type u} {W : Type v}
    (A : Hyper n V) (B : Hyper n W) (e : V ↪ W) :
    A.toAffine.Preserves B.toAffine e ↔ Hypertournaments.Preserves A B e := Iff.rfl

theorem preserves_toGroupAffine_iff {n : ℕ} {V : Type u} {W : Type v}
    (A : Hyper n V) (B : Hyper n W) (e : V ↪ W) :
    A.toGroupAffine.Preserves B.toGroupAffine e ↔ Hypertournaments.Preserves A B e := by
  constructor
  · intro h t
    exact p1BitToZMod_injective (h t)
  · intro h t
    exact congrArg p1BitToZMod (h t)

theorem preserves_boolToHyper_iff {n : ℕ} {V : Type u} {W : Type v}
    (A : Labelled n boolPalette V) (B : Labelled n boolPalette W) (e : V ↪ W) :
    Hypertournaments.Preserves A.boolToHyper B.boolToHyper e ↔ A.Preserves B e := by
  have h := preserves_toAffine_iff A.boolToHyper B.boolToHyper e
  simpa only [Labelled.boolToHyper_toAffine] using h.symm

theorem preserves_zmodTwoToHyper_iff {n : ℕ} {V : Type u} {W : Type v}
    (A : Labelled n (Palette.affine (1 : ZMod 2)) V)
    (B : Labelled n (Palette.affine (1 : ZMod 2)) W) (e : V ↪ W) :
    Hypertournaments.Preserves A.zmodTwoToHyper B.zmodTwoToHyper e ↔ A.Preserves B e := by
  have h := preserves_toGroupAffine_iff A.zmodTwoToHyper B.zmodTwoToHyper e
  simpa only [Labelled.zmodTwoToHyper_toGroupAffine] using h.symm

/-- Existence of a potential is unchanged, in both directions and on the original carrier. -/
theorem exists_evenData_potential_iff {r : ℕ} {V : Type u} (A : Hyper (r + 1) V) :
    (∃ p : Labelled r (Palette.affine (1 : ZMod 2)) V, IsPotential evenData A.toAffine p) ↔
      ∃ p : Hyper r V, Hypertournaments.IsPotential A p := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p.zmodTwoToHyper, (evenData_isPotential_iff_zmodTwoToHyper A p).mp hp⟩
  · rintro ⟨p, hp⟩
    exact ⟨p.toGroupAffine, (evenData_isPotential_iff A p).mpr hp⟩

/-- In the original even source arities the affine offset condition is automatic. -/
theorem evenData_parity_of_even {r : ℕ} (hr : Even r) :
    Even (r + 1) → evenData.offset = 0 := by
  intro h
  exact ((Nat.even_add_one.mp h) hr).elim

end Hypertournaments.Affine

namespace Hypertournaments

@[simp] theorem Hyper.toAffine_boolToHyper {n : ℕ} {V : Type u} (A : Hyper n V) :
    A.toAffine.boolToHyper = A := by
  apply Hyper.ext
  intro t
  rfl

@[simp] theorem Hyper.toGroupAffine_zmodTwoToHyper {n : ℕ} {V : Type u} (A : Hyper n V) :
    A.toGroupAffine.zmodTwoToHyper = A := by
  apply Hyper.ext
  intro t
  exact Affine.bool_zmod_roundtrip (A.orient t)

/-- There is no additional Boolean-labelled structure hidden in the specialization. -/
def Hyper.toAffineEquiv (n : ℕ) (V : Type u) :
    Hyper n V ≃ Affine.Labelled n Affine.boolPalette V where
  toFun := Hyper.toAffine
  invFun := Affine.Labelled.boolToHyper
  left_inv := Hyper.toAffine_boolToHyper
  right_inv := Affine.Labelled.boolToHyper_toAffine

/-- Every group-labelled affine potential is exactly an original hypertournament. -/
def Hyper.toGroupAffineEquiv (n : ℕ) (V : Type u) :
    Hyper n V ≃ Affine.Labelled n (Affine.Palette.affine (1 : ZMod 2)) V where
  toFun := Hyper.toGroupAffine
  invFun := Affine.Labelled.zmodTwoToHyper
  left_inv := Hyper.toGroupAffine_zmodTwoToHyper
  right_inv := Affine.Labelled.zmodTwoToHyper_toGroupAffine

/-- The new intrinsic coboundary recovers the original one on every tuple. -/
theorem Hyper.coboundary_toGroupAffine {r : ℕ} {V : Type u} (p : Hyper r V) (hr : Even r) :
    (p.coboundary hr).toGroupAffine =
      p.toGroupAffine.coboundary (Affine.evenData_parity_of_even hr) := by
  apply Affine.Labelled.ext
  intro t
  change p1BitToZMod ((p.coboundary hr).orient t) =
    Affine.signedCoboundary (fun s => p1BitToZMod (p.orient s)) t
  rw [p.coboundary_orient, Affine.signedCoboundary_eq_tupleCoboundary]

/-- The general affine existence theorem recovers the original finite
potential-existence statement, without invoking its original proof. -/
theorem Hyper.isEven_iff_exists_potential_via_affine {r : ℕ} {V : Type u} [Finite V]
    (hr : Even r) (A : Hyper (r + 1) V) :
    A.IsEven ↔ ∃ p : Hyper r V, Hypertournaments.IsPotential A p := by
  have h := Affine.closed_iff_exists_potential Affine.evenData
    (Affine.evenData_parity_of_even hr) A.toAffine
  exact (Affine.evenData_closed_iff_isEven A).symm.trans
    (h.trans (Affine.exists_evenData_potential_iff A))

end Hypertournaments

namespace Hypertournaments.Affine

/-- The inverse equivalence also intertwines the actual old and new coboundaries. -/
theorem Labelled.zmodTwoToHyper_coboundary {r : ℕ} {V : Type u}
    (p : Labelled r (Palette.affine (1 : ZMod 2)) V) (hr : Even r) :
    (p.coboundary (evenData_parity_of_even hr)).zmodTwoToHyper =
      p.zmodTwoToHyper.coboundary hr := by
  apply Hyper.ext
  intro t
  apply p1BitToZMod_injective
  have hfun : (fun s => p1BitToZMod (p.zmodTwoToHyper.orient s)) = p.label :=
    funext (fun s => p3BitToZMod_roundtrip (p.label s))
  change p1BitToZMod (p3ZMod2ToBool (signedCoboundary p.label t)) = _
  rw [p3BitToZMod_roundtrip, Hyper.coboundary_orient, hfun,
    signedCoboundary_eq_tupleCoboundary]

end Hypertournaments.Affine
