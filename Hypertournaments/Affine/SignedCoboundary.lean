import Hypertournaments.LocalTypes
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Mathlib.Data.Fin.SuccPred
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega

/-!
# Signed simplex coboundaries on actual injective tuples

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
the further potential constructions. Coefficients lie in an arbitrary
additive commutative group; no characteristic or finiteness is assumed.
-/

universe u v w

namespace Hypertournaments.Affine

/-- The signed simplex coboundary of an arbitrary tuple function. -/
def signedCoboundary {n : ℕ} {V : Type u} {G : Type v} [AddCommGroup G]
    (φ : (Fin n ↪ V) → G) (f : Fin (n + 1) ↪ V) : G :=
  ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • φ (facet f i)

theorem signedCoboundary_eq_signed_sum {n : ℕ} {V : Type u} {G : Type v}
    [AddCommGroup G] (φ : (Fin n ↪ V) → G) (f : Fin (n + 1) ↪ V) :
    signedCoboundary φ f = ∑ i : Fin (n + 1), (-1 : ℤ) ^ i.val • φ (facet f i) := rfl

@[simp] theorem signedCoboundary_zero {n : ℕ} {V : Type u} {G : Type v}
    [AddCommGroup G] (f : Fin (n + 1) ↪ V) :
    signedCoboundary (fun _ : Fin n ↪ V => (0 : G)) f = 0 := by
  simp [signedCoboundary]

theorem signedCoboundary_add {n : ℕ} {V : Type u} {G : Type v}
    [AddCommGroup G] (φ ψ : (Fin n ↪ V) → G) (f : Fin (n + 1) ↪ V) :
    signedCoboundary (fun t => φ t + ψ t) f = signedCoboundary φ f + signedCoboundary ψ f := by
  simp only [signedCoboundary, smul_add, Finset.sum_add_distrib]

theorem signedCoboundary_neg {n : ℕ} {V : Type u} {G : Type v}
    [AddCommGroup G] (φ : (Fin n ↪ V) → G) (f : Fin (n + 1) ↪ V) :
    signedCoboundary (fun t => -φ t) f = -signedCoboundary φ f := by
  simp only [signedCoboundary, smul_neg, Finset.sum_neg_distrib]

theorem signedCoboundary_sub {n : ℕ} {V : Type u} {G : Type v}
    [AddCommGroup G] (φ ψ : (Fin n ↪ V) → G) (f : Fin (n + 1) ↪ V) :
    signedCoboundary (fun t => φ t - ψ t) f = signedCoboundary φ f - signedCoboundary ψ f := by
  simp only [signedCoboundary, smul_sub, Finset.sum_sub_distrib]

/-- Deletion commutes with every vertex injection. -/
theorem signedCoboundary_naturality {n : ℕ} {V : Type u} {W : Type w}
    {G : Type v} [AddCommGroup G] (φ : (Fin n ↪ W) → G) (e : V ↪ W)
    (f : Fin (n + 1) ↪ V) :
    signedCoboundary (fun t => φ (t.trans e)) f = signedCoboundary φ (f.trans e) := rfl

/-- Interchanging the order of two deletions reverses the integral coefficient. -/
theorem signed_deletion_coefficient {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) :
    (-1 : ℤ) ^ (i.succAbove j).val * (-1 : ℤ) ^ (j.predAbove i).val =
      -((-1 : ℤ) ^ i.val * (-1 : ℤ) ^ j.val) := by
  rw [← pow_add, ← pow_add]
  by_cases h : j.castSucc < i
  · rw [Fin.succAbove_of_castSucc_lt _ _ h, Fin.predAbove_of_castSucc_lt _ _ h]
    simp only [Fin.val_castSucc, Fin.val_pred]
    have hi : 0 < i.val := by
      have hh : j.val < i.val := h
      omega
    have he : i.val + j.val = (j.val + (i.val - 1)) + 1 := by omega
    rw [he, pow_succ]
    simp
  · rw [Fin.succAbove_of_le_castSucc _ _ (le_of_not_gt h),
      Fin.predAbove_of_le_castSucc _ _ (le_of_not_gt h)]
    simp only [Fin.val_succ, Fin.coe_castPred]
    have he : j.val + 1 + i.val = (i.val + j.val) + 1 := by omega
    rw [he, pow_succ]
    simp

/-- Intrinsic Δ²=0, including arity zero and empty carriers. -/
theorem signedCoboundary_signedCoboundary_zero {n : ℕ} {V : Type u} {G : Type v}
    [AddCommGroup G] (φ : (Fin n ↪ V) → G) (f : Fin (n + 2) ↪ V) :
    signedCoboundary (signedCoboundary φ) f = 0 := by
  let flip : Fin (n + 2) × Fin (n + 1) → Fin (n + 2) × Fin (n + 1) :=
    fun p => (p.1.succAbove p.2, p.2.predAbove p.1)
  let value : Fin (n + 2) × Fin (n + 1) → G :=
    fun p => ((-1 : ℤ) ^ p.1.val * (-1 : ℤ) ^ p.2.val) •
      φ (facet (facet f p.1) p.2)
  have hfacet (p : Fin (n + 2) × Fin (n + 1)) :
      facet (facet f (flip p).1) (flip p).2 = facet (facet f p.1) p.2 := by
    ext k
    exact congrArg f (Fin.succAbove_succAbove_succAbove_predAbove p.1 p.2 k)
  have hvalue (p : Fin (n + 2) × Fin (n + 1)) : value (flip p) = -value p := by
    dsimp only [value]
    rw [hfacet]
    change ((-1 : ℤ) ^ (p.1.succAbove p.2).val *
      (-1 : ℤ) ^ (p.2.predAbove p.1).val) • _ = _
    rw [signed_deletion_coefficient, neg_smul]
  unfold signedCoboundary
  simp only [Finset.smul_sum, smul_smul]
  change (∑ i : Fin (n + 2), ∑ j : Fin (n + 1), value (i, j)) = 0
  rw [← Fintype.sum_prod_type]
  apply Finset.sum_ninvolution flip
  · intro p
    rw [hvalue]
    exact add_neg_cancel _
  · intro p _ hp
    exact Fin.succAbove_ne p.1 p.2 (congrArg Prod.fst hp)
  · intro p
    exact Finset.mem_univ _
  · intro p
    apply Prod.ext
    · exact Fin.succAbove_succAbove_predAbove p.1 p.2
    · exact Fin.predAbove_predAbove_succAbove p.1 p.2

end Hypertournaments.Affine
