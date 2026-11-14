import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.SetTheory.Cardinal.Finite
import Lean.Elab.Tactic.Omega

/-!
# Fixed representatives in odd invariant cosets

An involution of a finite odd set has a fixed point. Applying this to an
invariant left coset gives a fixed representative. The subgroup need not be
normal, and the ambient group need not be finite.
-/

namespace Hypertournaments.GroupTheory

/-- An involution of a finite odd set fixes a point. -/
theorem finite_odd_involution_fixed
    {X : Type*} [Finite X] (f : X → X) (hf : Function.Involutive f)
    (hodd : Odd (Nat.card X)) : ∃ x : X, f x = x := by
  classical
  let : Fintype X := Fintype.ofFinite X
  let σ : Equiv.Perm X := hf.toPerm f
  have hnd : ¬ 2 ∣ Fintype.card X := by
    rintro ⟨m, hm⟩
    obtain ⟨k, hk⟩ := hodd
    have hcard : Nat.card X = Fintype.card X := Nat.card_eq_fintype_card
    omega
  have hσ : σ ^ (2 ^ 1) = 1 := by
    ext x
    change f (f x) = x
    exact hf x
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 2) (n := 1) hnd hσ
  exact ⟨x, hx⟩

private abbrev LeftCosetCarrier {K : Type*} [Group K] (J : Subgroup K) (k : K) :=
  {x : K // k⁻¹ * x ∈ J}

private def leftCosetEquiv {K : Type*} [Group K] (J : Subgroup K) (k : K) :
    J ≃ LeftCosetCarrier J k where
  toFun j := ⟨k * j, by simpa only [inv_mul_cancel_left] using j.property⟩
  invFun x := ⟨k⁻¹ * x, x.property⟩
  left_inv j := Subtype.ext (by simp only [inv_mul_cancel_left])
  right_inv x := Subtype.ext (by simp only [mul_inv_cancel_left])

/-- An invariant coset of an odd subgroup has a representative fixed by the
involutive automorphism. Only forward stability of the subgroup is needed. -/
theorem odd_invariant_coset_fixed_representative
    {K : Type*} [Group K] (J : Subgroup K) [Finite J]
    (hodd : Odd (Nat.card J)) (α : MulAut K) (hα : Function.Involutive α)
    (hJ : ∀ j ∈ J, α j ∈ J) (k : K) (hcoset : k⁻¹ * α k ∈ J) :
    ∃ x : K, k⁻¹ * x ∈ J ∧ α x = x := by
  let : Finite (LeftCosetCarrier J k) := Finite.of_equiv J (leftCosetEquiv J k)
  have hoddCoset : Odd (Nat.card (LeftCosetCarrier J k)) :=
    Nat.card_congr (leftCosetEquiv J k) ▸ hodd
  have hstable (x : LeftCosetCarrier J k) : k⁻¹ * α x ∈ J := by
    have hmul := J.mul_mem hcoset (hJ (k⁻¹ * x) x.property)
    have heq : (k⁻¹ * α k) * α (k⁻¹ * x) = k⁻¹ * α x := by
      rw [map_mul, map_inv]
      simp only [mul_assoc, mul_inv_cancel_left]
    exact heq ▸ hmul
  let f : LeftCosetCarrier J k → LeftCosetCarrier J k := fun x => ⟨α x, hstable x⟩
  have hf : Function.Involutive f := by
    intro x
    exact Subtype.ext (hα x)
  obtain ⟨x, hx⟩ := finite_odd_involution_fixed f hf hoddCoset
  exact ⟨x, x.property, congrArg Subtype.val hx⟩

end Hypertournaments.GroupTheory
