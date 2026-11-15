import Mathlib.Algebra.Group.Action.End
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Restricting automorphism actions and passing to stable quotients

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`lem:klein-centralizer-generation`. These adapters retain the actual scalar
maps on subgroups, normalizers and quotient representatives.
-/

namespace Hypertournaments.GroupTheory

universe u v

variable {E : Type u} {K : Type v} [Group E] [Group K] [MulDistribMulAction E K]

/-- Restrict an automorphism action to an invariant subgroup. -/
abbrev stableSubgroupAction (H : Subgroup K)
    (hH : ∀ (e : E) (x : K), e • x ∈ H ↔ x ∈ H) : MulDistribMulAction E H where
  smul e x := ⟨e • x.val, (hH e x.val).mpr x.property⟩
  one_smul x := Subtype.ext (one_smul E x.val)
  mul_smul e f x := Subtype.ext (mul_smul e f x.val)
  smul_mul e x y := Subtype.ext (smul_mul' e x.val y.val)
  smul_one e := Subtype.ext (smul_one e)

/-- Normalizers inherit invariance from the subgroup being normalized. -/
theorem stable_normalizer (H : Subgroup K)
    (hH : ∀ (e : E) (x : K), e • x ∈ H ↔ x ∈ H) :
    ∀ (e : E) (x : K), e • x ∈ Subgroup.normalizer H ↔ x ∈ Subgroup.normalizer H := by
  have hclosure (e : E) (x : K) (hx : x ∈ Subgroup.normalizer H) : e • x ∈ Subgroup.normalizer H := by
    rw [Subgroup.mem_normalizer_iff] at hx ⊢
    intro y
    calc
      y ∈ H ↔ e⁻¹ • y ∈ H := (hH e⁻¹ y).symm
      _ ↔ x * (e⁻¹ • y) * x⁻¹ ∈ H := hx (e⁻¹ • y)
      _ ↔ e • (x * (e⁻¹ • y) * x⁻¹) ∈ H := (hH e _).symm
      _ ↔ (e • x) * y * (e • x)⁻¹ ∈ H := by
        simp only [smul_mul', smul_inv', smul_inv_smul]
  intro e x
  constructor
  · intro hx
    simpa only [inv_smul_smul] using hclosure e⁻¹ (e • x) hx
  · exact hclosure e x

/-- An invariant subgroup gives the precise congruence needed to act on cosets. -/
abbrev stableQuotientAction (H : Subgroup K)
    (hH : ∀ (e : E) (x : K), e • x ∈ H ↔ x ∈ H) :
    MulAction.QuotientAction E H where
  inv_mul_mem e := by
    intro a a' hx
    rw [← smul_inv', ← smul_mul']
    exact (hH e _).mpr hx

/-- The action on a stable normal quotient consists of group automorphisms. -/
abbrev stableQuotientDistribAction (H : Subgroup K) [H.Normal]
    (hH : ∀ (e : E) (x : K), e • x ∈ H ↔ x ∈ H) :
    MulDistribMulAction E (K ⧸ H) := by
  letI := stableQuotientAction H hH
  exact Function.Surjective.mulDistribMulAction (QuotientGroup.mk' H)
    (QuotientGroup.mk'_surjective H) (fun _ _ => rfl)

end Hypertournaments.GroupTheory
