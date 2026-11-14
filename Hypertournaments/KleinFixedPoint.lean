import Mathlib.GroupTheory.FixedPointFree
import Mathlib.Algebra.Group.Action.End

/-!
# Fixed elements for two involutive automorphisms

This is the elementary Klein-action ingredient used by the EPPA obstruction.
Neither odd order nor faithfulness of the action is required: two fixed-point-free
involutions are both inversion, so their product acts trivially.
-/

namespace Hypertournaments.GroupTheory

theorem two_involutions_fixed_witness
    {Q : Type*} [Group Q] [Finite Q] [Nontrivial Q]
    (a b : MulAut Q)
    (ha : Function.Involutive a) (hb : Function.Involutive b) :
    (∃ x : Q, x ≠ 1 ∧ a x = x) ∨
    (∃ x : Q, x ≠ 1 ∧ b x = x) ∨
    (∃ x : Q, x ≠ 1 ∧ (a * b) x = x) := by
  classical
  by_cases hA : ∃ x : Q, x ≠ 1 ∧ a x = x
  · exact Or.inl hA
  by_cases hB : ∃ x : Q, x ≠ 1 ∧ b x = x
  · exact Or.inr (Or.inl hB)
  have hAf : MonoidHom.FixedPointFree a := by
    intro x hx
    by_contra hne
    exact hA ⟨x, hne, hx⟩
  have hBf : MonoidHom.FixedPointFree b := by
    intro x hx
    by_contra hne
    exact hB ⟨x, hne, hx⟩
  have hAi := hAf.coe_eq_inv_of_involutive ha
  have hBi := hBf.coe_eq_inv_of_involutive hb
  obtain ⟨x, hx⟩ := exists_ne (1 : Q)
  refine Or.inr (Or.inr ⟨x, hx, ?_⟩)
  change a (b x) = x
  rw [show a (b x) = (b x)⁻¹ from congrFun hAi (b x)]
  rw [show b x = x⁻¹ from congrFun hBi x, inv_inv]

/-- A source group with two distinct nonidentity involutions supplies a
nonidentity acting element fixing a nonidentity point of a finite group.
The action need not be faithful, nor does the proof need commutativity. -/
theorem klein_hom_fixed_witness
    {E Q : Type*} [Group E] [Group Q] [Finite Q] [Nontrivial Q]
    (ρ : E →* MulAut Q) (a b : E)
    (ha : a * a = 1) (hb : b * b = 1)
    (hna : a ≠ 1) (hnb : b ≠ 1) (hab : a * b ≠ 1) :
    ∃ e : E, e ≠ 1 ∧ ∃ x : Q, x ≠ 1 ∧ ρ e x = x := by
  have ha' : Function.Involutive (ρ a) := by
    intro x
    change (ρ a * ρ a) x = x
    rw [← map_mul, ha, map_one]
    rfl
  have hb' : Function.Involutive (ρ b) := by
    intro x
    change (ρ b * ρ b) x = x
    rw [← map_mul, hb, map_one]
    rfl
  rcases two_involutions_fixed_witness (ρ a) (ρ b) ha' hb' with h | h | h
  · exact ⟨a, hna, h⟩
  · exact ⟨b, hnb, h⟩
  · refine ⟨a * b, hab, ?_⟩
    simpa only [map_mul] using h

/-- Action form retaining an involutive nonidentity acting element. -/
theorem klein_action_fixed_witness
    {E Q : Type*} [Group E] [Group Q] [Finite Q] [Nontrivial Q]
    [MulDistribMulAction E Q] (a b : E)
    (ha : a * a = 1) (hb : b * b = 1) (habComm : Commute a b)
    (hna : a ≠ 1) (hnb : b ≠ 1) (hab : a * b ≠ 1) :
    ∃ e : E, e ≠ 1 ∧ e * e = 1 ∧ ∃ x : Q, x ≠ 1 ∧ e • x = x := by
  let ρ : E →* MulAut Q := MulDistribMulAction.toMulAut E Q
  have ha' : Function.Involutive (ρ a) := by
    intro x
    change (ρ a * ρ a) x = x
    rw [← map_mul, ha, map_one]
    rfl
  have hb' : Function.Involutive (ρ b) := by
    intro x
    change (ρ b * ρ b) x = x
    rw [← map_mul, hb, map_one]
    rfl
  have hab' : (a * b) * (a * b) = 1 := by
    calc
      (a * b) * (a * b) = a * (b * a) * b := by simp only [mul_assoc]
      _ = a * (a * b) * b := by rw [← habComm.eq]
      _ = (a * a) * (b * b) := by simp only [mul_assoc]
      _ = 1 := by rw [ha, hb, one_mul]
  rcases two_involutions_fixed_witness (ρ a) (ρ b) ha' hb' with h | h | h
  · obtain ⟨x, hx, hfix⟩ := h
    exact ⟨a, hna, ha, x, hx, hfix⟩
  · obtain ⟨x, hx, hfix⟩ := h
    exact ⟨b, hnb, hb, x, hx, hfix⟩
  · obtain ⟨x, hx, hfix⟩ := h
    have hf : (a * b) • x = x := by
      change ρ (a * b) x = x
      simpa only [map_mul] using hfix
    exact ⟨a * b, hab, hab', x, hx, hf⟩

end Hypertournaments.GroupTheory
