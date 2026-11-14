import Hypertournaments.CentralizerSaturation
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
# Centralizer generation for an arbitrary Klein four-group

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`lem:klein-centralizer-generation`. Mathlib's `IsKleinFour` mixin supplies
all source-group hypotheses; neither chosen generators nor a p-group
provider are assumptions of these article-facing results.
-/

namespace Hypertournaments.GroupTheory

universe u v

private theorem klein_independent_involutions
    {E : Type u} [Group E] [IsKleinFour E] :
    ∃ a b : E, a * a = 1 ∧ b * b = 1 ∧ Commute a b ∧
      a ≠ 1 ∧ b ≠ 1 ∧ a * b ≠ 1 := by
  classical
  let : Finite E := IsKleinFour.instFinite
  let : Fintype E := Fintype.ofFinite E
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {(1 : E)}) (t := Finset.univ) (by simp [IsKleinFour.card_four'])
  have hna : a ≠ 1 := by simpa only [Finset.mem_singleton] using ha
  obtain ⟨b, _, hb⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := {(1 : E), a}) (t := Finset.univ) (by
      simp [IsKleinFour.card_four', Ne.symm hna])
  have hnb : b ≠ 1 := by
    intro h
    exact hb (by simp [h])
  have hba : b ≠ a := by
    intro h
    exact hb (by simp [h])
  refine ⟨a, b, IsKleinFour.mul_self a, IsKleinFour.mul_self b, ?_, hna, hnb, ?_⟩
  · exact (IsKleinFour.isMulCommutative (G := E)).is_comm.comm a b
  · intro h
    rw [mul_eq_one_iff_eq_inv, IsKleinFour.inv_eq_self] at h
    exact hba h.symm

/-- A stable subgroup of an odd finite group containing all centralizers of
nonidentity Klein elements is the whole group. -/
theorem klein_centralizer_saturation
    {E : Type u} {K : Type v} [Group E] [IsKleinFour E]
    [Group K] [Finite K] [MulDistribMulAction E K]
    (hK : Odd (Nat.card K)) (H : Subgroup K)
    (hH : ∀ (e : E) (x : K), e • x ∈ H ↔ x ∈ H)
    (hfixed : ∀ (e : E), e ≠ 1 → ∀ x : K, e • x = x → x ∈ H) : H = ⊤ := by
  have hE : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by simp)
  obtain ⟨a, b, ha, hb, hab, hna, hnb, hnab⟩ := klein_independent_involutions (E := E)
  exact centralizer_saturation hE hK a b ha hb hab hna hnb hnab H hH hfixed

/-- The source-exact generation theorem: nonidentity Klein fixed elements
generate every finite odd group on which the Klein group acts by automorphisms. -/
theorem klein_nonidentity_fixed_elements_generate
    {E : Type u} {K : Type v} [Group E] [IsKleinFour E]
    [Group K] [Finite K] [MulDistribMulAction E K]
    (hK : Odd (Nat.card K)) :
    Subgroup.closure {x : K | ∃ e : E, e ≠ 1 ∧ e • x = x} = ⊤ := by
  have hE : IsPGroup 2 E := IsPGroup.of_card (n := 2) (by simp)
  obtain ⟨a, b, ha, hb, hab, hna, hnb, hnab⟩ := klein_independent_involutions (E := E)
  exact nonidentity_fixed_elements_generate hE hK a b ha hb hab hna hnb hnab

end Hypertournaments.GroupTheory
