import Hypertournaments.InvariantSylow
import Hypertournaments.KleinFixedPoint
import Hypertournaments.OddCosetFixedPoint
import Hypertournaments.StableGroupAction
import Mathlib.GroupTheory.Nilpotent
import Mathlib.Algebra.Order.Ring.Abs

/-!
# Centralizer saturation under a Klein action

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`lem:klein-centralizer-generation`. The proof uses invariant Sylow subgroups,
the finite p-group normalizer condition, and an odd-coset fixed representative.
All restriction and quotient actions are built on their actual carriers.
-/

namespace Hypertournaments.GroupTheory

universe u v

/-- In an odd finite group acted on by a 2-group containing a Klein subgroup,
a stable subgroup containing every nontrivial scalar's fixed points is full. -/
theorem centralizer_saturation
    {E : Type u} {K : Type v} [Group E] [Group K] [Finite K]
    [MulDistribMulAction E K]
    (hE : IsPGroup 2 E) (hK : Odd (Nat.card K))
    (a b : E) (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b)
    (hna : a ≠ 1) (hnb : b ≠ 1) (hnab : a * b ≠ 1)
    (H : Subgroup K) (hH : ∀ (e : E) (x : K), e • x ∈ H ↔ x ∈ H)
    (hfixed : ∀ (e : E), e ≠ 1 → ∀ x : K, e • x = x → x ∈ H) : H = ⊤ := by
  classical
  by_contra hproper
  obtain ⟨p, hp, hpIndex⟩ := Nat.exists_prime_and_dvd
    (ne_of_gt (H.one_lt_index_of_ne_top hproper))
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := Hypertournaments.exists_invariant_sylow_of_odd_card p hE hK
  have hPnot : ¬ (P : Subgroup K) ≤ H := by
    intro hle
    exact P.not_dvd_index (dvd_trans hpIndex (Subgroup.index_dvd_of_le hle))
  let : MulDistribMulAction E P := stableSubgroupAction (P : Subgroup K) hP
  let J : Subgroup P := H.comap (P : Subgroup K).subtype
  have hJ : ∀ (e : E) (x : P), e • x ∈ J ↔ x ∈ J := by
    intro e x
    exact hH e x.val
  have hJproper : J ≠ ⊤ := by
    intro htop
    apply hPnot
    intro x hx
    have hmem : (⟨x, hx⟩ : P) ∈ J := by rw [htop]; trivial
    exact hmem
  let : Group.IsNilpotent P := P.isPGroup'.isNilpotent
  have hJN : J < Subgroup.normalizer (J : Set P) := Group.normalizerCondition_of_isNilpotent J (lt_top_iff_ne_top.mpr hJproper)
  let N := Subgroup.normalizer (J : Set P)
  have hN : ∀ (e : E) (x : P), e • x ∈ N ↔ x ∈ N := stable_normalizer J hJ
  let : MulDistribMulAction E N := stableSubgroupAction N hN
  let M : Subgroup N := J.subgroupOf N
  have hM : ∀ (e : E) (x : N), e • x ∈ M ↔ x ∈ M := by
    intro e x
    exact hJ e x.val
  have hMproper : M ≠ ⊤ := by
    intro htop
    have hNJ : N ≤ J := Subgroup.subgroupOf_eq_top.mp htop
    exact (not_le_of_gt hJN) hNJ
  let : M.Normal := Subgroup.normal_in_normalizer (H := J)
  let Q := N ⧸ M
  let : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hMproper
  let : MulDistribMulAction E Q := stableQuotientDistribAction M hM
  obtain ⟨e, hne, hee, q, hq, heq⟩ :=
    klein_action_fixed_witness a b ha hb hab hna hnb hnab (Q := Q)
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  change (↑(e • k) : Q) = ↑k at heq
  have hkcoset : k⁻¹ * (e • k) ∈ M := QuotientGroup.eq.mp heq.symm
  let α : MulAut N := MulDistribMulAction.toMulAut E N e
  have hα : Function.Involutive α := by
    intro x
    change e • (e • x) = x
    rw [← mul_smul, hee, one_smul]
  have hoddP : Odd (Nat.card P) := hK.of_dvd_nat (P : Subgroup K).card_subgroup_dvd_card
  have hoddN : Odd (Nat.card N) := hoddP.of_dvd_nat N.card_subgroup_dvd_card
  have hoddM : Odd (Nat.card M) := hoddN.of_dvd_nat M.card_subgroup_dvd_card
  obtain ⟨x, hxcoset, hxfixed⟩ := odd_invariant_coset_fixed_representative M hoddM α hα
    (fun j hj => (hM e j).mpr hj) k hkcoset
  have hxH : ((x : N) : P).val ∈ H :=
    hfixed e hne _ (congrArg (fun y : N => (y : P).val) hxfixed)
  have hxM : x ∈ M := hxH
  have hkinv : k⁻¹ ∈ M := (M.mul_mem_cancel_right hxM).mp hxcoset
  have hkM : k ∈ M := by simpa only [inv_inv] using M.inv_mem hkinv
  exact hq ((QuotientGroup.eq_one_iff k).mpr hkM)

/-- The exact generation lemma used by the article. The set of elements
fixed by some nonidentity scalar is stable under conjugation of that scalar,
so its generated subgroup satisfies centralizer saturation. -/
theorem nonidentity_fixed_elements_generate
    {E : Type u} {K : Type v} [Group E] [Group K] [Finite K]
    [MulDistribMulAction E K]
    (hE : IsPGroup 2 E) (hK : Odd (Nat.card K))
    (a b : E) (ha : a * a = 1) (hb : b * b = 1) (hab : Commute a b)
    (hna : a ≠ 1) (hnb : b ≠ 1) (hnab : a * b ≠ 1) :
    Subgroup.closure {x : K | ∃ e : E, e ≠ 1 ∧ e • x = x} = ⊤ := by
  let S : Set K := {x : K | ∃ e : E, e ≠ 1 ∧ e • x = x}
  let H := Subgroup.closure S
  have hS (e : E) (x : K) (hx : x ∈ S) : e • x ∈ S := by
    obtain ⟨d, hd, hdx⟩ := hx
    refine ⟨e * d * e⁻¹, ?_, ?_⟩
    · intro hconj
      apply hd
      simpa only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one,
        inv_mul_cancel] using congrArg (fun y : E => e⁻¹ * y * e) hconj
    · rw [mul_smul, mul_smul, inv_smul_smul, hdx]
  have hclosure (e : E) (x : K) (hx : x ∈ H) : e • x ∈ H := by
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (hS e x hx)
    | one => simpa only [smul_one] using H.one_mem
    | mul x y hx hy ihx ihy => simpa only [smul_mul'] using H.mul_mem ihx ihy
    | inv x hx ihx => simpa only [smul_inv'] using H.inv_mem ihx
  have hH : ∀ (e : E) (x : K), e • x ∈ H ↔ x ∈ H := by
    intro e x
    constructor
    · intro hx
      simpa only [inv_smul_smul] using hclosure e⁻¹ (e • x) hx
    · exact hclosure e x
  exact centralizer_saturation hE hK a b ha hb hab hna hnb hnab H hH
    (fun e he x hx => Subgroup.subset_closure ⟨e, he, hx⟩)

end Hypertournaments.GroupTheory
