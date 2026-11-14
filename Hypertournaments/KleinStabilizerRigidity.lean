import Lean.Elab.Tactic.Omega
import Hypertournaments.OddStabilizer
import Hypertournaments.KleinCentralizerGeneration
import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.Algebra.GroupWithZero.Action.End

/-!
# A lifted Klein action fixes the orbit of the distinguished point

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`prop:higharity-eppa-obstruction`. Conjugation is the actual normalizer
action on the pointwise base stabilizer. An extra fixed point would give
an involution with n-2 fixed vertices, contradicting alternation.
-/

namespace Hypertournaments

universe u v

private theorem pointwiseStabilizer_normalized
    {n : ℕ} {V : Type u} {E : Type v} [Group E]
    (B : Hyper n V) (s : Fin n ↪ V) (σ : E →* B.Aut)
    (hbase : ∀ a i, ∃ j, σ a • s i = s j) :
    ∀ a, σ a ∈ Subgroup.normalizer (B.pointwiseStabilizer (Set.range s) : Set B.Aut) := by
  let K := B.pointwiseStabilizer (Set.range s)
  have hclosure : ∀ a (k : B.Aut), k ∈ K → σ a * k * (σ a)⁻¹ ∈ K := by
    intro a k hk
    apply Hyper.mem_pointwiseStabilizer_iff.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hbase a⁻¹ i
    have hj' : (σ a)⁻¹ • s i = s j := by simpa only [map_inv] using hj
    change σ a • (k • ((σ a)⁻¹ • s i)) = s i
    have hkfixed : k • s j = s j :=
      (Hyper.mem_pointwiseStabilizer_iff.mp hk) (s j) ⟨j, rfl⟩
    rw [hj', hkfixed]
    rw [← hj', smul_inv_smul]
  have hle : σ.range ≤ Subgroup.normalizer K := Subgroup.le_normalizer_iff.mpr (by
    rintro _ ⟨a, rfl⟩ k hk
    exact hclosure a k hk)
  exact fun a => hle ⟨a, rfl⟩

/-- A faithful Klein action whose restriction to the base is supported on
four vertices, and which fixes x, makes the pointwise base stabilizer fix x. -/
theorem klein_pointwiseStabilizer_fixes
    {n : ℕ} {V : Type u} {E : Type v} [Finite V] [Group E] [IsKleinFour E]
    (B : Hyper n V) (hn : 4 ≤ n) (s : Fin n ↪ V) (x : V)
    (hx : x ∉ Set.range s) (w : Fin 4 ↪ Fin n)
    (σ : E →* B.Aut) (hσ : Function.Injective σ)
    (hbase : ∀ a i, ∃ j, σ a • s i = s j)
    (hpoint : ∀ a, σ a • x = x)
    (houtside : ∀ a i, i ∉ Set.range w → σ a • s i = s i)
    (k : B.pointwiseStabilizer (Set.range s)) :
    (k : B.Aut) • x = x := by
  classical
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
  let K := B.pointwiseStabilizer (Set.range s)
  let normHom : E →* Subgroup.normalizer (K : Set B.Aut) :=
    σ.codRestrict _ (pointwiseStabilizer_normalized B s σ hbase)
  let : MulDistribMulAction E K := MulDistribMulAction.compHom K normHom
  have hsmul (a : E) (z : K) :
      ((a • z : K) : B.Aut) = σ a * (z : B.Aut) * (σ a)⁻¹ := rfl
  let H : Subgroup K := MulAction.stabilizer K x
  have hpointInv (a : E) : (σ a)⁻¹ • x = x := by
    simpa only [map_inv] using hpoint a⁻¹
  have hH : ∀ (a : E) (z : K), a • z ∈ H ↔ z ∈ H := by
    intro a z
    change ((a • z : K) : B.Aut) • x = x ↔ (z : B.Aut) • x = x
    rw [hsmul]
    change σ a • ((z : B.Aut) • ((σ a)⁻¹ • x)) = x ↔ (z : B.Aut) • x = x
    rw [hpointInv]
    constructor
    · intro h
      have hh := congrArg (fun y : V => (σ a)⁻¹ • y) h
      simpa only [inv_smul_smul, hpointInv] using hh
    · intro h
      rw [h, hpoint]
  have hfixed : ∀ (a : E), a ≠ 1 → ∀ z : K, a • z = z → z ∈ H := by
    intro a hna z hz
    change (z : B.Aut) • x = x
    by_contra hmove
    have hc : σ a * (z : B.Aut) = (z : B.Aut) * σ a := by
      have hh : σ a * (z : B.Aut) * (σ a)⁻¹ = (z : B.Aut) := by
        rw [← hsmul]
        exact congrArg (fun y : K => (y : B.Aut)) hz
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using
        congrArg (fun y : B.Aut => y * σ a) hh
    have hfixImage : σ a • ((z : B.Aut) • x) = (z : B.Aut) • x := by
      rw [← mul_smul, hc, mul_smul, hpoint]
    have hzbase (i : Fin (m + 4)) : (z : B.Aut) • s i = s i :=
      (Hyper.mem_pointwiseStabilizer_iff.mp z.property) (s i) ⟨i, rfl⟩
    have himage : (z : B.Aut) • x ∉ Set.range s := by
      rintro ⟨i, hi⟩
      apply hx
      refine ⟨i, ?_⟩
      exact ((z : B.Aut) : Equiv.Perm V).injective ((hzbase i).trans hi)
    let T : Finset (Fin (m + 4)) := Finset.univ \ Finset.univ.image w
    have hT : T.card = m := by
      dsimp [T]
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
        Finset.card_image_of_injective _ w.injective]
      simp
    obtain ⟨t, ht⟩ := Function.Embedding.exists_of_card_le_finset
      (show Fintype.card (Fin m) ≤ T.card by simp [hT])
    let p : Fin m ↪ V := t.trans s
    have hp : x ∉ Set.range p := by
      rintro ⟨i, hi⟩
      exact hx ⟨t i, hi⟩
    have hq : (z : B.Aut) • x ∉ Set.range p := by
      rintro ⟨i, hi⟩
      exact himage ⟨t i, hi⟩
    have hpoints : x ≠ (z : B.Aut) • x := fun h => hmove h.symm
    let q := twoPadTuple p x ((z : B.Aut) • x) hp hq hpoints
    have hqfixed : ∀ i, (σ a : Equiv.Perm V) (q i) = q i := by
      intro i
      refine Fin.cases ?_ (fun i => ?_) i
      · exact hpoint a
      · refine Fin.cases ?_ (fun j => ?_) i
        · exact hfixImage
        · change σ a • s (t j) = s (t j)
          apply houtside a (t j)
          intro hw
          obtain ⟨b, hb⟩ := hw
          have hnot := (Finset.mem_sdiff.mp (ht ⟨j, rfl⟩)).2
          exact hnot (Finset.mem_image.mpr ⟨b, Finset.mem_univ _, hb⟩)
    have hsq : σ a * σ a = 1 := by
      rw [← map_mul, IsKleinFour.mul_self, map_one]
    have hzero := (σ a).eq_one_of_sq_eq_one_of_fixes_tuple hsq q hqfixed
    exact hna (hσ (hzero.trans (map_one σ).symm))
  let st : Fin (m + 2) ↪ V := (Fin.castLEOrderEmb (by omega : m + 2 ≤ m + 4)).toEmbedding.trans s
  have hst : Set.range st ⊆ Set.range s := by
    rintro _ ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  have hodd : Odd (Nat.card K) := B.odd_card_pointwiseStabilizer_of_tuple
    (Set.range s) st hst
  have htop : H = ⊤ := GroupTheory.klein_centralizer_saturation hodd H hH hfixed
  have hk : k ∈ H := by rw [htop]; trivial
  exact hk

end Hypertournaments
