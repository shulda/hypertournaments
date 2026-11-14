import Hypertournaments.LocalPairCancellation
import Hypertournaments.IncreasingTupleUniqueness

/-!
# Constant full-packet tails witness failure of pair cancellation

The order transported along a full tuple makes each pair-link tuple a
facet obtained by deleting one of its tail coordinates. Consequently a
constant family of those facets gives an actual auxiliary order and pair
for which all links have the same orientation.
-/

namespace Hypertournaments

private theorem canonical_pairLink_is_facet {k : ℕ} (hk : 2 ≤ k)
    (q : Fin (k + 1) ↪ Fin (k + 2)) (h : IsPairLink 0 1 q) :
    ∃ a : Fin (k + 2), 2 ≤ a.val ∧ q = Fin.succAboveEmb a := by
  classical
  have h0 : q 0 = 0 := h.1 0 rfl
  have hone : (1 : Fin (k + 1)).val = 1 :=
    Nat.mod_eq_of_lt (show 1 < k + 1 by omega)
  have h1 : q 1 = 1 := h.2.1 1 hone
  have hmono : StrictMono q := by
    intro i j hij
    by_cases hi0 : i.val = 0
    · have hi : i = 0 := Fin.ext hi0
      have hj : j ≠ 0 := by intro he; subst j; simp at hij
      have hqj : q j ≠ 0 := by intro he; exact hj (q.injective (he.trans h0.symm))
      rw [hi, h0]
      exact Fin.pos_iff_ne_zero.mpr hqj
    · by_cases hi1 : i.val = 1
      · have hi : i = 1 := Fin.ext (hi1.trans hone.symm)
        have hj0 : j ≠ 0 := by intro he; subst j; simp at hij
        have hj1 : j ≠ 1 := by intro he; subst j; rw [hi] at hij; simp at hij
        have hqj0 : q j ≠ 0 := by intro he; exact hj0 (q.injective (he.trans h0.symm))
        have hqj1 : q j ≠ 1 := by intro he; exact hj1 (q.injective (he.trans h1.symm))
        rw [hi, h1]
        change 1 < (q j).val
        have hqj0v : (q j).val ≠ 0 := fun he => hqj0 (Fin.ext he)
        have hqj1v : (q j).val ≠ 1 := fun he => hqj1 (Fin.ext he)
        omega
      · exact h.2.2 i j (by omega) hij
  have hns : ¬ Function.Surjective q := by
    intro hs
    have hc := Fintype.card_le_of_surjective q hs
    simp only [Fintype.card_fin] at hc
    omega
  have hex : ∃ a : Fin (k + 2), ∀ i, q i ≠ a := by
    simpa only [Function.Surjective, not_forall, not_exists] using hns
  obtain ⟨a, ha⟩ := hex
  have ha2 : 2 ≤ a.val := by
    have ha0 : a.val ≠ 0 := by
      intro he
      exact ha 0 (h0.trans (Fin.ext he).symm)
    have ha1 : a.val ≠ 1 := by
      intro he
      exact ha 1 (h1.trans (Fin.ext he).symm)
    omega
  have hsub : tupleVertices q ⊆ (Finset.univ : Finset (Fin (k + 2))).erase a := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact Finset.mem_erase.mpr ⟨ha i, Finset.mem_univ _⟩
  have hsupp : tupleVertices q = (Finset.univ : Finset (Fin (k + 2))).erase a := by
    apply Finset.eq_of_subset_of_card_le hsub
    simp only [tupleVertices, Finset.card_image_of_injective _ q.injective,
      Finset.card_univ, Fintype.card_fin,
      Finset.card_erase_of_mem (Finset.mem_univ a)]
    omega
  have hsupp' : tupleVertices (Fin.succAboveEmb a) =
      (Finset.univ : Finset (Fin (k + 2))).erase a := by
    have hrefl : tupleVertices (Function.Embedding.refl (Fin (k + 2))) =
        (Finset.univ : Finset (Fin (k + 2))) := by
      ext x
      constructor
      · intro _; exact Finset.mem_univ _
      · intro _; exact Finset.mem_image.mpr ⟨x, Finset.mem_univ _, rfl⟩
    have hh := tupleVertices_facet_eq_erase (Function.Embedding.refl (Fin (k + 2))) a
    rw [hrefl] at hh
    exact hh
  have heq := increasingEmb_eq_of_tupleVertices
    (OrderEmbedding.ofStrictMono q hmono) (Fin.succAboveOrderEmb a)
    (hsupp.trans hsupp'.symm)
  refine ⟨a, ha2, ?_⟩
  ext i
  exact congrArg Fin.val (congrArg (fun e : Fin (k + 1) ↪o Fin (k + 2) => e i) heq)

/-- An actual constant link on every tail-deleted facet of a bijective
full tuple contradicts pair cancellation. -/
theorem not_pairCancelling_of_constant_full_tail
    {k : ℕ} {V : Type*} (hk : 2 ≤ k) (A : Hyper (k + 1) V)
    (f : Fin (k + 2) ↪ V) (hf : Function.Surjective f) (b : Bool)
    (hraw : ∀ i : Fin k, A.orient (facet f i.succ.succ) = b) :
    ¬ PairCancelling A := by
  classical
  let e : Fin (k + 2) ≃ V := Equiv.ofBijective f ⟨f.injective, hf⟩
  let order : LinearOrder V := LinearOrder.lift' e.symm e.symm.injective
  let : LinearOrder V := order
  have hconst (t : Fin (k + 1) ↪ V) (ht : IsPairLink (f 0) (f 1) t) :
      A.orient t = b := by
    let q : Fin (k + 1) ↪ Fin (k + 2) := t.trans e.symm.toEmbedding
    have hq : IsPairLink 0 1 q := by
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        change e.symm (t i) = 0
        rw [ht.1 i hi]
        exact e.symm_apply_apply 0
      · intro i hi
        change e.symm (t i) = 1
        rw [ht.2.1 i hi]
        exact e.symm_apply_apply 1
      · intro i j hi hij
        exact ht.2.2 i j hi hij
    obtain ⟨a, ha, heq⟩ := canonical_pairLink_is_facet hk q hq
    have ht_eq : t = facet f a := by
      ext i
      apply e.symm.injective
      change q i = e.symm (e (a.succAbove i))
      rw [e.symm_apply_apply]
      exact congrArg (fun q : Fin (k + 1) ↪ Fin (k + 2) => q i) heq
    obtain ⟨i, rfl⟩ : ∃ i : Fin k, a = i.succ.succ :=
      ⟨⟨a.val - 2, by omega⟩, Fin.ext (by simp; omega)⟩
    rw [ht_eq]
    exact hraw i
  intro hpc
  have huv : f 0 ≠ f 1 := by
    intro he
    have hh := congrArg Fin.val (f.injective he)
    simp at hh
  obtain ⟨t, s, ht, hs, hne⟩ := hpc.2.2 order (f 0) (f 1) huv
  exact hne ((hconst t ht).trans (hconst s hs).symm)

end Hypertournaments
