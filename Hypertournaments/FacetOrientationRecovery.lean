import Hypertournaments.CanonicalOrientationRecovery
import Hypertournaments.CanonicalPacket

/-!
# Recovering a local orientation from its actual facets

Every n-element subset of `Fin (n+1)` omits exactly one vertex. Its
increasing enumeration is the corresponding actual facet, so preserving
all those facets preserves all ordered injective n-tuples.
-/

namespace Hypertournaments

/-- Each canonical n-tuple on n+1 vertices is literally a facet of the
identity tuple. -/
theorem exists_canonical_eq_facet {n : ℕ}
    (Q : Finset (Fin (n + 1))) (hQ : Q.card = n) :
    ∃ i : Fin (n + 1), (Q.orderEmbOfFin hQ).toEmbedding =
      facet (Function.Embedding.refl (Fin (n + 1))) i := by
  classical
  have hnot : ¬ (Finset.univ : Finset (Fin (n + 1))) ⊆ Q := by
    intro h
    have hc := Finset.card_le_card h
    simp only [Finset.card_univ, Fintype.card_fin] at hc
    omega
  obtain ⟨i, _, hi⟩ := Finset.not_subset.mp hnot
  have hsub : Q ⊆ (Finset.univ : Finset (Fin (n + 1))).erase i := by
    intro x hx
    exact Finset.mem_erase.mpr ⟨by intro h; subst x; exact hi hx, Finset.mem_univ x⟩
  have heq : Q = (Finset.univ : Finset (Fin (n + 1))).erase i :=
    Finset.eq_of_subset_of_card_le hsub (by simp [hQ])
  let f : Fin n ↪ Fin (n + 1) := facet (Function.Embedding.refl _) i
  have hf : (f : Fin n → Fin (n + 1)) = Q.orderEmbOfFin hQ := by
    apply Finset.orderEmbOfFin_unique hQ
    · intro j
      rw [heq]
      exact Finset.mem_erase.mpr ⟨Fin.succAbove_ne i j, Finset.mem_univ _⟩
    · exact Fin.strictMono_succAbove i
  exact ⟨i, Function.Embedding.ext (congrFun hf.symm)⟩

/-- On n+1 source vertices, checking the n+1 actual facets is enough for
intrinsic preservation on all ordered injective n-tuples. -/
theorem preserves_of_facets {n : ℕ} {V : Type*}
    (A : Hyper n (Fin (n + 1))) (B : Hyper n V) (e : Fin (n + 1) ↪ V)
    (h : ∀ i : Fin (n + 1),
      B.orient ((facet (Function.Embedding.refl _) i).trans e) =
        A.orient (facet (Function.Embedding.refl _) i)) : Preserves A B e := by
  apply preserves_of_canonical A B e
  intro Q hQ
  obtain ⟨i, hi⟩ := exists_canonical_eq_facet Q hQ
  rw [hi]
  exact h i

/-- Equality of normalized local packets also suffices: their coordinate
normalizations cancel separately on each actual facet. -/
theorem preserves_of_normalizedFacets {n : ℕ} {V : Type*}
    (A : Hyper n (Fin (n + 1))) (B : Hyper n V) (e : Fin (n + 1) ↪ V)
    (h : ∀ i : Fin (n + 1),
      normalizedFacet B e i = normalizedFacet A (Function.Embedding.refl _) i) :
    Preserves A B e := by
  apply preserves_of_facets A B e
  intro i
  have hi := h i
  unfold normalizedFacet at hi
  have hc := congrArg (fun b => Bool.xor b (decide (i.val % 2 = 1))) hi
  have hf : facet e i = (facet (Function.Embedding.refl _) i).trans e := by
    ext j
    rfl
  simpa only [Bool.xor_assoc, Bool.xor_self, Bool.xor_false, hf] using hc

end Hypertournaments
