import Mathlib.Tactic.Ext
import Hypertournaments.NormalizedPacketSign
import Hypertournaments.LocalTypes
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Card
import Lean.Elab.Tactic.Omega

/-!
# Four equal normalized facets and a distinguished extra vertex

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:higharity-no-eppa`. The selected four facet indices can be moved
into the first n coordinates, leaving a distinct final vertex.
-/

namespace Hypertournaments

def HasFourEqualFacets {n : ℕ} (P : Hyper n (Fin (n + 1))) : Prop :=
  ∃ u : Fin 4 ↪ Fin (n + 1), ∀ i,
    normalizedFacet P (Function.Embedding.refl _) (u i) =
      normalizedFacet P (Function.Embedding.refl _) (u 0)

def HasFourEqualBaseFacets {n : ℕ} (P : Hyper n (Fin (n + 1))) : Prop :=
  ∃ u : Fin 4 ↪ Fin n, ∀ i,
    normalizedFacet P (Function.Embedding.refl _) (u i).castSucc =
      normalizedFacet P (Function.Embedding.refl _) (u 0).castSucc

private theorem bool_counts {k : ℕ} (bits : Fin k → Bool) :
    (Finset.univ.filter (fun i => bits i = true)).card +
      (Finset.univ.filter (fun i => bits i = false)).card = k := by
  classical
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin k)))
    (p := fun i => bits i = true)
  have heq : (Finset.univ.filter (fun i => ¬ bits i = true)) =
      Finset.univ.filter (fun i => bits i = false) := by
    ext i
    cases bits i <;> simp
  rw [heq] at h
  simpa using h

private theorem four_equal_of_count {k : ℕ} (bits : Fin k → Bool) (b : Bool)
    (h : 4 ≤ (Finset.univ.filter (fun i => bits i = b)).card) :
    ∃ u : Fin 4 ↪ Fin k, ∀ i, bits (u i) = bits (u 0) := by
  classical
  have hc : Fintype.card (Fin 4) ≤ (Finset.univ.filter (fun i => bits i = b)).card := by
    simpa using h
  obtain ⟨u, hu⟩ := Function.Embedding.exists_of_card_le_finset hc
  have hb (i : Fin 4) : bits (u i) = b :=
    (Finset.mem_filter.mp (hu ⟨i, rfl⟩)).2
  exact ⟨u, fun i => (hb i).trans (hb 0).symm⟩

/-- Seven Boolean facet values contain four equal entries. -/
theorem hasFourEqualFacets_of_six_le {n : ℕ} (hn : 6 ≤ n)
    (P : Hyper n (Fin (n + 1))) : HasFourEqualFacets P := by
  classical
  let bits := fun i => normalizedFacet P (Function.Embedding.refl _) i
  have hc := bool_counts bits
  have h : 4 ≤ (Finset.univ.filter (fun i => bits i = true)).card ∨
      4 ≤ (Finset.univ.filter (fun i => bits i = false)).card := by omega
  rcases h with h | h
  · exact four_equal_of_count bits true h
  · exact four_equal_of_count bits false h

/-- A packet with at least four entries in its larger color class satisfies
the local obstruction's equal-facet requirement. -/
theorem hasFourEqualFacets_of_localIndex_le {n : ℕ}
    (P : Hyper n (Fin (n + 1)))
    (hd : localIndex P (Function.Embedding.refl _) ≤ n - 3) (hn : 3 ≤ n) :
    HasFourEqualFacets P := by
  classical
  let bits := fun i => normalizedFacet P (Function.Embedding.refl _) i
  have hc := bool_counts bits
  have hpos : positiveFacetCount P (Function.Embedding.refl _) =
      (Finset.univ.filter (fun i => bits i = true)).card := rfl
  unfold localIndex at hd
  rw [hpos] at hd
  have h : 4 ≤ (Finset.univ.filter (fun i => bits i = true)).card ∨
      4 ≤ (Finset.univ.filter (fun i => bits i = false)).card := by omega
  rcases h with h | h
  · exact four_equal_of_count bits true h
  · exact four_equal_of_count bits false h

/-- Reindex the packet so the four selected indices lie in the common base,
and the final coordinate is a different vertex. -/
theorem reindex_four_equal_to_base {n : ℕ} (hn : 4 ≤ n)
    (P : Hyper n (Fin (n + 1))) (hP : HasFourEqualFacets P) :
    ∃ σ : Equiv.Perm (Fin (n + 1)),
      HasFourEqualBaseFacets (P.pullback σ.toEmbedding) := by
  classical
  obtain ⟨u, hu⟩ := hP
  have hcard : (Finset.univ.image u).card < (Finset.univ : Finset (Fin (n + 1))).card := by
    rw [Finset.card_image_of_injective _ u.injective]
    simp only [Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨a, _, ha⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hne (i : Fin 4) : u i ≠ a := by
    intro hi
    exact ha (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap (Fin.last n) a
  have hs : σ (Fin.last n) = a := Equiv.swap_apply_left _ _
  have hlt (i : Fin 4) : (σ.symm (u i)).val < n := by
    have hi : σ.symm (u i) ≠ Fin.last n := by
      intro hh
      have hx := congrArg σ hh
      rw [σ.apply_symm_apply, hs] at hx
      exact hne i hx
    have hv : (σ.symm (u i)).val ≠ n := by
      intro hh
      exact hi (Fin.ext hh)
    have hb := (σ.symm (u i)).isLt
    omega
  let w : Fin 4 ↪ Fin n := ⟨fun i => ⟨(σ.symm (u i)).val, hlt i⟩, by
    intro i j hij
    apply u.injective
    apply σ.symm.injective
    exact Fin.ext (congrArg (fun z : Fin n => z.val) hij)⟩
  have hw (i : Fin 4) : σ (w i).castSucc = u i := by
    have hh : (w i).castSucc = σ.symm (u i) := Fin.ext rfl
    rw [hh]
    exact σ.apply_symm_apply _
  refine ⟨σ, w, ?_⟩
  intro i
  change normalizedFacet P (σ.toEmbedding.trans (Function.Embedding.refl _)) (w i).castSucc =
    normalizedFacet P (σ.toEmbedding.trans (Function.Embedding.refl _)) (w 0).castSucc
  rw [normalizedFacet_perm_signBit, normalizedFacet_perm_signBit, hw, hw, hu]

end Hypertournaments
