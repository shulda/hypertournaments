import Hypertournaments.LocalTypes

/-!
# Preservation of intrinsic local types along hypertournament embeddings

A vertex embedding preserving every orientation preserves all
normalized local packet words and therefore their minority index.
This lemma applies in every arity and does not require an ordering
on either ambient vertex type.
-/

namespace Hypertournaments

/-- The true local index is invariant under any embedding preserving
all n-tuple orientations, uniformly in the arity. -/
theorem localIndex_preserves
    {n : ℕ} {V W : Type*}
    (A : Hyper n V) (B : Hyper n W)
    (e : V ↪ W) (h : Preserves A B e)
    (f : Fin (n+1) ↪ V) :
    localIndex B (f.trans e) = localIndex A f := by
  have hfacet (i : Fin (n+1)) :
      B.orient (facet (f.trans e) i) =
        A.orient (facet f i) := by
    have hf : facet (f.trans e) i = (facet f i).trans e := by
      ext j
      rfl
    rw [hf]
    exact h (facet f i)
  have hnorm (i : Fin (n+1)) :
      normalizedFacet B (f.trans e) i = normalizedFacet A f i := by
    unfold normalizedFacet
    rw [hfacet i]
  have hcount :
      positiveFacetCount B (f.trans e) = positiveFacetCount A f := by
    unfold positiveFacetCount
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hnorm i]
  unfold localIndex
  rw [hcount]

end Hypertournaments
