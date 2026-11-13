import Mathlib.Tactic.Ext
import Hypertournaments.OnePointMixedFactor

/-!
# Inherited local admissibility of nonmixed one-point tuples

The full two-coordinate reflection reconstructs a lower-arity
hypertournament on the canonical union of two one-point extensions.
A local tuple that omits either new vertex belongs to one original
side, where admissibility is already known.

We make the reasoning intrinsic: the local type index is preserved by
*arbitrary* vertex embeddings that preserve all oriented n-tuples,
not just order embeddings. The nonmixed tuple factorization then
immediately transfers the original local admissibility to any
hypothetical joint structure.

The matching-profile hypothesis of the main reflection will therefore
be needed only for genuinely mixed tuples.
-/

namespace Hypertournaments

/-- Intrinsic local-type indices are preserved by every embedding of
hyperorientations. No linear order is used. -/
theorem localIndex_preserves
    {n : ℕ} {U V : Type*}
    (A : Hyper n U) (E : Hyper n V) (f : U ↪ V)
    (hf : Preserves A E f) (t : Fin (n + 1) ↪ U) :
    localIndex A t = localIndex E (t.trans f) := by
  have hfacet (i : Fin (n + 1)) :
      facet (t.trans f) i = (facet t i).trans f := rfl
  have hsign (i : Fin (n + 1)) :
      normalizedFacet A t i =
      normalizedFacet E (t.trans f) i := by
    unfold normalizedFacet
    rw [hfacet]
    exact congrArg
      (fun b : Bool => Bool.xor b (decide (i.val % 2 = 1)))
      (hf (facet t i)).symm
  have hcount :
      positiveFacetCount A t =
      positiveFacetCount E (t.trans f) := by
    unfold positiveFacetCount
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hsign i]
  unfold localIndex
  rw [hcount]

/-- All nonmixed tuples of a canonical one-point joint inherit
admissibility from the left or right original side. This is the exact
nonmixed premise required by the two-coordinate reflection. -/
theorem onePoint_nonmixed_admissible
    {n a : ℕ} (S : Set ℕ)
    (L R : Hyper n (Fin (a + 1)))
    (E : Hyper n (Fin (a + 2)))
    (hL : Admissible S L) (hR : Admissible S R)
    (hEL : Preserves L E (leftJointInclusion a))
    (hER : Preserves R E (rightJointInclusion a))
    (t : Fin (n + 1) ↪ Fin (a + 2))
    (hnot : ¬ IsMixedOnePointTuple n a t) :
    localIndex E t ∈ S := by
  rcases onePointTuple_nonmixed_factors t hnot with ⟨l, hl⟩ | ⟨r, hr⟩
  · rw [← hl, ← localIndex_preserves L E (leftJointInclusion a) hEL l]
    exact hL l
  · rw [← hr, ← localIndex_preserves R E (rightJointInclusion a) hER r]
    exact hR r

end Hypertournaments
