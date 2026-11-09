import Hypertournaments.EvenSuspensionOrderedFacets
import Hypertournaments.EvenPadOrderCount
import Hypertournaments.EvenThreePadOrderedPacket

/-!
# Central local type for actual increasing three-pad suspension packets

For even old arity 2k, the exact pad count h=3 puts all pads at
the first three coordinates of every increasing ambient tuple.
The three pad-deletion facet orientations agree and all remaining
facets are positive by the concrete suspension sign table. Thus the
uniform three-pad normalized-packet theorem applies, and the local
minority index is exactly k+1.

This establishes h=3 for *increasing* ambient tuples. The extension
to arbitrary orderings requires all-arity local-index invariance.
-/

namespace Hypertournaments

theorem Hyper.evenSuspension_localIndex_increasing_threePads
    (k m a : ℕ)
    (A : Hyper (2 * k) (Fin a))
    (f : Fin (2 * k + 3) ↪o Fin (m + a))
    (hthree :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 3) :
    localIndex (A.evenSuspension m a) f.toEmbedding = k + 1 := by
  let Q := tupleVertices f.toEmbedding
  let b := A.canonicalSignTable (evenOldProjection m a Q)
  have hpad :
      ∀ i : Fin (2 * k + 3), i.val < 3 →
        evenSuspensionSignTable m a A
          (tupleVertices (facet f.toEmbedding i)) = b := by
    intro i hi
    have hlt : (f i).val < m := by
      have h := (evenPadProjection_ordered_prefix f i).1
      apply h
      rw [hthree]
      exact hi
    obtain ⟨p, hpEq⟩ :=
      (evenPadShift_mem_range_iff_lt m a (f i)).2 hlt
    have hpMem : evenPadShift m a p ∈ Q := by
      rw [hpEq]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    have hpProj : p ∈ evenPadProjection m a Q := by
      simp only [evenPadProjection, Finset.mem_filter,
        Finset.mem_univ, true_and]
      exact hpMem
    have hraw := A.evenSuspension_orient_increasingFacet_pad_three
      f hthree p hpProj i hpEq.symm
    have hread := fromOrderedSigns_facet_increasing
      (evenSuspensionSignTable m a A) f i
    exact hread.symm.trans hraw
  have hnon :
      ∀ i : Fin (2 * k + 3), 3 ≤ i.val →
        evenSuspensionSignTable m a A
          (tupleVertices (facet f.toEmbedding i)) = true := by
    intro i hi
    have hnot : ¬(f i).val < m := by
      intro hp
      have hsmall := (evenPadProjection_ordered_prefix f i).2 hp
      rw [hthree] at hsmall
      omega
    have hnotRange : f i ∉ Set.range (evenPadShift m a) := by
      intro hp
      exact hnot ((evenPadShift_mem_range_iff_lt m a (f i)).1 hp)
    have hraw := A.evenSuspension_orient_increasingFacet_nonpad_three
      f hthree i hnotRange
    have hread := fromOrderedSigns_facet_increasing
      (evenSuspensionSignTable m a A) f i
    exact hread.symm.trans hraw
  exact localIndex_ordered_threePad_central k
    (evenSuspensionSignTable m a A) f b hpad hnon

end Hypertournaments
