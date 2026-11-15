import Hypertournaments.OddToggleP3ActualParentOrderedTuple
import Hypertournaments.OddToggleP3OrderedFacetCanonicalSigns

/-!
# Complete genuine RAW facet dictionary of a selected p3 parent packet

From the actual strictly increasing selected parent tuple with
old block vertices at positions 0,...,m-1, left fresh at m,
right fresh at m+1, we identify the intrinsic orientation of
each facet with the canonical sign on its literal true
(n=4k+3)-vertex set.

The first m raw signs are exactly the selected genuine mixed
facet canonical signs. The penultimate raw sign (deleting
left fresh) is the right-side endpoint sign, and the final
raw sign (deleting right fresh) is the left-side endpoint.
This is EXACTLY the packet ordering needed by the
fixed-bad-W alternating phase constraint.

No switch-gauge interpretation or probability is asserted here.
-/

namespace Hypertournaments

/-- For every genuine selected p3 parent, one actual increasing
vertex enumeration identifies ALL raw facets with their true
unlabelled canonical finite-set signs, at the exact deletion
indices required for the alternating packet argument. -/
theorem Hyper.p3ActualSelectedParent_has_raw_facet_dictionary
    (k t : ℕ) (ht : 0 < t)
    (E : Hyper (4*k+3) (Fin (((4*k+2)*t)+2)))
    (q : p3SelectedTrials (ZMod t) (4*k+1)) :
    ∃ f : Fin (4*k+4) ↪o Fin (((4*k+2)*t)+2),
      tupleVertices f.toEmbedding =
        p3ActualSelectedParentSet k t ht q ∧
      (∀ i : Fin (4*k+2),
        E.orient (facet f.toEmbedding (i.castSucc.castSucc)) =
          E.canonicalSignTable
            (p3ActualSelectedMixedSet k t ht q i)) ∧
      E.orient (facet f.toEmbedding
        ((Fin.last (4*k+2)).castSucc)) =
        E.canonicalSignTable
          (insert (Fin.last ((4*k+2)*t+1))
            ((p3CoordinateTransversal (4*k+2) t ht q.1).image
              ((onePointBaseEmbedding ((4*k+2)*t)).trans
                (leftJointInclusion ((4*k+2)*t))))) ∧
      E.orient (facet f.toEmbedding
        (Fin.last ((4*k+2)+1))) =
        E.canonicalSignTable
          (insert ((Fin.last ((4*k+2)*t)).castSucc)
            ((p3CoordinateTransversal (4*k+2) t ht q.1).image
              ((onePointBaseEmbedding ((4*k+2)*t)).trans
                (leftJointInclusion ((4*k+2)*t))))) := by
  classical
  obtain ⟨f,hParent,hOld,hLeft,hRight⟩ :=
    p3ActualSelectedParent_increasing_tuple k t ht q
  refine ⟨f,hParent,?_,?_,?_⟩
  · intro i
    calc
      E.orient (facet f.toEmbedding (i.castSucc.castSucc)) =
          E.canonicalSignTable
            ((tupleVertices f.toEmbedding).erase
              (f (i.castSucc.castSucc))) :=
        E.orderedFacet_orient_eq_canonical_erase
          f (i.castSucc.castSucc)
      _ = E.canonicalSignTable
          (p3ActualSelectedMixedSet k t ht q i) := by
        rw [hParent,hOld i,p3ActualSelectedParent_erase_old_vertex]
  · calc
      E.orient (facet f.toEmbedding
          ((Fin.last (4*k+2)).castSucc)) =
        E.canonicalSignTable
          ((tupleVertices f.toEmbedding).erase
            (f ((Fin.last (4*k+2)).castSucc))) :=
        E.orderedFacet_orient_eq_canonical_erase
          f ((Fin.last (4*k+2)).castSucc)
      _ = E.canonicalSignTable
          (insert (Fin.last ((4*k+2)*t+1))
            ((p3CoordinateTransversal (4*k+2) t ht q.1).image
              ((onePointBaseEmbedding ((4*k+2)*t)).trans
                (leftJointInclusion ((4*k+2)*t))))) := by
        rw [hParent,hLeft,p3ActualSelectedParent_erase_left]
  · calc
      E.orient (facet f.toEmbedding (Fin.last ((4*k+2)+1))) =
        E.canonicalSignTable
          ((tupleVertices f.toEmbedding).erase
            (f (Fin.last ((4*k+2)+1)))) :=
        E.orderedFacet_orient_eq_canonical_erase
          f (Fin.last ((4*k+2)+1))
      _ = E.canonicalSignTable
          (insert ((Fin.last ((4*k+2)*t)).castSucc)
            ((p3CoordinateTransversal (4*k+2) t ht q.1).image
              ((onePointBaseEmbedding ((4*k+2)*t)).trans
                (leftJointInclusion ((4*k+2)*t))))) := by
        rw [hParent,hRight,p3ActualSelectedParent_erase_right]

end Hypertournaments
