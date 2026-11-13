import Hypertournaments.OddToggleP3ActualParentPacketFacets

/-!
# Both genuine selected parent endpoint facets in canonical joint order

The actual selected parent packet contains its old full transversal
and the two canonical new vertices, with every old vertex smaller
than both new vertices. Erasing the right fresh point gives the
literal left one-point endpoint set, and erasing the left fresh
point gives the literal right one-point endpoint set.

Together with the old-facet erasure theorem, this gives a
complete facet-set dictionary for the actual selected parent.
Only the index/order transport to the raw Fin(n+1) facet word
remains separate.
-/

namespace Hypertournaments

open scoped Classical

/-- Erasing the RIGHT fresh point leaves precisely the old full
transversal together with the canonical LEFT fresh vertex. -/
theorem p3ActualSelectedParent_erase_right
    (k t : ℕ) (ht : 0 < t)
    (q : p3SelectedTrials (ZMod t) (4*k+1)) :
    (p3ActualSelectedParentSet k t ht q).erase
      (Fin.last ((4*k+2)*t+1)) =
    insert ((Fin.last ((4*k+2)*t)).castSucc)
      ((p3CoordinateTransversal (4*k+2) t ht q.1).image
        ((onePointBaseEmbedding ((4*k+2)*t)).trans
          (leftJointInclusion ((4*k+2)*t)))) := by
  classical
  let m : ℕ := 4*k+2
  let a : ℕ := m*t
  let Q : Finset (Fin a) := p3CoordinateTransversal m t ht q.1
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  let l : Fin (a+2) := (Fin.last a).castSucc
  let r : Fin (a+2) := Fin.last (a+1)
  have hlr : l ≠ r := Fin.castSucc_ne_last (Fin.last a)
  have hr : r ∉ Q.image old := by
    intro hmem
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hmem
    change v.castSucc.castSucc = Fin.last (a+1) at hv
    exact Fin.castSucc_ne_last (v.castSucc) hv
  change (insert l (insert r (Q.image old))).erase r =
    insert l (Q.image old)
  rw [Finset.erase_insert_of_ne hlr]
  simp [hr]

/-- Erasing the LEFT fresh point leaves precisely the old full
transversal together with the canonical RIGHT fresh vertex. -/
theorem p3ActualSelectedParent_erase_left
    (k t : ℕ) (ht : 0 < t)
    (q : p3SelectedTrials (ZMod t) (4*k+1)) :
    (p3ActualSelectedParentSet k t ht q).erase
      ((Fin.last ((4*k+2)*t)).castSucc) =
    insert (Fin.last ((4*k+2)*t+1))
      ((p3CoordinateTransversal (4*k+2) t ht q.1).image
        ((onePointBaseEmbedding ((4*k+2)*t)).trans
          (leftJointInclusion ((4*k+2)*t)))) := by
  classical
  let m : ℕ := 4*k+2
  let a : ℕ := m*t
  let Q : Finset (Fin a) := p3CoordinateTransversal m t ht q.1
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  let l : Fin (a+2) := (Fin.last a).castSucc
  let r : Fin (a+2) := Fin.last (a+1)
  have hr : l ≠ r := Fin.castSucc_ne_last (Fin.last a)
  have hlold : l ∉ Q.image old := by
    intro hmem
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hmem
    change v.castSucc.castSucc = (Fin.last a).castSucc at hv
    have heq : v.castSucc = Fin.last a :=
      (Fin.castSuccEmb : Fin (a+1) ↪ Fin (a+2)).injective hv
    exact Fin.castSucc_ne_last v heq
  have hl : l ∉ insert r (Q.image old) := by
    simp only [Finset.mem_insert,not_or]
    exact ⟨hr,hlold⟩
  change (insert l (insert r (Q.image old))).erase l =
    insert r (Q.image old)
  simp [hl]

end Hypertournaments
