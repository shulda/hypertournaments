import Hypertournaments.OddToggleP1ActualJointSymmetry
import Hypertournaments.IncreasingTupleUniqueness

/-!
# A genuine p1 homogeneous-neighbor edge is a zero-type double deletion

For any two distinct vertices x and y of the canonical two-point
joint, the unordered (n+1)-set obtained by deleting both has a unique
increasing enumeration. This is exactly the oriented local packet
counted by the zero-or-two neighbor set at x when y is deleted.
This lemma keeps actual `localIndex` and both order embeddings,
rather than postulating an abstract symmetric graph.
-/

namespace Hypertournaments

def p1JointDoubleDeletion (k : ℕ)
    (x y : Fin (4*k+6+2)) : Finset (Fin (4*k+6+2)) :=
  ((Finset.univ : Finset (Fin (4*k+6+2))).erase x).erase y

theorem p1JointDoubleDeletion_card (k : ℕ)
    (x y : Fin (4*k+6+2)) (hxy : x ≠ y) :
    (p1JointDoubleDeletion k x y).card = 4*k+6 := by
  have hfirst := Finset.card_erase_add_one
    (Finset.mem_univ x :
      x ∈ (Finset.univ : Finset (Fin (4*k+6+2))))
  have hymem : y ∈
      (Finset.univ : Finset (Fin (4*k+6+2))).erase x :=
    Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ _⟩
  have hsecond := Finset.card_erase_add_one hymem
  simp only [Finset.card_univ, Fintype.card_fin] at hfirst
  change ((Finset.univ : Finset (Fin (4*k+6+2))).erase x).card + 1 =
    4*k+6+2 at hfirst
  change (((Finset.univ : Finset (Fin (4*k+6+2))).erase x).erase y).card + 1 =
    ((Finset.univ : Finset (Fin (4*k+6+2))).erase x).card at hsecond
  change (((Finset.univ : Finset (Fin (4*k+6+2))).erase x).erase y).card = 4*k+6
  omega

/-- An actual homogeneous-neighbor edge is equivalent to the
zero local index on the increasing double-deletion packet. -/
theorem p1JointNeighbor_mem_iff_canonical_zero
    (k : ℕ) (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (x y : Fin (4*k+6+2)) (hxy : x ≠ y) :
    y ∈ p1JointHomogeneousNeighbors k E x ↔
      localIndex E
        ((p1JointDoubleDeletion k x y).orderEmbOfFin
          (p1JointDoubleDeletion_card k x y hxy)).toEmbedding = 0 := by
  let Q : Finset (Fin (4*k+6+2)) := p1JointDoubleDeletion k x y
  let hQ : Q.card = 4*k+6 := p1JointDoubleDeletion_card k x y hxy
  let fx : Fin (4*k+7) ↪o Fin (4*k+6+2) :=
    p1JointParentOrderEmb k x
  have hordered (i : Fin (4*k+7)) (hiy : fx i = y) :
      p1OrderedFacet fx i = Q.orderEmbOfFin hQ := by
    apply increasingEmb_eq_of_tupleVertices
    have hs : tupleVertices (p1OrderedFacet fx i).toEmbedding = Q := by
      rw [p1OrderedFacet_toEmbedding]
      simpa only [Q, p1JointDoubleDeletion, fx, hiy] using
        (p1JointParentFacet_vertexSet k x i)
    have ho : tupleVertices (Q.orderEmbOfFin hQ).toEmbedding = Q := by
      simpa [tupleVertices] using
        (Finset.image_orderEmbOfFin_univ Q hQ)
    exact hs.trans ho.symm
  have hlocal (i : Fin (4*k+7)) (hiy : fx i = y) :
      localIndex E (facet fx.toEmbedding i) =
        localIndex E (Q.orderEmbOfFin hQ).toEmbedding := by
    have hh := hordered i hiy
    have hemb := p1OrderedFacet_toEmbedding fx i
    have htype := congrArg
      (fun g : Fin (4*k+6) ↪o Fin (4*k+6+2) =>
        localIndex E g.toEmbedding) hh
    rw [hemb] at htype
    exact htype
  constructor
  · intro hy
    obtain ⟨i, hi, hiy⟩ :=
      (p1JointHomogeneousNeighbors_mem_iff k E x y).mp hy
    exact (hlocal i hiy).symm.trans hi
  · intro hzero
    have hmem : y ∈ p1JointParentPacket k x :=
      Finset.mem_erase.mpr ⟨hxy.symm, Finset.mem_univ _⟩
    have himage :
        y ∈ (Finset.univ : Finset (Fin (4*k+7))).image fx := by
      change y ∈ (Finset.univ : Finset (Fin (4*k+7))).image
        ((p1JointParentPacket k x).orderEmbOfFin
          (p1JointParentPacket_card k x))
      rw [Finset.image_orderEmbOfFin_univ]
      exact hmem
    obtain ⟨i, _, hiy⟩ := Finset.mem_image.mp himage
    apply (p1JointHomogeneousNeighbors_mem_iff k E x y).mpr
    exact ⟨i, (hlocal i hiy).trans hzero, hiy⟩

end Hypertournaments
