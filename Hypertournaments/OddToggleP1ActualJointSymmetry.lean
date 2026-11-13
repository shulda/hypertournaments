import Mathlib.Tactic.Ext
import Mathlib.Tactic.Tauto
import Hypertournaments.OddToggleP1ActualJointDegrees
import Hypertournaments.IncreasingTupleUniqueness

/-!
# Symmetry of the actual homogeneous double-erasure relation

In an arbitrary intrinsic hypertournament, the local index of
the increasing packet remaining after deleting distinct vertices
x and y is independent of the deletion order. The certification
uses exact equality of underlying double-erasure finite subsets,
rather than arbitrary tuple permutations or a synthetic signed
graph. Consequently the actual p1 zero-or-two neighbor relation
on a canonical joint is symmetric.
-/

namespace Hypertournaments

theorem p1JointHomogeneousNeighbors_symmetric (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (x y : Fin (4*k+6+2))
    (hy : y ∈ p1JointHomogeneousNeighbors k E x) :
    x ∈ p1JointHomogeneousNeighbors k E y := by
  obtain ⟨i, hi, hiy⟩ :=
    (p1JointHomogeneousNeighbors_mem_iff k E x y).mp hy
  have hne : y ≠ x :=
    p1JointHomogeneousNeighbors_ne_self k E x y hy
  let fx : Fin (4*k+7) ↪o Fin (4*k+6+2) :=
    p1JointParentOrderEmb k x
  let fy : Fin (4*k+7) ↪o Fin (4*k+6+2) :=
    p1JointParentOrderEmb k y
  have hxParent : x ∈ p1JointParentPacket k y := by
    exact Finset.mem_erase.mpr ⟨hne.symm, Finset.mem_univ _⟩
  have hxImage : x ∈ (Finset.univ : Finset (Fin (4*k+7))).image fy := by
    change x ∈ (Finset.univ : Finset (Fin (4*k+7))).image
      ((p1JointParentPacket k y).orderEmbOfFin (p1JointParentPacket_card k y))
    rw [Finset.image_orderEmbOfFin_univ]
    exact hxParent
  obtain ⟨j, _, hjx⟩ := Finset.mem_image.mp hxImage
  have hsets :
      tupleVertices (p1OrderedFacet fx i).toEmbedding =
        tupleVertices (p1OrderedFacet fy j).toEmbedding := by
    calc
      tupleVertices (p1OrderedFacet fx i).toEmbedding =
          ((Finset.univ : Finset (Fin (4*k+6+2))).erase x).erase (fx i) := by
            rw [p1OrderedFacet_toEmbedding]
            exact p1JointParentFacet_vertexSet k x i
      _ = ((Finset.univ : Finset (Fin (4*k+6+2))).erase x).erase y := by
        rw [hiy]
      _ = ((Finset.univ : Finset (Fin (4*k+6+2))).erase y).erase x := by
        ext z
        simp only [Finset.mem_erase, Finset.mem_univ, and_true]
        tauto
      _ = ((Finset.univ : Finset (Fin (4*k+6+2))).erase y).erase (fy j) := by
        rw [hjx]
      _ = tupleVertices (p1OrderedFacet fy j).toEmbedding := by
        rw [p1OrderedFacet_toEmbedding]
        exact (p1JointParentFacet_vertexSet k y j).symm
  have hordered :
      p1OrderedFacet fx i = p1OrderedFacet fy j :=
    increasingEmb_eq_of_tupleVertices (p1OrderedFacet fx i)
      (p1OrderedFacet fy j) hsets
  have hyzero :
      localIndex E (facet fy.toEmbedding j) = 0 := by
    have hxzero : localIndex E (p1OrderedFacet fx i).toEmbedding = 0 := by
      rw [p1OrderedFacet_toEmbedding]
      exact hi
    rw [hordered] at hxzero
    rw [p1OrderedFacet_toEmbedding] at hxzero
    exact hxzero
  exact (p1JointHomogeneousNeighbors_mem_iff k E y x).mpr
    ⟨j, hyzero, hjx⟩

end Hypertournaments
