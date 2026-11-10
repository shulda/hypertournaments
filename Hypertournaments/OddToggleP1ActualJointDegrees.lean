import Hypertournaments.OddToggleP1ActualZeroTwo
import Hypertournaments.CanonicalPacket

/-!
# Actual zero-or-two homogeneous-neighbor degrees in a p1 joint

For arity n=4k+5 a canonical joint of two one-point extensions has
n+3=4k+8 vertices. Removing any vertex x leaves an (n+2)-packet,
and the already certified intrinsic zero-or-two theorem says that
the number of homogeneous (n+1)-deletions of that packet is exactly
zero or two. The neighbor set below is genuinely the image of
these actual deleted-facet positions, with no abstract Boolean
graph assumptions.
-/

namespace Hypertournaments

/-- The full canonical two-point joint with a given vertex erased. -/
def p1JointParentPacket (k : ℕ)
    (x : Fin (4*k+6+2)) : Finset (Fin (4*k+6+2)) :=
  Finset.univ.erase x

theorem p1JointParentPacket_card (k : ℕ)
    (x : Fin (4*k+6+2)) :
    (p1JointParentPacket k x).card = 4*k+7 := by
  have h := Finset.card_erase_add_one
    (Finset.mem_univ x : x ∈ (Finset.univ : Finset (Fin (4*k+6+2))))
  change ((Finset.univ : Finset (Fin (4*k+6+2))).erase x).card + 1 =
    4*k+6+2 at h
  exact (by change ((Finset.univ : Finset (Fin (4*k+6+2))).erase x).card =
    4*k+7; omega)

/-- The unique increasing enumeration of the parent with x erased. -/
def p1JointParentOrderEmb (k : ℕ) (x : Fin (4*k+6+2)) :
    Fin (4*k+7) ↪o Fin (4*k+6+2) :=
  (p1JointParentPacket k x).orderEmbOfFin (p1JointParentPacket_card k x)

/-- All y which arise as homogeneous deletions of the true parent
packet obtained from the full joint by erasing x. -/
def p1JointHomogeneousNeighbors (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (x : Fin (4*k+6+2)) : Finset (Fin (4*k+6+2)) :=
  (Finset.univ.filter (fun i : Fin (4*k+7) =>
    localIndex E (facet (p1JointParentOrderEmb k x).toEmbedding i) = 0)).image
      (p1JointParentOrderEmb k x)

/-- The actual homogeneous-neighbor set at every joint vertex has
cardinality zero or two whenever the whole joint is admissible. -/
theorem p1JointHomogeneousNeighbors_zero_or_two (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hE : Admissible (toggleZero (switchingAllowed (4*k+5))) E)
    (x : Fin (4*k+6+2)) :
    (p1JointHomogeneousNeighbors k E x).card = 0 ∨
      (p1JointHomogeneousNeighbors k E x).card = 2 := by
  have hzero := E.p1Toggle_actual_zero_or_two
    k (4*k+6+2) hE (p1JointParentOrderEmb k x)
  unfold p1JointHomogeneousNeighbors
  rw [Finset.card_image_of_injective _
    (p1JointParentOrderEmb k x).injective]
  exact hzero

/-- Each neighbor is a genuine facet index of the increasing
(n+2)-packet, and conversely. -/
theorem p1JointHomogeneousNeighbors_mem_iff (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (x y : Fin (4*k+6+2)) :
    y ∈ p1JointHomogeneousNeighbors k E x ↔
      ∃ i : Fin (4*k+7),
        localIndex E (facet (p1JointParentOrderEmb k x).toEmbedding i) = 0 ∧
          p1JointParentOrderEmb k x i = y := by
  constructor
  · intro hy
    obtain ⟨i, hi, hiy⟩ := Finset.mem_image.mp hy
    exact ⟨i, (Finset.mem_filter.mp hi).2, hiy⟩
  · rintro ⟨i, hi, rfl⟩
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩, rfl⟩

/-- A joint neighbor is never the erased parent vertex itself. -/
theorem p1JointHomogeneousNeighbors_ne_self (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (x y : Fin (4*k+6+2))
    (hy : y ∈ p1JointHomogeneousNeighbors k E x) : y ≠ x := by
  obtain ⟨i, _, rfl⟩ :=
    (p1JointHomogeneousNeighbors_mem_iff k E x y).mp hy
  have hrange :
      (p1JointParentOrderEmb k x) i ∈ p1JointParentPacket k x := by
    have himage :=
      Finset.image_orderEmbOfFin_univ
        (p1JointParentPacket k x) (p1JointParentPacket_card k x)
    rw [← himage]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  exact (Finset.mem_erase.mp hrange).1

/-- Exact set of vertices of an intrinsic homogeneous deletion from
the parent: full joint minus x and the chosen neighbor. -/
theorem p1JointParentFacet_vertexSet (k : ℕ)
    (x : Fin (4*k+6+2)) (i : Fin (4*k+7)) :
    tupleVertices (facet (p1JointParentOrderEmb k x).toEmbedding i) =
      ((Finset.univ : Finset (Fin (4*k+6+2))).erase x).erase
        (p1JointParentOrderEmb k x i) := by
  have hparent :
      tupleVertices (p1JointParentOrderEmb k x).toEmbedding =
        p1JointParentPacket k x := by
    simpa [tupleVertices, p1JointParentOrderEmb] using
      (Finset.image_orderEmbOfFin_univ
        (p1JointParentPacket k x) (p1JointParentPacket_card k x))
  rw [tupleVertices_facet_eq_erase, hparent]
  rfl

end Hypertournaments
