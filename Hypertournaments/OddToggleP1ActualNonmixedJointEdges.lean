import Hypertournaments.OddToggleP1JointSideOmissionLocalIndex
import Hypertournaments.OddToggleP1NeighborCanonicalPair
import Hypertournaments.OddToggleP1NonhomogeneousRows
import Hypertournaments.OddToggleP1RightProtectedActualZero

/-!
# Exactly the nonmixed edges needed in the exceptional p1 obstruction

The genuine homogeneous-neighbor relation in a hypothetical canonical
joint reads the local type of the actual one-point side on the
complementary packet. The protected right packet omitting a4 is
homogeneous and creates the fixed edge (a4,left-new). Every left
old-omission packet is nonhomogeneous, so no old vertex is adjacent
to right-new. The right packet omitting a2 is also nonhomogeneous,
so (a2,left-new) is absent.

All statements are intrinsic, in the actual joint, without a
strong-amalgamation assumption or an added linear order.
-/

namespace Hypertournaments

/-- The left-new edge at old v is homogeneous precisely when the
right one-point packet omitting v is homogeneous. -/
theorem p1JointOld_leftNew_neighbor_iff_rightZero
    (k : ℕ) (v : Fin (4*k+6))
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hER : Preserves (p1SideHyper k false) E
      (rightJointInclusion (4*k+6))) :
    p1JointLeftNew k ∈ p1JointHomogeneousNeighbors k E
      (p1JointOld k v) ↔
    localIndex (p1SideHyper k false)
      ((p1SidePacketOmitOld k v).orderEmbOfFin
        (p1SidePacketOmitOld_card k v)).toEmbedding = 0 := by
  have hneq : p1JointOld k v ≠ p1JointLeftNew k :=
    ne_of_lt (p1JointOld_lt_left k v)
  have hnb := p1JointNeighbor_mem_iff_canonical_zero k E
    (p1JointOld k v) (p1JointLeftNew k) hneq
  have hloc := p1JointRightOmission_localIndex k v E hER
  constructor
  · intro h
    have hh := hnb.mp h
    have hz :
      localIndex E
        (((Finset.univ : Finset (Fin (4*k+6+2))).erase
          (p1JointOld k v)).erase (p1JointLeftNew k)).orderEmbOfFin
          (by
            rw [← p1RightSideOmission_image_joint k v]
            rw [Finset.card_image_of_injective _
              (p1RightJointOrderEmb k).injective]
            exact p1SidePacketOmitOld_card k v)).toEmbedding = 0 := by
      simpa only [p1JointDoubleDeletion] using hh
    exact hloc.symm.trans hz
  · intro hz
    apply hnb.mpr
    have hh := hloc.trans hz
    simpa only [p1JointDoubleDeletion] using hh

/-- The right-new edge at old v is homogeneous precisely when
the left one-point packet omitting v is homogeneous. -/
theorem p1JointOld_rightNew_neighbor_iff_leftZero
    (k : ℕ) (v : Fin (4*k+6))
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hEL : Preserves (p1SideHyper k true) E
      (leftJointInclusion (4*k+6))) :
    p1JointRightNew k ∈ p1JointHomogeneousNeighbors k E
      (p1JointOld k v) ↔
    localIndex (p1SideHyper k true)
      ((p1SidePacketOmitOld k v).orderEmbOfFin
        (p1SidePacketOmitOld_card k v)).toEmbedding = 0 := by
  have hneq : p1JointOld k v ≠ p1JointRightNew k :=
    ne_of_lt (lt_trans (p1JointOld_lt_left k v)
      (p1JointLeft_lt_right k))
  have hnb := p1JointNeighbor_mem_iff_canonical_zero k E
    (p1JointOld k v) (p1JointRightNew k) hneq
  have hloc := p1JointLeftOmission_localIndex k v E hEL
  constructor
  · intro h
    have hh := hnb.mp h
    have hz :
      localIndex E
        (((Finset.univ : Finset (Fin (4*k+6+2))).erase
          (p1JointOld k v)).erase (p1JointRightNew k)).orderEmbOfFin
          (by
            rw [← p1LeftSideOmission_image_joint k v]
            rw [Finset.card_image_of_injective _
              (Fin.castSuccOrderEmb :
                Fin (4*k+6+1) ↪o Fin (4*k+6+2)).injective]
            exact p1SidePacketOmitOld_card k v)).toEmbedding = 0 := by
      simpa only [p1JointDoubleDeletion] using hh
    exact hloc.symm.trans hz
  · intro hz
    apply hnb.mpr
    have hh := hloc.trans hz
    simpa only [p1JointDoubleDeletion] using hh

/-- In every potential joint the core vertex a4 has its fixed
homogeneous edge to left-new, and neither a4 nor a2 is adjacent
to right-new; a2 is not adjacent to left-new either. -/
theorem p1JointCore_fixed_and_excluded_new_edges (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hEL : Preserves (p1SideHyper k true) E
      (leftJointInclusion (4*k+6)))
    (hER : Preserves (p1SideHyper k false) E
      (rightJointInclusion (4*k+6))) :
    (p1JointLeftNew k ∈ p1JointHomogeneousNeighbors k E
       (p1JointOld k (p1CoreAt k (4 : Fin 6)))) ∧
    (p1JointRightNew k ∉ p1JointHomogeneousNeighbors k E
       (p1JointOld k (p1CoreAt k (4 : Fin 6)))) ∧
    (p1JointLeftNew k ∉ p1JointHomogeneousNeighbors k E
       (p1JointOld k (p1CoreAt k (2 : Fin 6)))) ∧
    (p1JointRightNew k ∉ p1JointHomogeneousNeighbors k E
       (p1JointOld k (p1CoreAt k (2 : Fin 6)))) := by
  have hsource (v : Fin (4*k+6)) :
      tupleVertices
        ((p1SidePacketOmitOld k v).orderEmbOfFin
          (p1SidePacketOmitOld_card k v)).toEmbedding =
      p1SidePacketOmitOld k v := by
    simpa [tupleVertices] using
      (Finset.image_orderEmbOfFin_univ
        (p1SidePacketOmitOld k v) (p1SidePacketOmitOld_card k v))
  have h20 : p1CoreAt k (2 : Fin 6) ≠ p1CoreAt k (0 : Fin 6) := by
    intro h
    have hh := (p1CoreAt_injective k) h
    exact (by decide : (2 : Fin 6) ≠ 0) hh
  have h24 : p1CoreAt k (2 : Fin 6) ≠ p1CoreAt k (4 : Fin 6) := by
    intro h
    have hh := (p1CoreAt_injective k) h
    exact (by decide : (2 : Fin 6) ≠ 4) hh
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (p1JointOld_leftNew_neighbor_iff_rightZero k
      (p1CoreAt k (4 : Fin 6)) E hER).mpr
    exact p1RightCoreFour_packet_localIndex k
      (p1SidePacketOmitOld_card k (p1CoreAt k (4 : Fin 6)))
  · intro h
    have hz := (p1JointOld_rightNew_neighbor_iff_leftZero k
      (p1CoreAt k (4 : Fin 6)) E hEL).mp h
    exact (p1LeftSide_omission_nonhomogeneous k
      (p1CoreAt k (4 : Fin 6))
      ((p1SidePacketOmitOld k (p1CoreAt k (4 : Fin 6))).orderEmbOfFin
        (p1SidePacketOmitOld_card k (p1CoreAt k (4 : Fin 6))))
      (hsource _)) hz
  · intro h
    have hz := (p1JointOld_leftNew_neighbor_iff_rightZero k
      (p1CoreAt k (2 : Fin 6)) E hER).mp h
    exact (p1RightSide_omission_unprotected_nonhomogeneous k
      (p1CoreAt k (2 : Fin 6)) h20 h24
      ((p1SidePacketOmitOld k (p1CoreAt k (2 : Fin 6))).orderEmbOfFin
        (p1SidePacketOmitOld_card k (p1CoreAt k (2 : Fin 6))))
      (hsource _)) hz
  · intro h
    have hz := (p1JointOld_rightNew_neighbor_iff_leftZero k
      (p1CoreAt k (2 : Fin 6)) E hEL).mp h
    exact (p1LeftSide_omission_nonhomogeneous k
      (p1CoreAt k (2 : Fin 6))
      ((p1SidePacketOmitOld k (p1CoreAt k (2 : Fin 6))).orderEmbOfFin
        (p1SidePacketOmitOld_card k (p1CoreAt k (2 : Fin 6))))
      (hsource _)) hz

end Hypertournaments
