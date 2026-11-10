import Hypertournaments.LocalIndexCanonicalImage
import Hypertournaments.OddToggleP1JointEndpointSigns
import Hypertournaments.OddToggleP1OmissionFacets

/-!
# Intrinsic local types of true p1 one-point packets inside a canonical joint

Deleting the left new vertex and any old vertex v from a canonical
joint produces the image of the right one-point side packet omitting
v. The left side is analogous with the right new vertex deleted.
The exact equality of finite images plus the canonical image local
index lemma identifies their genuine local indices, without
assuming an ambient order is in the hypertournament language.
-/

namespace Hypertournaments

/-- The right-side old-omission (n+1)-packet maps exactly to the
joint with the left new vertex and the omitted old point erased. -/
theorem p1RightSideOmission_image_joint
    (k : ℕ) (v : Fin (4*k+6)) :
    (p1SidePacketOmitOld k v).image (p1RightJointOrderEmb k) =
      ((Finset.univ : Finset (Fin (4*k+6+2))).erase
        (p1JointOld k v)).erase (p1JointLeftNew k) := by
  have hfirst := p1ImageErase
    (rightJointInclusion (4*k+6))
    (Finset.univ : Finset (Fin (4*k+6+1))) v.castSucc
  calc
    (p1SidePacketOmitOld k v).image (p1RightJointOrderEmb k) =
        ((Finset.univ : Finset (Fin (4*k+6+1))).erase v.castSucc).image
          (rightJointInclusion (4*k+6)) := by
      rfl
    _ = ((Finset.univ : Finset (Fin (4*k+6+1))).image
          (rightJointInclusion (4*k+6))).erase
          (rightJointInclusion (4*k+6) v.castSucc) := hfirst
    _ = ((Finset.univ : Finset (Fin (4*k+6+2))).erase
          (p1JointLeftNew k)).erase (p1JointOld k v) := by
      rw [p1RightJoint_image_univ, p1JointOld_right_inclusion]
    _ = ((Finset.univ : Finset (Fin (4*k+6+2))).erase
          (p1JointOld k v)).erase (p1JointLeftNew k) := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      tauto

/-- The left-side old-omission packet maps to the joint with
the right new vertex and the omitted old vertex erased. -/
theorem p1LeftSideOmission_image_joint
    (k : ℕ) (v : Fin (4*k+6)) :
    (p1SidePacketOmitOld k v).image
      (Fin.castSuccOrderEmb : Fin (4*k+6+1) ↪o Fin (4*k+6+2)) =
      ((Finset.univ : Finset (Fin (4*k+6+2))).erase
        (p1JointOld k v)).erase (p1JointRightNew k) := by
  have hfirst := p1ImageErase
    (leftJointInclusion (4*k+6))
    (Finset.univ : Finset (Fin (4*k+6+1))) v.castSucc
  calc
    (p1SidePacketOmitOld k v).image
        (Fin.castSuccOrderEmb : Fin (4*k+6+1) ↪o Fin (4*k+6+2)) =
        ((Finset.univ : Finset (Fin (4*k+6+1))).erase v.castSucc).image
          (leftJointInclusion (4*k+6)) := by
      rfl
    _ = ((Finset.univ : Finset (Fin (4*k+6+1))).image
          (leftJointInclusion (4*k+6))).erase
          (leftJointInclusion (4*k+6) v.castSucc) := hfirst
    _ = ((Finset.univ : Finset (Fin (4*k+6+2))).erase
          (p1JointRightNew k)).erase (p1JointOld k v) := by
      rw [p1LeftJoint_image_univ, p1JointOld_left_inclusion]
    _ = ((Finset.univ : Finset (Fin (4*k+6+2))).erase
          (p1JointOld k v)).erase (p1JointRightNew k) := by
      ext t
      simp only [Finset.mem_erase, Finset.mem_univ, and_true]
      tauto

/-- Exact genuine local-index transfer from the right one-point
side into its corresponding nonmixed joint packet. -/
theorem p1JointRightOmission_localIndex
    (k : ℕ) (v : Fin (4*k+6))
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hER : Preserves (p1SideHyper k false) E
       (rightJointInclusion (4*k+6))) :
    localIndex E
      ((((Finset.univ : Finset (Fin (4*k+6+2))).erase
        (p1JointOld k v)).erase (p1JointLeftNew k)).orderEmbOfFin
        (by
          rw [← p1RightSideOmission_image_joint k v]
          rw [Finset.card_image_of_injective _
            (p1RightJointOrderEmb k).injective]
          exact p1SidePacketOmitOld_card k v)).toEmbedding =
      localIndex (p1SideHyper k false)
        ((p1SidePacketOmitOld k v).orderEmbOfFin
          (p1SidePacketOmitOld_card k v)).toEmbedding := by
  have he : Preserves (p1SideHyper k false) E
      (p1RightJointOrderEmb k).toEmbedding := by
    rw [p1RightJointOrderEmb_toEmbedding]
    exact hER
  have hloc := localIndex_image_orderEmb_preserves
    (p1SideHyper k false) E (p1RightJointOrderEmb k) he
    (p1SidePacketOmitOld k v) (p1SidePacketOmitOld_card k v)
  simpa only [p1RightSideOmission_image_joint k v] using hloc

/-- Exact genuine local-index transfer from the left one-point
side into its corresponding nonmixed joint packet. -/
theorem p1JointLeftOmission_localIndex
    (k : ℕ) (v : Fin (4*k+6))
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hEL : Preserves (p1SideHyper k true) E
       (leftJointInclusion (4*k+6))) :
    localIndex E
      ((((Finset.univ : Finset (Fin (4*k+6+2))).erase
        (p1JointOld k v)).erase (p1JointRightNew k)).orderEmbOfFin
        (by
          rw [← p1LeftSideOmission_image_joint k v]
          rw [Finset.card_image_of_injective _
            (Fin.castSuccOrderEmb :
              Fin (4*k+6+1) ↪o Fin (4*k+6+2)).injective]
          exact p1SidePacketOmitOld_card k v)).toEmbedding =
      localIndex (p1SideHyper k true)
        ((p1SidePacketOmitOld k v).orderEmbOfFin
          (p1SidePacketOmitOld_card k v)).toEmbedding := by
  have he : Preserves (p1SideHyper k true) E
      (Fin.castSuccOrderEmb :
        Fin (4*k+6+1) ↪o Fin (4*k+6+2)).toEmbedding := by
    change Preserves (p1SideHyper k true) E
      (leftJointInclusion (4*k+6))
    exact hEL
  have hloc := localIndex_image_orderEmb_preserves
    (p1SideHyper k true) E
    (Fin.castSuccOrderEmb : Fin (4*k+6+1) ↪o Fin (4*k+6+2)) he
    (p1SidePacketOmitOld k v) (p1SidePacketOmitOld_card k v)
  simpa only [p1LeftSideOmission_image_joint k v] using hloc

end Hypertournaments
