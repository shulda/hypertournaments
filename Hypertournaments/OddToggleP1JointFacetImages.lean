import Hypertournaments.OddToggleP1MixedPacketOrder
import Hypertournaments.OddToggleP1ActualPhase
import Hypertournaments.OddToggleP1OmissionFacets

/-!
# Actual side facets inside a canonical p1 mixed joint packet

With both new vertices retained, a mixed packet is the full joint
minus exactly two old vertices v,w. Deleting the right new vertex
gives precisely the left-side n-facet missing old v,w, while
deleting the left new vertex gives the right-side n-facet missing
those same vertices. These are equalities of finite sets and image
maps, not statements about external hyperorientations.
-/

namespace Hypertournaments

/-- The canonical right inclusion has image all joint vertices
except the left new one. -/
theorem p1RightJoint_image_univ (k : ℕ) :
    ((Finset.univ : Finset (Fin (4*k+6+1))).image
       (rightJointInclusion (4*k+6))) =
    (Finset.univ : Finset (Fin (4*k+6+2))).erase
       (p1JointLeftNew k) := by
  have hsub :
      ((Finset.univ : Finset (Fin (4*k+6+1))).image
        (rightJointInclusion (4*k+6))) ⊆
        (Finset.univ : Finset (Fin (4*k+6+2))).erase
          (p1JointLeftNew k) := by
    intro x hx
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hx
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have hbad : rightJointInclusion (4*k+6) y =
          p1JointLeftNew k := hy.trans he
      change (Fin.last (4*k+6)).castSucc.succAbove y =
          (Fin.last (4*k+6)).castSucc at hbad
      exact (Fin.succAbove_ne _ _) hbad
    · exact Finset.mem_univ _
  have hcimage :
      ((Finset.univ : Finset (Fin (4*k+6+1))).image
        (rightJointInclusion (4*k+6))).card = 4*k+6+1 := by
    rw [Finset.card_image_of_injective _
      (rightJointInclusion (4*k+6)).injective]
    simp
  have hcerase :
      ((Finset.univ : Finset (Fin (4*k+6+2))).erase
        (p1JointLeftNew k)).card = 4*k+6+1 := by
    have h := Finset.card_erase_add_one
      (Finset.mem_univ (p1JointLeftNew k) :
        p1JointLeftNew k ∈
          (Finset.univ : Finset (Fin (4*k+6+2))))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hcimage, hcerase]

/-- The canonical left inclusion has image all joint vertices
except the right new one. -/
theorem p1LeftJoint_image_univ (k : ℕ) :
    ((Finset.univ : Finset (Fin (4*k+6+1))).image
       (leftJointInclusion (4*k+6))) =
    (Finset.univ : Finset (Fin (4*k+6+2))).erase
       (p1JointRightNew k) := by
  have hsub :
      ((Finset.univ : Finset (Fin (4*k+6+1))).image
        (leftJointInclusion (4*k+6))) ⊆
        (Finset.univ : Finset (Fin (4*k+6+2))).erase
          (p1JointRightNew k) := by
    intro x hx
    obtain ⟨y, _, hy⟩ := Finset.mem_image.mp hx
    apply Finset.mem_erase.mpr
    constructor
    · intro he
      have hbad : leftJointInclusion (4*k+6) y =
          p1JointRightNew k := hy.trans he
      change y.castSucc = Fin.last (4*k+6+1) at hbad
      exact Fin.castSucc_ne_last y hbad
    · exact Finset.mem_univ _
  have hcimage :
      ((Finset.univ : Finset (Fin (4*k+6+1))).image
        (leftJointInclusion (4*k+6))).card = 4*k+6+1 := by
    rw [Finset.card_image_of_injective _
      (leftJointInclusion (4*k+6)).injective]
    simp
  have hcerase :
      ((Finset.univ : Finset (Fin (4*k+6+2))).erase
        (p1JointRightNew k)).card = 4*k+6+1 := by
    have h := Finset.card_erase_add_one
      (Finset.mem_univ (p1JointRightNew k) :
        p1JointRightNew k ∈
          (Finset.univ : Finset (Fin (4*k+6+2))))
    simp only [Finset.card_univ, Fintype.card_fin] at h
    omega
  apply Finset.eq_of_subset_of_card_le hsub
  rw [hcimage, hcerase]

/-- The right-side n-facet obtained by omitting old v,w maps to
the mixed joint packet with the left new endpoint erased. -/
theorem p1JointMixed_rightFacet_image (k : ℕ)
    (v w : Fin (4*k+6)) :
    (((p1SidePacketOmitOld k v).erase w.castSucc).image
       (rightJointInclusion (4*k+6))) =
      (p1JointMixedPacket k v w).erase (p1JointLeftNew k) := by
  have hfirst := p1ImageErase
    (rightJointInclusion (4*k+6))
    (Finset.univ : Finset (Fin (4*k+6+1))) v.castSucc
  have hsecond := p1ImageErase
    (rightJointInclusion (4*k+6))
    ((Finset.univ : Finset (Fin (4*k+6+1))).erase v.castSucc)
    w.castSucc
  calc
    (((p1SidePacketOmitOld k v).erase w.castSucc).image
       (rightJointInclusion (4*k+6))) =
      (((Finset.univ : Finset (Fin (4*k+6+1))).erase
        v.castSucc).image (rightJointInclusion (4*k+6))).erase
          (rightJointInclusion (4*k+6) w.castSucc) := hsecond
    _ = ((((Finset.univ : Finset (Fin (4*k+6+1))).image
        (rightJointInclusion (4*k+6))).erase
          (rightJointInclusion (4*k+6) v.castSucc)).erase
          (rightJointInclusion (4*k+6) w.castSucc)) := by rw [hfirst]
    _ = (((Finset.univ : Finset (Fin (4*k+6+2))).erase
          (p1JointLeftNew k)).erase (p1JointOld k v)).erase
          (p1JointOld k w) := by
      rw [p1RightJoint_image_univ,
        p1JointOld_right_inclusion, p1JointOld_right_inclusion]
    _ = (p1JointMixedPacket k v w).erase
          (p1JointLeftNew k) := by
      ext x
      simp only [p1JointMixedPacket, Finset.mem_erase,
        Finset.mem_univ, and_true]
      tauto

/-- The corresponding left-side n-facet maps to the mixed joint
packet with the right new endpoint erased. -/
theorem p1JointMixed_leftFacet_image (k : ℕ)
    (v w : Fin (4*k+6)) :
    (((p1SidePacketOmitOld k v).erase w.castSucc).image
       (leftJointInclusion (4*k+6))) =
      (p1JointMixedPacket k v w).erase (p1JointRightNew k) := by
  have hfirst := p1ImageErase
    (leftJointInclusion (4*k+6))
    (Finset.univ : Finset (Fin (4*k+6+1))) v.castSucc
  have hsecond := p1ImageErase
    (leftJointInclusion (4*k+6))
    ((Finset.univ : Finset (Fin (4*k+6+1))).erase v.castSucc)
    w.castSucc
  calc
    (((p1SidePacketOmitOld k v).erase w.castSucc).image
       (leftJointInclusion (4*k+6))) =
      (((Finset.univ : Finset (Fin (4*k+6+1))).erase
        v.castSucc).image (leftJointInclusion (4*k+6))).erase
          (leftJointInclusion (4*k+6) w.castSucc) := hsecond
    _ = ((((Finset.univ : Finset (Fin (4*k+6+1))).image
        (leftJointInclusion (4*k+6))).erase
          (leftJointInclusion (4*k+6) v.castSucc)).erase
          (leftJointInclusion (4*k+6) w.castSucc)) := by rw [hfirst]
    _ = (((Finset.univ : Finset (Fin (4*k+6+2))).erase
          (p1JointRightNew k)).erase (p1JointOld k v)).erase
          (p1JointOld k w) := by
      rw [p1LeftJoint_image_univ,
        p1JointOld_left_inclusion, p1JointOld_left_inclusion]
    _ = (p1JointMixedPacket k v w).erase
          (p1JointRightNew k) := by
      ext x
      simp only [p1JointMixedPacket, Finset.mem_erase,
        Finset.mem_univ, and_true]
      tauto

end Hypertournaments
