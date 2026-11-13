import Hypertournaments.OddToggleP3CanonicalJointPacketImages
import Hypertournaments.OddToggleP3JointOrderEmbeddings
import Hypertournaments.OddToggleP3CanonicalSides

/-!
# The actual Boolean endpoint signs in every preserved canonical p3 joint

The complete generic mixed-gauge theorem works at the F₂ level,
but the final forbidden homogeneous packet has raw Boolean
facet signs. On every old m-set Q the actual canonical sign on
Q plus the left or right fresh joint vertex is exactly the
corresponding one-point side's own canonical sign, because both
side inclusions are order-preserving and preserve the true
intrinsic orientation.

This does not select any ambient completion. Both identities
hold for EVERY actual joint preserving the corresponding side.
-/

namespace Hypertournaments

/-- An actual joint preserving the canonical LEFT one-point side
has exactly the left side's canonical Boolean sign on the old
full m-set plus its actual LEFT fresh vertex. -/
theorem p3CanonicalJoint_left_endpointBool_of_preserves
    (m t : ℕ) (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (E : Hyper (m+1) (Fin (m*t+2)))
    (hL : Preserves (p3CanonicalSide m t eligible W L) E
      (leftJointInclusion (m*t)))
    (Q : Finset (Fin (m*t))) :
    E.canonicalSignTable
      (insert ((Fin.last (m*t)).castSucc)
        (Q.image ((onePointBaseEmbedding (m*t)).trans
          (leftJointInclusion (m*t))))) =
    (p3CanonicalSide m t eligible W L).canonicalSignTable
      (insert (Fin.last (m*t))
        (Q.image (onePointBaseEmbedding (m*t)))) := by
  let a := m*t
  let SQ : Finset (Fin (a+1)) :=
    insert (Fin.last a) (Q.image (onePointBaseEmbedding a))
  have hPres : Preserves (p3CanonicalSide m t eligible W L) E
      (Fin.castSuccOrderEmb : Fin (a+1) ↪o Fin (a+2)).toEmbedding := hL
  have hSign := Hyper.canonicalSignTable_image_orderEmbedding
    (p3CanonicalSide m t eligible W L) E
    (Fin.castSuccOrderEmb : Fin (a+1) ↪o Fin (a+2))
    hPres SQ
  have hImage :
      (insert (Fin.last a) (Q.image (onePointBaseEmbedding a))).image
        (Fin.castSuccOrderEmb : Fin (a+1) ↪o Fin (a+2)) =
      insert ((Fin.last a).castSucc)
        (Q.image ((onePointBaseEmbedding a).trans
          (leftJointInclusion a))) :=
    p3CanonicalJoint_left_packet_image a Q
  dsimp only [SQ] at hSign
  rw [hImage] at hSign
  exact hSign

/-- An actual joint preserving the canonical RIGHT one-point side
has exactly the right side's canonical Boolean sign on the old
full m-set plus its actual RIGHT fresh vertex. -/
theorem p3CanonicalJoint_right_endpointBool_of_preserves
    (m t : ℕ) (eligible : Finset (Fin m))
    (W R : Finset (Fin (m*t)) → ZMod 2)
    (E : Hyper (m+1) (Fin (m*t+2)))
    (hR : Preserves (p3CanonicalSide m t eligible W R) E
      (rightJointInclusion (m*t)))
    (Q : Finset (Fin (m*t))) :
    E.canonicalSignTable
      (insert (Fin.last (m*t+1))
        (Q.image ((onePointBaseEmbedding (m*t)).trans
          (leftJointInclusion (m*t))))) =
    (p3CanonicalSide m t eligible W R).canonicalSignTable
      (insert (Fin.last (m*t))
        (Q.image (onePointBaseEmbedding (m*t)))) := by
  let a := m*t
  let SQ : Finset (Fin (a+1)) :=
    insert (Fin.last a) (Q.image (onePointBaseEmbedding a))
  have hPres : Preserves (p3CanonicalSide m t eligible W R) E
      (p3RightJointOrderEmb a).toEmbedding := by
    rw [p3RightJointOrderEmb_toEmbedding]
    exact hR
  have hSign := Hyper.canonicalSignTable_image_orderEmbedding
    (p3CanonicalSide m t eligible W R) E
    (p3RightJointOrderEmb a) hPres SQ
  have hImage :
      (insert (Fin.last a) (Q.image (onePointBaseEmbedding a))).image
        (p3RightJointOrderEmb a) =
      insert (Fin.last (a+1))
        (Q.image ((onePointBaseEmbedding a).trans
          (leftJointInclusion a))) :=
    p3CanonicalJoint_right_packet_image a Q
  dsimp only [SQ] at hSign
  rw [hImage] at hSign
  exact hSign

end Hypertournaments
