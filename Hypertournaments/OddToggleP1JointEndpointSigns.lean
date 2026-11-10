import Hypertournaments.OddToggleP1JointFacetImages
import Hypertournaments.OddToggleP1TwoOldCanonicalSign
import Hypertournaments.CanonicalSignTableNaturality

/-!
# Actual endpoint canonical signs in hypothetical p1 mixed joints

The actual right/left side embeddings preserve orientations into
any canonical two-point joint. The previous exact finite-set image
geometry and canonical-sign naturality therefore force the two
canonical n-facet signs at the endpoints of every mixed joint packet
to equal the prescribed right/left canonical link bits.

This makes no homogeneity or AP assumption. It is the key bridge from
the source tables to genuine facets inside a hypothetical amalgam.
-/

namespace Hypertournaments

/-- The right joint inclusion is strictly increasing; package it
as an order embedding for canonical sign-table naturality. -/
def p1RightJointOrderEmb (k : ℕ) :
    Fin (4*k+6+1) ↪o Fin (4*k+6+2) :=
  OrderEmbedding.ofStrictMono (rightJointInclusion (4*k+6))
    (Fin.strictMono_succAbove ((Fin.last (4*k+6)).castSucc))

theorem p1RightJointOrderEmb_toEmbedding (k : ℕ) :
    (p1RightJointOrderEmb k).toEmbedding =
      rightJointInclusion (4*k+6) := by
  ext i
  rfl

/-- A mixed n-facet deleting the left new vertex reads exactly
the actual right side link bit. -/
theorem p1JointMixed_right_canonicalSign
    (k : ℕ) (v w : Fin (4*k+6)) (hvne : v ≠ w)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hER : Preserves (p1SideHyper k false) E
      (rightJointInclusion (4*k+6))) :
    E.canonicalSignTable
      ((p1JointMixedPacket k v w).erase (p1JointLeftNew k)) =
        p1CanonicalLink k false v w := by
  let S : Finset (Fin (4*k+6+1)) :=
    (p1SidePacketOmitOld k v).erase w.castSucc
  have hER' : Preserves (p1SideHyper k false) E
      (p1RightJointOrderEmb k).toEmbedding := by
    rw [p1RightJointOrderEmb_toEmbedding]
    exact hER
  have himage :
      S.image (p1RightJointOrderEmb k) =
        (p1JointMixedPacket k v w).erase (p1JointLeftNew k) := by
    calc
      S.image (p1RightJointOrderEmb k) =
          S.image (rightJointInclusion (4*k+6)) := by
        rfl
      _ = (p1JointMixedPacket k v w).erase (p1JointLeftNew k) :=
        p1JointMixed_rightFacet_image k v w
  calc
    E.canonicalSignTable
        ((p1JointMixedPacket k v w).erase (p1JointLeftNew k)) =
      E.canonicalSignTable (S.image (p1RightJointOrderEmb k)) := by
        rw [himage]
    _ = (p1SideHyper k false).canonicalSignTable S :=
      E.canonicalSignTable_image_orderEmbedding
        (p1SideHyper k false) E (p1RightJointOrderEmb k) hER' S
    _ = p1CanonicalLink k false v w :=
      p1SideHyper_canonicalSignTable_two_old k false v w hvne

/-- The other mixed endpoint n-facet, deleting the right new
vertex, reads exactly the actual left side link bit. -/
theorem p1JointMixed_left_canonicalSign
    (k : ℕ) (v w : Fin (4*k+6)) (hvne : v ≠ w)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hEL : Preserves (p1SideHyper k true) E
      (leftJointInclusion (4*k+6))) :
    E.canonicalSignTable
      ((p1JointMixedPacket k v w).erase (p1JointRightNew k)) =
        p1CanonicalLink k true v w := by
  let S : Finset (Fin (4*k+6+1)) :=
    (p1SidePacketOmitOld k v).erase w.castSucc
  have hemb :
      (Fin.castSuccOrderEmb : Fin (4*k+6+1) ↪o Fin (4*k+6+2)).toEmbedding =
        leftJointInclusion (4*k+6) := by
    ext i
    rfl
  have hEL' : Preserves (p1SideHyper k true) E
      (Fin.castSuccOrderEmb : Fin (4*k+6+1) ↪o Fin (4*k+6+2)).toEmbedding := by
    rw [hemb]
    exact hEL
  have himage :
      S.image (Fin.castSuccOrderEmb : Fin (4*k+6+1) ↪o Fin (4*k+6+2)) =
        (p1JointMixedPacket k v w).erase (p1JointRightNew k) := by
    calc
      S.image (Fin.castSuccOrderEmb : Fin (4*k+6+1) ↪o Fin (4*k+6+2)) =
          S.image (leftJointInclusion (4*k+6)) := by
        rfl
      _ = (p1JointMixedPacket k v w).erase (p1JointRightNew k) :=
        p1JointMixed_leftFacet_image k v w
  calc
    E.canonicalSignTable
        ((p1JointMixedPacket k v w).erase (p1JointRightNew k)) =
      E.canonicalSignTable
        (S.image (Fin.castSuccOrderEmb :
          Fin (4*k+6+1) ↪o Fin (4*k+6+2))) := by
        rw [himage]
    _ = (p1SideHyper k true).canonicalSignTable S :=
      E.canonicalSignTable_image_orderEmbedding
        (p1SideHyper k true) E
        (Fin.castSuccOrderEmb : Fin (4*k+6+1) ↪o Fin (4*k+6+2))
        hEL' S
    _ = p1CanonicalLink k true v w :=
      p1SideHyper_canonicalSignTable_two_old k true v w hvne

end Hypertournaments
