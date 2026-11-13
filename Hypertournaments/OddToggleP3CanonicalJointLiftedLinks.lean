import Hypertournaments.OddToggleP3CanonicalJointPacketImages
import Hypertournaments.OddToggleP3LiftedSideLinks

/-!
# True canonical joint side-link orientations equal lifted cochain boundaries

In the ordinary-AP joint Fin(mt+2) there are two order-preserving
embeddings of the canonical Fin(mt+1) sides: left via castSucc,
right via succAbove the new-left point. They agree exactly on
the actual old base.

On any actual m-element old subset Q, the two endpoint (m+1)-sets
have the exact image identities established in
OddToggleP3CanonicalJointPacketImages. A joint preserving the side
has true canonical sign on that endpoint equal to the coboundary
of its actual side potential, lifted by the side inclusion.
No preferred joint completion or synthetic orientation is chosen.

The final universal mixed gauge theorem can now accept both
endpoint-link equalities from genuine Preserves hypotheses.
-/

namespace Hypertournaments

/-- The genuine left endpoint's canonical F₂ sign is the
coboundary of its lifted left side potential on the *actual*
old-plus-left packet, under preservation of that side. -/
theorem p3CanonicalJoint_left_link_via_lift
    (m t : ℕ)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (E : Hyper (m+1) (Fin (m*t+2)))
    (hL : Preserves (p3CanonicalSide m t eligible W L) E
      (leftJointInclusion (m*t)))
    (Q : Finset (Fin (m*t))) (hQ : Q.card = m) :
    p1BitToZMod (E.canonicalSignTable
      (insert ((Fin.last (m*t)).castSucc)
        (Q.image ((onePointBaseEmbedding (m*t)).trans
          (leftJointInclusion (m*t)))))) =
    coboundary
      (p3LiftFinPotential (leftJointInclusion (m*t))
        (p3SidePotential m t
          (onePointBaseEmbedding (m*t)) (Fin.last (m*t))
          eligible W L))
      (insert ((Fin.last (m*t)).castSucc)
        (Q.image ((onePointBaseEmbedding (m*t)).trans
          (leftJointInclusion (m*t))))) := by
  let A := m*t
  let SQ : Finset (Fin (A+1)) :=
    insert (Fin.last A) (Q.image (onePointBaseEmbedding A))
  have hSQ : SQ.card = m+1 :=
    p3CanonicalSide_oldPlusNew_card A m Q hQ
  have hPres : Preserves
      (p3SideHyper m t (onePointBaseEmbedding A)
        (Fin.last A) eligible W L) E
      (Fin.castSuccOrderEmb : Fin (A+1) ↪o Fin (A+2)).toEmbedding := by
    exact hL
  have hLink :=
    p3SideHyper_jointCanonicalViaLift
      m t (A+1) (A+2)
      (onePointBaseEmbedding A) (Fin.last A)
      eligible W L E
      (Fin.castSuccOrderEmb : Fin (A+1) ↪o Fin (A+2))
      hPres SQ hSQ
  have hImage := p3CanonicalJoint_left_packet_image A Q
  dsimp only [SQ] at hLink
  rw [hImage] at hLink
  exact hLink

/-- The genuine right endpoint's canonical F₂ sign is the
coboundary of its lifted right side potential on the *actual*
old-plus-right packet, under preservation of that side. -/
theorem p3CanonicalJoint_right_link_via_lift
    (m t : ℕ)
    (eligible : Finset (Fin m))
    (W R : Finset (Fin (m*t)) → ZMod 2)
    (E : Hyper (m+1) (Fin (m*t+2)))
    (hR : Preserves (p3CanonicalSide m t eligible W R) E
      (rightJointInclusion (m*t)))
    (Q : Finset (Fin (m*t))) (hQ : Q.card = m) :
    p1BitToZMod (E.canonicalSignTable
      (insert (Fin.last (m*t+1))
        (Q.image ((onePointBaseEmbedding (m*t)).trans
          (leftJointInclusion (m*t)))))) =
    coboundary
      (p3LiftFinPotential (rightJointInclusion (m*t))
        (p3SidePotential m t
          (onePointBaseEmbedding (m*t)) (Fin.last (m*t))
          eligible W R))
      (insert (Fin.last (m*t+1))
        (Q.image ((onePointBaseEmbedding (m*t)).trans
          (leftJointInclusion (m*t))))) := by
  let A := m*t
  let SQ : Finset (Fin (A+1)) :=
    insert (Fin.last A) (Q.image (onePointBaseEmbedding A))
  have hSQ : SQ.card = m+1 :=
    p3CanonicalSide_oldPlusNew_card A m Q hQ
  have hPres : Preserves
      (p3SideHyper m t (onePointBaseEmbedding A)
        (Fin.last A) eligible W R) E
      (p3RightJointOrderEmb A).toEmbedding := by
    rw [p3RightJointOrderEmb_toEmbedding]
    exact hR
  have hLink :=
    p3SideHyper_jointCanonicalViaLift
      m t (A+1) (A+2)
      (onePointBaseEmbedding A) (Fin.last A)
      eligible W R E
      (p3RightJointOrderEmb A) hPres SQ hSQ
  have hImage := p3CanonicalJoint_right_packet_image A Q
  dsimp only [SQ] at hLink
  rw [hImage] at hLink
  exact hLink

end Hypertournaments
