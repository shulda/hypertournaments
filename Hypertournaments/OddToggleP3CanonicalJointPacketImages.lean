import Hypertournaments.OddToggleP3JointOrderEmbeddings
import Hypertournaments.OddToggleP3CanonicalSides

/-!
# Actual canonical side packet image, with its new endpoint

In the ordinary-AP p3 joint the old base lies first, then
the left new point at a, then the right new point at a+1.
An order-preserving injection of a canonical side takes the
old-plus-new set to precisely the old image plus the image
of its new point. These are literal Finset identities,
not merely isomorphisms of hyperturnaments.

Both endpoint cases are provided: the left new point becomes
a.castSucc, the right new point becomes Fin.last(a+1).
This is the missing exact set-image interface for transporting
intrinsic canonical side coboundaries into arbitrary joints.
-/

namespace Hypertournaments

/-- The canonical side packet, consisting of one new point
and a genuine m-element old subset, has exactly m+1 vertices. -/
theorem p3CanonicalSide_oldPlusNew_card
    (a m : ℕ) (Q : Finset (Fin a)) (hQ : Q.card = m) :
    (insert (Fin.last a)
      (Q.image (onePointBaseEmbedding a))).card = m+1 := by
  classical
  have hn : Fin.last a ∉ Q.image (onePointBaseEmbedding a) := by
    intro hmem
    obtain ⟨v,_,heq⟩ := Finset.mem_image.mp hmem
    exact Fin.castSucc_ne_last v heq
  rw [Finset.card_insert_of_not_mem hn]
  rw [Finset.card_image_of_injective _ (onePointBaseEmbedding a).injective]
  omega

/-- A genuine increasing embedding of a canonical one-fresh
side maps the packet literally onto the old joint image plus
the new endpoint. Requires only commuting old-coordinate maps. -/
theorem p3CanonicalSide_packet_image
    (a : ℕ)
    (g : Fin (a+1) ↪o Fin (a+2))
    (oldJoint : Fin a ↪ Fin (a+2))
    (freshJoint : Fin (a+2))
    (hnew : g (Fin.last a) = freshJoint)
    (hold : ∀ v : Fin a,
      g ((onePointBaseEmbedding a) v) = oldJoint v)
    (Q : Finset (Fin a)) :
    (insert (Fin.last a) (Q.image (onePointBaseEmbedding a))).image
      g.toEmbedding =
      insert freshJoint (Q.image oldJoint) := by
  classical
  rw [Finset.image_insert]
  have himage := p3Finset_image_commutes
    (onePointBaseEmbedding a) g.toEmbedding oldJoint hold Q
  rw [hnew]
  exact congrArg (insert freshJoint) himage

/-- Actual left one-point image: the left endpoint l lies
immediately after the a old vertices in the joint. -/
theorem p3CanonicalJoint_left_packet_image
    (a : ℕ) (Q : Finset (Fin a)) :
    (insert (Fin.last a) (Q.image (onePointBaseEmbedding a))).image
      (Fin.castSuccOrderEmb :
        Fin (a+1) ↪o Fin (a+2)).toEmbedding =
    insert ((Fin.last a).castSucc)
      (Q.image
        ((onePointBaseEmbedding a).trans (leftJointInclusion a))) := by
  apply p3CanonicalSide_packet_image a
    (Fin.castSuccOrderEmb :
      Fin (a+1) ↪o Fin (a+2))
    ((onePointBaseEmbedding a).trans (leftJointInclusion a))
    ((Fin.last a).castSucc)
  · rfl
  · intro v
    rfl

/-- Actual right one-point image: the right endpoint r is
the last vertex in the joint, while the old base is identical. -/
theorem p3CanonicalJoint_right_packet_image
    (a : ℕ) (Q : Finset (Fin a)) :
    (insert (Fin.last a) (Q.image (onePointBaseEmbedding a))).image
      (p3RightJointOrderEmb a).toEmbedding =
    insert (Fin.last (a+1))
      (Q.image
        ((onePointBaseEmbedding a).trans (leftJointInclusion a))) := by
  apply p3CanonicalSide_packet_image a
    (p3RightJointOrderEmb a)
    ((onePointBaseEmbedding a).trans (leftJointInclusion a))
    (Fin.last (a+1))
  · exact rightJointInclusion_new a
  · intro v
    exact p3CanonicalJoint_old_coincidence a v

end Hypertournaments
