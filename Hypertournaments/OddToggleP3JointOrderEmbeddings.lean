import Mathlib.Tactic.Ext
import Hypertournaments.OnePointJoint
import Hypertournaments.OddToggleP3LiftedSideBaseAgreement

/-!
# Exact order-preserving canonical one-point inclusions into the p3 joint

The ordinary AP canonical joint has the old a vertices first,
left fresh at a, right fresh at a+1. Both one-point side
embeddings are strictly increasing, and they agree exactly
on every old vertex. Their actual images of any old finite
subset coincide, including the ambient orientation-sign order.

This is the side-link diagram needed to apply the certified
lifted-potential and all-genuine-joints mixed-gauge lemmas
without silently substituting the auxiliary order l<A<r.
No admissibility or AP assertion is made here.
-/

namespace Hypertournaments

/-- The right canonical one-point inclusion, skipping the
left fresh point, is an ORDER embedding (not just an injection). -/
def p3RightJointOrderEmb (a : ℕ) :
    Fin (a+1) ↪o Fin (a+2) :=
  OrderEmbedding.ofStrictMono
    (fun x : Fin (a+1) => rightJointInclusion a x)
    (by
      change StrictMono
        (fun x : Fin (a+1) =>
          ((Fin.last a).castSucc : Fin (a+2)).succAbove x)
      exact Fin.strictMono_succAbove ((Fin.last a).castSucc))

/-- The order-preserving right inclusion represents exactly
the original canonical rightJointInclusion embedding. -/
theorem p3RightJointOrderEmb_toEmbedding (a : ℕ) :
    (p3RightJointOrderEmb a).toEmbedding =
      rightJointInclusion a := by
  ext i
  rfl

/-- A canonical old base vertex lands in the same two-step
successor under either the left or the right side inclusion. -/
theorem p3CanonicalJoint_old_coincidence
    (a : ℕ) (v : Fin a) :
    (p3RightJointOrderEmb a)
        ((onePointBaseEmbedding a) v) =
      (Fin.castSuccOrderEmb :
        Fin (a+1) ↪o Fin (a+2))
        ((onePointBaseEmbedding a) v) := by
  change rightJointInclusion a v.castSucc = v.castSucc.castSucc
  exact rightJointInclusion_old a v

/-- The actual old finite-set image under the two
order-preserving side embeddings is literally identical. -/
theorem p3CanonicalJoint_old_set_images_agree
    (a : ℕ) (Q : Finset (Fin a)) :
    (Q.image (onePointBaseEmbedding a)).image
        (Fin.castSuccOrderEmb :
          Fin (a+1) ↪o Fin (a+2)).toEmbedding =
    (Q.image (onePointBaseEmbedding a)).image
        (p3RightJointOrderEmb a).toEmbedding := by
  classical
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  calc
    (Q.image (onePointBaseEmbedding a)).image
        (Fin.castSuccOrderEmb :
          Fin (a+1) ↪o Fin (a+2)).toEmbedding =
      Q.image old := by
        exact p3Finset_image_commutes
          (onePointBaseEmbedding a)
          (Fin.castSuccOrderEmb :
            Fin (a+1) ↪o Fin (a+2)).toEmbedding
          old (by intro v; rfl) Q
    _ = (Q.image (onePointBaseEmbedding a)).image
        (p3RightJointOrderEmb a).toEmbedding := by
      symm
      exact p3Finset_image_commutes
        (onePointBaseEmbedding a)
        (p3RightJointOrderEmb a).toEmbedding
        old (by
          intro v
          exact p3CanonicalJoint_old_coincidence a v) Q

end Hypertournaments
