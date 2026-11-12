import Hypertournaments.OnePointJoint

/-!
# Canonical ordinary-AP union geometry for the p3 one-point span

Both p3 one-point sides have the old vertices 0,...,a-1 followed
by their distinct new last point. In the canonical joint Fin(a+2),
the left fresh point is a and the right fresh point is a+1.
The two original old-base embeddings agree pointwise in the joint,
and both fresh vertices are disjoint from all old ones.

These are purely vertex-theoretic lemmas, requiring neither order
nor orientation assumptions. They discharge the exact fresh-point
and old-image agreement hypotheses of the all-actual-joints p3
mixed gauge theorem, and are compatible with the existing ordinary
AP factorization and nonidentification infrastructure.
-/

namespace Hypertournaments

/-- The old base as a genuine injective subset of the canonical
joint with two distinct fresh vertices. -/
def p3CanonicalJointOld (a : ℕ) : Fin a ↪ Fin (a+2) :=
  (onePointBaseEmbedding a).trans (leftJointInclusion a)

/-- The first new point of the canonical ordinary AP joint. -/
def p3CanonicalJointLeft (a : ℕ) : Fin (a+2) :=
  leftJointInclusion a (Fin.last a)

/-- The second new point of the canonical ordinary AP joint. -/
def p3CanonicalJointRight (a : ℕ) : Fin (a+2) :=
  rightJointInclusion a (Fin.last a)

/-- Both sides share exactly the same old-base inclusion in the
canonical joint, without any appeal to a chosen potential. -/
theorem p3CanonicalJoint_old_commutes (a : ℕ) :
    (onePointBaseEmbedding a).trans (leftJointInclusion a) =
    (onePointBaseEmbedding a).trans (rightJointInclusion a) := by
  ext v
  change ((leftJointInclusion a) v.castSucc).val =
    ((rightJointInclusion a) v.castSucc).val
  rw [rightJointInclusion_old]
  rfl

/-- The two true new points of the canonical joint are distinct. -/
theorem p3CanonicalJoint_fresh_distinct (a : ℕ) :
    p3CanonicalJointLeft a ≠ p3CanonicalJointRight a := by
  change (leftJointInclusion a (Fin.last a)) ≠
    rightJointInclusion a (Fin.last a)
  rw [rightJointInclusion_new]
  exact Fin.castSucc_ne_last (Fin.last a)

/-- No old base vertex can equal either new endpoint in the
canonical joint. This is exactly the hFresh premise of the
genuine all-joints mixed parity and gauge theorems. -/
theorem p3CanonicalJoint_fresh_disjoint (a : ℕ) :
    ∀ v : Fin a,
      p3CanonicalJointOld a v ≠ p3CanonicalJointLeft a ∧
      p3CanonicalJointOld a v ≠ p3CanonicalJointRight a := by
  intro v
  constructor
  · intro h
    have hsource : v.castSucc = Fin.last a :=
      (leftJointInclusion a).injective h
    exact Fin.castSucc_ne_last v hsource
  · intro h
    change (leftJointInclusion a v.castSucc) =
      (rightJointInclusion a (Fin.last a)) at h
    rw [rightJointInclusion_new] at h
    exact Fin.castSucc_ne_last v.castSucc h

end Hypertournaments
