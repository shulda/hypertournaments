import Hypertournaments.OddToggleP3CanonicalJointMixedGauge
import Hypertournaments.OddToggleP3ActualSideLinkSource

/-!
# Exact canonical p3 lifted side contractions on actual old subsets

The all-genuine-joints mixed gauge is written using two ambient
lifted side potentials contracted at the left/right fresh vertices.
Here we evaluate each such contraction on an actual old finite
subset and prove it equals exactly the eligible punctured
coefficient of the original side potential.

The general auxiliary lemma uses only injection-image naturality;
no synthetic ambient completion, order convention or probabilistic
premise is introduced. Both left and right use the actual canonical
joint inclusions from OnePointJoint.
-/

namespace Hypertournaments

/-- The contraction of a finite potential lifted along an
injective vertex map, at the image of a fresh point outside U,
recovers exactly the original potential on insert fresh U. -/
theorem p3LiftFinPotential_contractAt_image
    {a b : ℕ} (g : Fin a ↪ Fin b)
    (fresh : Fin a) (z : Finset (Fin a) → ZMod 2)
    (U : Finset (Fin a)) (hfresh : fresh ∉ U) :
    contractAt (g fresh) (p3LiftFinPotential g z) (U.image g) =
      z (insert fresh U) := by
  classical
  have hnot : g fresh ∉ U.image g := by
    intro hmem
    obtain ⟨v, hv, heq⟩ := Finset.mem_image.mp hmem
    have hvfresh : v = fresh := g.injective heq
    exact hfresh (hvfresh ▸ hv)
  change (if g fresh ∈ U.image g then 0 else
    p3LiftFinPotential g z (insert (g fresh) (U.image g))) =
      z (insert fresh U)
  rw [if_neg hnot]
  simpa only [Finset.image_insert] using
    (p3LiftFinPotential_image g z (insert fresh U))

/-- The real canonical LEFT lifted potential, contracted at the
left fresh vertex, reads the genuine eligible left-side link
coefficient on each old U. -/
theorem p3CanonicalLeftLift_contractAt_old
    (m t : ℕ) (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (U : Finset (Fin (m*t))) :
    contractAt ((Fin.last (m*t)).castSucc)
      (p3LiftFinPotential (leftJointInclusion (m*t))
        (p3SidePotential m t (onePointBaseEmbedding (m*t))
          (Fin.last (m*t)) eligible W L))
      (U.image ((onePointBaseEmbedding (m*t)).trans
        (leftJointInclusion (m*t)))) =
    if p3IsEligibleMissingTransversal m t eligible U
    then L U else 0 := by
  classical
  let a := m*t
  let old : Fin a ↪ Fin (a+1) := onePointBaseEmbedding a
  let fresh : Fin (a+1) := Fin.last a
  let g : Fin (a+1) ↪ Fin (a+2) := leftJointInclusion a
  let z : Finset (Fin (a+1)) → ZMod 2 :=
    p3SidePotential m t old fresh eligible W L
  have hfresh : fresh ∉ U.image old := by
    intro hh
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hh
    exact Fin.castSucc_ne_last v hv
  have hLift := p3LiftFinPotential_contractAt_image
    g fresh z (U.image old) hfresh
  have himage :
      (U.image old).image g = U.image (old.trans g) :=
    p3Finset_image_commutes old g (old.trans g)
      (by intro v; rfl) U
  rw [himage] at hLift
  have hvalue := p3CanonicalSidePotential_fresh_old_image
    m t eligible W L U
  change contractAt (g fresh) (p3LiftFinPotential g z)
    (U.image (old.trans g)) =
      if p3IsEligibleMissingTransversal m t eligible U
      then L U else 0
  exact hLift.trans hvalue

/-- The real canonical RIGHT lifted potential, contracted at the
right fresh vertex, reads its genuine eligible right-side link
coefficient on each old U. The right inclusion skips the left
fresh vertex but fixes all old vertices. -/
theorem p3CanonicalRightLift_contractAt_old
    (m t : ℕ) (eligible : Finset (Fin m))
    (W R : Finset (Fin (m*t)) → ZMod 2)
    (U : Finset (Fin (m*t))) :
    contractAt (Fin.last (m*t+1))
      (p3LiftFinPotential (rightJointInclusion (m*t))
        (p3SidePotential m t (onePointBaseEmbedding (m*t))
          (Fin.last (m*t)) eligible W R))
      (U.image ((onePointBaseEmbedding (m*t)).trans
        (leftJointInclusion (m*t)))) =
    if p3IsEligibleMissingTransversal m t eligible U
    then R U else 0 := by
  classical
  let a := m*t
  let old : Fin a ↪ Fin (a+1) := onePointBaseEmbedding a
  let fresh : Fin (a+1) := Fin.last a
  let g : Fin (a+1) ↪ Fin (a+2) := rightJointInclusion a
  let jointOld : Fin a ↪ Fin (a+2) :=
    old.trans (leftJointInclusion a)
  let z : Finset (Fin (a+1)) → ZMod 2 :=
    p3SidePotential m t old fresh eligible W R
  have hfresh : fresh ∉ U.image old := by
    intro hh
    obtain ⟨v, _, hv⟩ := Finset.mem_image.mp hh
    exact Fin.castSucc_ne_last v hv
  have hLift := p3LiftFinPotential_contractAt_image
    g fresh z (U.image old) hfresh
  have himage :
      (U.image old).image g = U.image jointOld :=
    p3Finset_image_commutes old g jointOld
      (by intro v; exact rightJointInclusion_old a v) U
  rw [himage] at hLift
  have hvalue := p3CanonicalSidePotential_fresh_old_image
    m t eligible W R U
  have hresult :
      contractAt (g fresh) (p3LiftFinPotential g z)
        (U.image jointOld) =
      if p3IsEligibleMissingTransversal m t eligible U
      then R U else 0 := hLift.trans hvalue
  simpa only [g, rightJointInclusion_new] using hresult

end Hypertournaments
