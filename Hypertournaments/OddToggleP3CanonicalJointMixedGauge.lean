import Hypertournaments.OddToggleP3CanonicalJointLiftedLinks
import Hypertournaments.OddToggleP3JointPotentialLinks
import Hypertournaments.OddToggleP3LiftedSideBaseAgreement

/-!
# Every genuine preserved canonical p3 joint satisfies the FULL mixed gauge

Fix the actual canonical old base of a=(4k+2)t vertices and its
one-point left/right sides. The old vertices precede both fresh
points, which are a and a+1 in the canonical joint.

Assume a genuine intrinsic switching-admissible joint E preserves
BOTH canonical one-point sides under the actual left/right inclusion
embeddings. Their link signs on every actual old-plus-new (4k+3)-set
are exactly the cochain boundaries of their ambient lifted side
potentials; this is the certified link-transport theorem.
The two lifts agree on every image of an old-only subset.

Thus all hypotheses of the existing full arbitrary-joint p3
mixed gauge theorem are discharged directly from Preserves.
No chosen completion or preferred orientation is used. The remaining
non-AP task is to identify source-variable evaluations in the gauge
normal form on all selected zero-sum transversals.
-/

namespace Hypertournaments

/-- Every actual switching joint preserving both canonical p3
one-point sides has its full mixed orientation cochain equal
to the sum of their contracted lifted potentials plus delta u. -/
theorem Hyper.p3CanonicalPreservedJoint_has_mixed_gauge
    (k t : ℕ) (root : Fin ((4*k+2)*t))
    (E : Hyper (4*k+3) (Fin ((4*k+2)*t+2)))
    (hE : Admissible (switchingAllowed (4*k+3)) E)
    (eligibleL eligibleR : Finset (Fin (4*k+2)))
    (W L R : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (hL : Preserves
      (p3CanonicalSide (4*k+2) t eligibleL W L)
      E (leftJointInclusion ((4*k+2)*t)))
    (hR : Preserves
      (p3CanonicalSide (4*k+2) t eligibleR W R)
      E (rightJointInclusion ((4*k+2)*t))) :
    ∃ u : Finset (Fin ((4*k+2)*t)) → ZMod 2,
      ∀ U : Finset (Fin ((4*k+2)*t)), U.card=4*k+1 →
      let a := (4*k+2)*t
      let old : Fin a ↪ Fin (a+2) :=
        (onePointBaseEmbedding a).trans (leftJointInclusion a)
      let leftNew : Fin (a+2) := (Fin.last a).castSucc
      let rightNew : Fin (a+2) := Fin.last (a+1)
      let zL := p3LiftFinPotential (leftJointInclusion a)
        (p3SidePotential (4*k+2) t
          (onePointBaseEmbedding a) (Fin.last a) eligibleL W L)
      let zR := p3LiftFinPotential (rightJointInclusion a)
        (p3SidePotential (4*k+2) t
          (onePointBaseEmbedding a) (Fin.last a) eligibleR W R)
      contractAt rightNew
        (contractAt leftNew
          (fun T : Finset (Fin (a+2)) =>
            p1BitToZMod (E.canonicalSignTable T)))
        (U.image old) =
      (contractAt leftNew zL (U.image old) +
        contractAt rightNew zR (U.image old)) +
        coboundary u U := by
  let a : ℕ := (4*k+2)*t
  let old : Fin a ↪ Fin (a+2) :=
    (onePointBaseEmbedding a).trans (leftJointInclusion a)
  let leftNew : Fin (a+2) := (Fin.last a).castSucc
  let rightNew : Fin (a+2) := Fin.last (a+1)
  let zL : Finset (Fin (a+2)) → ZMod 2 :=
    p3LiftFinPotential (leftJointInclusion a)
      (p3SidePotential (4*k+2) t
        (onePointBaseEmbedding a) (Fin.last a) eligibleL W L)
  let zR : Finset (Fin (a+2)) → ZMod 2 :=
    p3LiftFinPotential (rightJointInclusion a)
      (p3SidePotential (4*k+2) t
        (onePointBaseEmbedding a) (Fin.last a) eligibleR W R)
  have hDistinct : leftNew ≠ rightNew := by
    exact Fin.castSucc_ne_last (Fin.last a)
  have hFresh : ∀ v : Fin a, old v ≠ leftNew ∧ old v ≠ rightNew := by
    intro v
    constructor
    · intro h
      have hEq : v.castSucc = Fin.last a :=
        (Fin.castSuccEmb : Fin (a+1) ↪ Fin (a+2)).injective h
      exact Fin.castSucc_ne_last v hEq
    · exact Fin.castSucc_ne_last (v.castSucc)
  have hLeftLink : ∀ Q : Finset (Fin a), Q.card = 4*k+2 →
      p1BitToZMod
        (E.canonicalSignTable (insert leftNew (Q.image old))) =
        coboundary zL (insert leftNew (Q.image old)) := by
    intro Q hQ
    exact p3CanonicalJoint_left_link_via_lift
      (4*k+2) t eligibleL W L E hL Q hQ
  have hRightLink : ∀ Q : Finset (Fin a), Q.card = 4*k+2 →
      p1BitToZMod
        (E.canonicalSignTable (insert rightNew (Q.image old))) =
        coboundary zR (insert rightNew (Q.image old)) := by
    intro Q hQ
    exact p3CanonicalJoint_right_link_via_lift
      (4*k+2) t eligibleR W R E hR Q hQ
  have hBase : ∀ Q : Finset (Fin a), Q.card = 4*k+2 →
      zL (Q.image old) = zR (Q.image old) := by
    intro Q _
    exact p3CanonicalLiftedSides_agree_old_base
      (4*k+2) t eligibleL eligibleR W L R
      (leftJointInclusion a) (rightJointInclusion a)
      old
      (by intro v; rfl)
      (by intro v; exact p3CanonicalJoint_old_coincidence a v)
      Q
  obtain ⟨u,hu⟩ :=
    E.p3ActualJoint_gauge_of_side_potentials
      k a root hE old leftNew rightNew
      hDistinct hFresh zL zR hLeftLink hRightLink hBase
  refine ⟨u, ?_⟩
  intro U hU
  exact hu U hU

end Hypertournaments
