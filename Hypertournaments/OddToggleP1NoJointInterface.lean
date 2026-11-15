import Hypertournaments.OddToggleP1SidesAdmissible
import Hypertournaments.OddToggleP1ConcreteDisagreement
import Hypertournaments.EvenOnePointWitness

/-!
# The exact outstanding no-joint proposition for the p1 exceptional class

At every arity n=4k+5 the explicit common base and both one-point
sides are already intrinsically admissible and compatible. Their
orientations disagree on a real common n-tuple when the new vertices
are identified. Therefore the *only* remaining premise for a genuine
bad ordinary one-point witness is the absence of a canonical
two-distinct-new-vertex joint. Once that is proved, the already
certified general ordinary-amalgam reflection immediately yields
failure of ordinary AP, including all identifications.

No new statement is asserted unconditionally beyond the supplied
no-joint premise. This is the final intended interface to the
negative classification induction.
-/

namespace Hypertournaments

/-- The precise, still-open strong-joint exclusion for the actual
explicit exceptional one-point sides. -/
def P1NoCanonicalJoint (k : ℕ) : Prop :=
  ∀ E : Hyper (4*k+5) (Fin (4*k+6+2)),
    Admissible (toggleZero (switchingAllowed (4*k+5))) E →
    Preserves (p1SideHyper k true) E (leftJointInclusion (4*k+6)) →
    Preserves (p1SideHyper k false) E (rightJointInclusion (4*k+6)) →
    False

/-- Any proof of the concrete p1 no-joint statement yields a bad
ordinary one-point span in that arity, without silently assuming
new-vertex distinctness in an arbitrary amalgam. -/
theorem p1HasBadOnePoint_of_no_canonical_joint
    (k : ℕ) (h : P1NoCanonicalJoint k) :
    HasBadOnePoint (4*k+5)
      (toggleZero (switchingAllowed (4*k+5))) := by
  refine ⟨4*k+6, p1BaseHyper k,
    p1SideHyper k true, p1SideHyper k false,
    p1BaseHyper_admissible k,
    p1LeftSide_admissible k, p1RightSide_admissible k,
    p1SideHyper_preserves_base k true,
    p1SideHyper_preserves_base k false, ?_⟩
  exact no_onePoint_amalgam_of_disagreement_and_no_joint
    (toggleZero (switchingAllowed (4*k+5)))
    (p1BaseHyper k) (p1SideHyper k true) (p1SideHyper k false)
    (p1ConcreteSides_orient_disagreement k) h

/-- In particular the class fails ordinary AP if the remaining
actual canonical-joint obstruction is established. -/
theorem p1NotHasAP_of_no_canonical_joint
    (k : ℕ) (h : P1NoCanonicalJoint k) :
    ¬ HasAP (4*k+5)
      (toggleZero (switchingAllowed (4*k+5))) := by
  exact not_hasAP_of_bad_onePoint
    (p1HasBadOnePoint_of_no_canonical_joint k h)

end Hypertournaments
