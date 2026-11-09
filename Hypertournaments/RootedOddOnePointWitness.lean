import Hypertournaments.RootedOddSuspensionAdmissibility
import Hypertournaments.RootedOddSuspensionBase
import Hypertournaments.RootedOddSuspensionRecovery
import Hypertournaments.EvenOnePointWitness

/-!
# Transfer of bad ordinary one-point spans through rooted odd suspension

For odd source arity 2k+1, use the concrete rooted suspension with root
0 in the nonempty source common base. Its high sides inherit the same
root under the canonical one-point base embedding.

The high span is S-admissible by the full concrete odd suspension
admissibility theorem; it preserves the common base, and any possible
high amalgam would reflect to a lower one using exact two-pad
orientation recovery. Ordinary amalgams identifying the two new
vertices are excluded using the lifted side-orientation disagreement.

This proves a genuine ordinary AP witness transfer for every *given*
lower bad span whose base is nonempty. It does not assume that every
abstract AP failure has such a witness.
-/

namespace Hypertournaments

/-- A concrete lower bad one-point span of odd arity, with nonempty
common base, transfers to a concrete bad ordinary one-point span two
arities higher. -/
theorem HasBadOnePoint.oddRootedSuspension_of_span
    (k a : ℕ) (ha : 0 < a) (S T : Set ℕ)
    (A : Hyper (2*k+1) (Fin a))
    (L R : Hyper (2*k+1) (Fin (a+1)))
    (hA : Admissible S A) (hL : Admissible S L)
    (hR : Admissible S R)
    (hAL : Preserves A L (onePointBaseEmbedding a))
    (hAR : Preserves A R (onePointBaseEmbedding a))
    (hcentral : k+1 ∈ S)
    (hraise : ∀ d : ℕ, d ∈ S → d+1 ∈ T)
    (hshift : shiftedAllowed T ⊆ S)
    (hno : ¬ OnePointHasAmalgam S A L R) :
    HasBadOnePoint (2*k+3) T := by
  let root : Fin a := ⟨0, ha⟩
  let rootLift : Fin (a+1) := onePointBaseEmbedding a root
  have hroot0 : root.val = 0 := rfl
  have hrootLift0 : rootLift.val = 0 := by
    change root.val = 0
    exact hroot0
  let m : ℕ :=
    2 ^ Fintype.card (Fin (2*k+2) ↪ Fin (a+2)) + 1
  have hm :
      2 ^ Fintype.card (Fin (2*k+2) ↪ Fin (a+2)) < m := by
    dsimp [m]
    omega
  let Ahi : Hyper (2*k+3) (Fin (m+a)) :=
    A.rootedOddSuspension m a root
  let Lhi : Hyper (2*k+3) (Fin (m+a+1)) :=
    L.rootedOddSuspension m (a+1) rootLift
  let Rhi : Hyper (2*k+3) (Fin (m+a+1)) :=
    R.rootedOddSuspension m (a+1) rootLift
  have hAhi : Admissible T Ahi :=
    A.rootedOddSuspension_admissible_of_shift
      k m a S T root hroot0 hA hcentral hraise
  have hLhi : Admissible T Lhi :=
    L.rootedOddSuspension_admissible_of_shift
      k m (a+1) S T rootLift hrootLift0 hL hcentral hraise
  have hRhi : Admissible T Rhi :=
    R.rootedOddSuspension_admissible_of_shift
      k m (a+1) S T rootLift hrootLift0 hR hcentral hraise
  have hALhi : Preserves Ahi Lhi
      (onePointBaseEmbedding (m+a)) :=
    Hyper.rootedOddSuspension_preserves_base
      (m := m) A L root hAL
  have hARhi : Preserves Ahi Rhi
      (onePointBaseEmbedding (m+a)) :=
    Hyper.rootedOddSuspension_preserves_base
      (m := m) A R root hAR
  have hLowNoJoint :=
    onePointNoAmalgam_no_canonical_joint S A L R hno
  have hLowDisagree :=
    onePointNoAmalgam_has_disagreement S A L R hL hno
  have hrec : CanonicalTwoPadSideRecovery
      (2*k+1) a m L R Lhi Rhi :=
    canonical_twoPad_recovery_rootedOddSuspension
      (m := m) L R rootLift
  have hHighDisagree :
      ∃ t : Fin (2*k+3) ↪ Fin (m+a+1),
        Lhi.orient t ≠ Rhi.orient t :=
    canonical_twoPad_disagreement_of_low_disagreement
      L R Lhi Rhi hm hrec hLowDisagree
  have hNoHighJoint :
      ∀ E : Hyper (2*k+3) (Fin (m+a+2)),
        Admissible T E →
        Preserves Lhi E (leftJointInclusion (m+a)) →
        Preserves Rhi E (rightJointInclusion (m+a)) → False :=
    no_canonical_high_joint_of_twoPad_recovery
      S T L R Lhi Rhi hLowNoJoint hshift hm hrec
  have hNoHigh :
      ¬ OnePointHasAmalgam T Ahi Lhi Rhi :=
    no_onePoint_amalgam_of_disagreement_and_no_joint
      T Ahi Lhi Rhi hHighDisagree hNoHighJoint
  exact ⟨m+a, Ahi, Lhi, Rhi,
    hAhi, hLhi, hRhi, hALhi, hARhi, hNoHigh⟩

end Hypertournaments
