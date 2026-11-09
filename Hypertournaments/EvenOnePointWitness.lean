import Hypertournaments.EvenSuspensionExplicitBadSpan
import Hypertournaments.EvenSuspensionBasePreservation
import Hypertournaments.EvenSuspensionSideRecovery
import Hypertournaments.TwoPadDisagreement

/-!
# Ordinary AP induction by explicit bad one-point witnesses

A concrete even suspension turns every bad ordinary canonical one-point
span into another bad ordinary canonical one-point span. This gives a
stronger induction interface than mere failure of ordinary AP and
avoids assuming that every arbitrary AP failure has a one-point witness.

All source assumptions and all identification cases are explicit.
-/

namespace Hypertournaments

/-- Existence of an actual finite bad ordinary one-point span. -/
def HasBadOnePoint (n : ℕ) (S : Set ℕ) : Prop :=
  ∃ (a : ℕ) (A : Hyper n (Fin a))
    (L R : Hyper n (Fin (a+1))),
    Admissible S A ∧
    Admissible S L ∧
    Admissible S R ∧
    Preserves A L (onePointBaseEmbedding a) ∧
    Preserves A R (onePointBaseEmbedding a) ∧
    ¬ OnePointHasAmalgam S A L R

theorem not_hasAP_of_bad_onePoint
    {n : ℕ} {S : Set ℕ}
    (hbad : HasBadOnePoint n S) : ¬ HasAP n S := by
  obtain ⟨a, A, L, R, hA, hL, hR, hAL, hAR, hno⟩ := hbad
  exact not_hasAP_of_no_onePoint_amalgam A L R
    hA hL hR hAL hAR hno

/-- An obstruction on the distinct canonical union plus disagreement
also excludes any amalgam identifying the two new vertices. -/
theorem no_onePoint_amalgam_of_disagreement_and_no_joint
    {n a : ℕ} (S : Set ℕ)
    (A : Hyper n (Fin a)) (L R : Hyper n (Fin (a+1)))
    (hdisagree : ∃ t : Fin n ↪ Fin (a+1),
      L.orient t ≠ R.orient t)
    (hNoJoint : ∀ E : Hyper n (Fin (a+2)),
      Admissible S E →
      Preserves L E (leftJointInclusion a) →
      Preserves R E (rightJointInclusion a) → False) :
    ¬ OnePointHasAmalgam S A L R := by
  intro h
  obtain ⟨d, D, i, j, hD, hi, hj, hbase⟩ := h
  have hbase' : ∀ x : Fin a, i x.castSucc = j x.castSucc := by
    intro x
    exact hbase x
  have hne : i (Fin.last a) ≠ j (Fin.last a) :=
    onePoint_points_distinct_of_orient_disagree
      L R D i j hbase' hi hj hdisagree
  obtain ⟨g, hleft, hright⟩ :=
    exists_joint_embedding a d i j hbase' hne
  let E : Hyper n (Fin (a+2)) := D.pullback g
  have hE : Admissible S E := admissible_pullback D g hD
  have hEL : Preserves L E (leftJointInclusion a) := by
    intro t
    change D.orient ((t.trans (leftJointInclusion a)).trans g) =
      L.orient t
    have ht :
        (t.trans (leftJointInclusion a)).trans g = t.trans i := by
      ext x
      exact congrArg Fin.val (DFunLike.congr_fun hleft (t x))
    rw [ht]
    exact hi t
  have hER : Preserves R E (rightJointInclusion a) := by
    intro t
    change D.orient ((t.trans (rightJointInclusion a)).trans g) =
      R.orient t
    have ht :
        (t.trans (rightJointInclusion a)).trans g = t.trans j := by
      ext x
      exact congrArg Fin.val (DFunLike.congr_fun hright (t x))
    rw [ht]
    exact hj t
  exact hNoJoint E hE hEL hER

/-- Every genuine lower bad one-point span has a genuine higher bad
one-point suspension span; no AP-failure normalization is needed. -/
theorem HasBadOnePoint.evenSuspension
    (k : ℕ) (S T : Set ℕ)
    (hcentral : k ∈ S)
    (hraise : ∀ d : ℕ, d ∈ S → d+1 ∈ T)
    (hshift : shiftedAllowed T ⊆ S)
    (hbad : HasBadOnePoint (2*k) S) :
    HasBadOnePoint (2*k+2) T := by
  obtain ⟨a, A, L, R, hA, hL, hR, hAL, hAR, hno⟩ := hbad
  let m : ℕ :=
    2 ^ Fintype.card (Fin (2*k+1) ↪ Fin (a+2)) + 1
  have hm :
      2 ^ Fintype.card (Fin (2*k+1) ↪ Fin (a+2)) < m := by
    dsimp [m]
    omega
  let Ahi : Hyper (2*k+2) (Fin (m+a)) :=
    A.evenSuspension m a
  let Lhi : Hyper (2*k+2) (Fin (m+a+1)) :=
    L.evenSuspension m (a+1)
  let Rhi : Hyper (2*k+2) (Fin (m+a+1)) :=
    R.evenSuspension m (a+1)
  have hAhi : Admissible T Ahi :=
    A.evenSuspension_admissible_of_shift k m a S T hA hcentral hraise
  have hLhi : Admissible T Lhi :=
    L.evenSuspension_admissible_of_shift k m (a+1) S T hL hcentral hraise
  have hRhi : Admissible T Rhi :=
    R.evenSuspension_admissible_of_shift k m (a+1) S T hR hcentral hraise
  have hALhi : Preserves Ahi Lhi (onePointBaseEmbedding (m+a)) :=
    Hyper.evenSuspension_preserves_base (m := m) A L hAL
  have hARhi : Preserves Ahi Rhi (onePointBaseEmbedding (m+a)) :=
    Hyper.evenSuspension_preserves_base (m := m) A R hAR
  have hLowNoJoint :=
    onePointNoAmalgam_no_canonical_joint S A L R hno
  have hLowDisagree :=
    onePointNoAmalgam_has_disagreement S A L R hL hno
  have hrec : CanonicalTwoPadSideRecovery
      (2*k) a m L R Lhi Rhi :=
    canonical_twoPad_recovery_evenSuspension (m := m) L R
  have hHighDisagree :
      ∃ t : Fin (2*k+2) ↪ Fin (m+a+1),
        Lhi.orient t ≠ Rhi.orient t :=
    canonical_twoPad_disagreement_of_low_disagreement
      L R Lhi Rhi hm hrec hLowDisagree
  have hNoHighJoint :
      ∀ E : Hyper (2*k+2) (Fin (m+a+2)),
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
