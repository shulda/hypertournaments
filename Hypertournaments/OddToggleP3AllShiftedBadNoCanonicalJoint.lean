import Hypertournaments.OddToggleP3ActualShiftedBadTrialContradiction
import Hypertournaments.OddToggleP3ActualGaugeBoolShift
import Hypertournaments.OddToggleP3ActualMixedBooleanSource

/-!
# All-gauges shifted bad-source avoidance excludes EVERY genuine p3 joint

Assume one full Boolean source assignment has a selected
gauge-SHIFTED forbidden raw full trial for EVERY supported
Boolean gauge v. If a genuine canonical p3 joint E existed
preserving both potential-induced sides, the certified
universal mixed source theorem gives one F₂ cochain u
realizing all its mixed signs simultaneously. The certified
finite-support Boolean gauge theorem encodes this u by ONE
supported v for all selected trials.

For that v, a forbidden shifted raw source trial q exists.
The deterministic actual parent raw-packet theorem then
contradicts admissibility of E. No random calculation, no
synthetic packet, and no preferred joint are used here.
-/

namespace Hypertournaments

open scoped Classical

/-- A global full-source assignment with a genuinely shifted
bad trial for every supported Boolean gauge admits NO
toggleZero-admissible actual canonical joint preserving both
corresponding real one-point sides. -/
theorem p3AllShiftedBad_no_canonical_joint
    (k t : ℕ) (ht : 0 < t)
    (root : Fin ((4*k+2)*t))
    (eligibleL : Finset (Fin (4*k+2)))
    (bits : p3FullSourceSpace (ZMod t) (4*k+1) → Bool)
    (hAvoid :
      ∀ v : p3GaugeDomain ((4*k+2)*t) (4*k) → Bool,
        (fun qi : p3FullSelectedSpace (ZMod t) (4*k+1) =>
          bits (p3FullTrialSourceIndex (4*k+1) qi)) ∉
        p3ShiftedGoodSelectedTrialSet (4*k+1)
          (fun q i => p3ActualSelectedGaugeShift k t ht v q i)
          (fun q => p3FixedBadWChoice (4*k+2)
            (p3ActualSelectedGaugeShift k t ht v q)
            (p3EligibleLinkParity (4*k+1)
              (Finset.univ \ eligibleL)))) :
    ∀ E : Hyper (4*k+3) (Fin ((4*k+2)*t+2)),
      Admissible (toggleZero (switchingAllowed (4*k+3))) E →
      Preserves
        (p3CanonicalSide (4*k+2) t eligibleL
          (p3RealWFromSources (4*k+1) t ht bits)
          (p3RealLinkFromSources (4*k+1) t ht bits))
        E (leftJointInclusion ((4*k+2)*t)) →
      Preserves
        (p3CanonicalSide (4*k+2) t (Finset.univ \ eligibleL)
          (p3RealWFromSources (4*k+1) t ht bits)
          (p3RealLinkFromSources (4*k+1) t ht bits))
        E (rightJointInclusion ((4*k+2)*t)) →
      False := by
  classical
  intro E hE hL hR
  obtain ⟨u,hu⟩ :=
    E.p3ActualSelectedJoint_has_boolean_source_shift
      k t ht root eligibleL bits hE hL hR
  obtain ⟨v,hv⟩ :=
    p3ActualSelectedGaugeShift_complete k t ht u
  let shift :
      p3SelectedTrials (ZMod t) (4*k+1) →
      Fin (4*k+2) → Bool :=
    fun q i => p3ActualSelectedGaugeShift k t ht v q i
  let choice :
      p3SelectedTrials (ZMod t) (4*k+1) →
      Bool → Bool :=
    fun q => p3FixedBadWChoice (4*k+2)
      (shift q)
      (p3EligibleLinkParity (4*k+1) (Finset.univ \ eligibleL))
  have hBad := hAvoid v
  obtain ⟨q,hq⟩ :=
    p3NotShiftedGoodSelected_has_bad_trial
      (4*k+1) shift choice
      (fun qi : p3FullSelectedSpace (ZMod t) (4*k+1) =>
        bits (p3FullTrialSourceIndex (4*k+1) qi)) hBad
  apply E.p3ActualShiftedBadTrial_impossible
    k t ht (Finset.univ \ eligibleL)
    bits hE hR q (shift q)
  · intro i
    have h := hu q i
    rw [← hv q i] at h
    exact h
  · exact hq

end Hypertournaments
