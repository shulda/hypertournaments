import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3AllShiftedBadNoCanonicalJoint
import Hypertournaments.OddToggleP3RealOddLinkSideDisagreement
import Hypertournaments.OddToggleP3CompleteCanonicalSideAge
import Hypertournaments.EvenOnePointWitness

/-!
# A shifted full-source witness is a genuine bad ordinary one-point p3 span

A full global Boolean W/link assignment gives actual canonical
one-point p3 sides with the common induced old base. For k>=1,
their entire intrinsic ages are already certified.

If one selected real zero-sum trial has odd link-source parity,
the sides disagree on one ACTUAL orientation of an injective
n-tuple. They therefore cannot identify their fresh points.

If the assignment additionally causes a shifted bad raw source
trial for EVERY supported Boolean gauge, the certified universal
source-to-packet theorem rules out EVERY distinct-vertex
canonical joint. The existing ordinary one-point amalgamation
reduction combines the two cases.

This template isolates the remaining source-existence step.
The next theorem will construct such an assignment using the
corrected all-gauge shifted finite witness.
-/

namespace Hypertournaments

open scoped Classical

/-- Every global source assignment satisfying BOTH the
selected odd-link event and the all-gauge SHIFTED bad-trial
event produces a genuine ordinary bad one-point span of
the p3 homogeneous-free switching age. -/
theorem p3BadOnePoint_of_global_shifted_source_witness
    (k t : ℕ) (hk : 1 ≤ k) [NeZero t] (ht : 0 < t)
    (root : Fin ((4*k+2)*t))
    (bits : p3FullSourceSpace (ZMod t) (4*k+1) → Bool)
    (q0 : p3SelectedTrials (ZMod t) (4*k+1))
    (hOdd :
      (∑ i : Fin (4*k+2),
        p1BitToZMod
          (bits (p3FullTrialSourceIndex (4*k+1) (q0,Sum.inl i)))) = 1)
    (hAvoid :
      ∀ v : p3GaugeDomain ((4*k+2)*t) (4*k) → Bool,
        (fun qi : p3FullSelectedSpace (ZMod t) (4*k+1) =>
          bits (p3FullTrialSourceIndex (4*k+1) qi)) ∉
        p3ShiftedGoodSelectedTrialSet (4*k+1)
          (fun q i => p3ActualSelectedGaugeShift k t ht v q i)
          (fun q => p3FixedBadWChoice (4*k+2)
            (p3ActualSelectedGaugeShift k t ht v q)
            (p3EligibleLinkParity (4*k+1)
              (Finset.univ \ p3EligibleLowerHalf (4*k+2))))) :
    HasBadOnePoint (4*k+3)
      (toggleZero (switchingAllowed (4*k+3))) := by
  classical
  let m : ℕ := 4*k+2
  let s : ℕ := 4*k+1
  let a : ℕ := m*t
  let eligibleL : Finset (Fin m) := p3EligibleLowerHalf m
  let eligibleR : Finset (Fin m) := Finset.univ \ eligibleL
  let W : Finset (Fin a) → ZMod 2 :=
    p3RealWFromSources s t ht bits
  let Link : Finset (Fin a) → ZMod 2 :=
    p3RealLinkFromSources s t ht bits
  let L : Hyper (m+1) (Fin (a+1)) :=
    p3CanonicalSide m t eligibleL W Link
  let R : Hyper (m+1) (Fin (a+1)) :=
    p3CanonicalSide m t eligibleR W Link
  let A : Hyper (m+1) (Fin a) :=
    L.pullback (onePointBaseEmbedding a)
  have hComplement : eligibleR = p3EligibleUpperHalf m := by
    dsimp only [eligibleR, eligibleL]
    ext i
    simp [p3EligibleLowerHalf, p3EligibleUpperHalf] <;> omega
  have hL : Admissible
      (toggleZero (switchingAllowed (4*k+3))) L :=
    p3CanonicalSide_lowerHalf_admissible k t hk ht W Link
  have hR : Admissible
      (toggleZero (switchingAllowed (4*k+3))) R := by
    change Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3CanonicalSide m t eligibleR W Link)
    rw [hComplement]
    exact p3CanonicalSide_upperHalf_admissible k t hk ht W Link
  have hA : Admissible
      (toggleZero (switchingAllowed (4*k+3))) A :=
    admissible_pullback L (onePointBaseEmbedding a) hL
  have hAL : Preserves A L (onePointBaseEmbedding a) := by
    intro z
    rfl
  have hSpan := p3CanonicalSpan_preserves_base
    m t eligibleL eligibleR W Link Link
  have hAR : Preserves A R (onePointBaseEmbedding a) := by
    intro z
    change R.orient (z.trans (onePointBaseEmbedding a)) =
      L.orient (z.trans (onePointBaseEmbedding a))
    exact (hSpan.2 z).trans (hSpan.1 z).symm
  have hDisagree : ∃ z : Fin (4*k+3) ↪ Fin (a+1),
      L.orient z ≠ R.orient z :=
    p3RealOddLink_forces_side_tuple_disagreement
      k t ht eligibleL bits q0 hOdd
  have hNoJoint :
      ∀ E : Hyper (4*k+3) (Fin (a+2)),
        Admissible (toggleZero (switchingAllowed (4*k+3))) E →
        Preserves L E (leftJointInclusion a) →
        Preserves R E (rightJointInclusion a) → False := by
    intro E hE hEL hER
    exact p3AllShiftedBad_no_canonical_joint
      k t ht root eligibleL bits hAvoid E hE hEL hER
  have hNoAmalgam :
      ¬ OnePointHasAmalgam
        (toggleZero (switchingAllowed (4*k+3))) A L R :=
    no_onePoint_amalgam_of_disagreement_and_no_joint
      (toggleZero (switchingAllowed (4*k+3)))
      A L R hDisagree hNoJoint
  exact ⟨a,A,L,R,hA,hL,hR,hAL,hAR,hNoAmalgam⟩

end Hypertournaments
