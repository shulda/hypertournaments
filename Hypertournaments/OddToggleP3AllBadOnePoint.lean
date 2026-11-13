import Hypertournaments.OddToggleP3AllGaugesShiftedFiniteWitness
import Hypertournaments.OddToggleP3BadOnePointSourceTemplate
import Hypertournaments.NegativeModuloP3

/-!
# Unconditional p3 exceptional ordinary one-point non-amalgamation

For every k>=1 put m=4k+2 and use the explicit positive
block size t=2^(m+1)*m^(m-2). The selected source group is
ZMod t, with exactly t elements. Its zero-sum code has
t^(m-1) selected transversals.

For every supported Boolean gauge v and selected q, use
the actual local source shift coming from δ of the
corresponding finitely supported cochain and the exact
phase-to-bad-W functional of the real RIGHT endpoint.
The fully gauge-SHIFTED finite counting theorem produces
ONE global W/link source assignment simultaneously forcing
odd link parity on q0 and a genuinely shifted forbidden
full trial for EVERY supported gauge.

The certified actual p3 bad-one-point source template
converts it to two finite admissible one-point sides
which cannot be amalgamated even with vertex identification.

No artificial independence assumption or synthetic parent
orientation belongs to the argument. The global negative
classification then follows from the existing exact induction
reduction from all other arities to the exceptional p3 family.
-/

namespace Hypertournaments

open scoped Classical

/-- A real bad ordinary one-point span in every exceptional
arity n=4k+3 >=7; this discharges the sole remaining negative
classification assumption without introducing any axiom. -/
theorem p3BadOnePoint_all (k : ℕ) (hk : 1 ≤ k) :
    HasBadOnePoint (4*k+3)
      (toggleZero (switchingAllowed (4*k+3))) := by
  classical
  let m : ℕ := 4*k+2
  let t : ℕ := p3WitnessBlockSize m
  have hm : 2 ≤ m := by dsimp [m]; omega
  have ht : 0 < t := p3WitnessBlockSize_pos m hm
  letI : NeZero t := ⟨by omega⟩
  have hCard : Fintype.card (ZMod t) = p3WitnessBlockSize m := by
    simpa only [t] using (ZMod.card t)
  let q0 : p3SelectedTrials (ZMod t) (m-1) :=
    ⟨fun _ => 0, by simp⟩
  let chosen : Fin ((m-1)+1) :=
    ⟨0, by dsimp [m]; omega⟩
  have ha : 0 < m*t := by
    exact Nat.mul_pos (by omega) ht
  let root : Fin (m*t) := ⟨0,ha⟩
  let Shift :
      (p3GaugeDomain (m*t) (m-2) → Bool) →
      p3SelectedTrials (ZMod t) (m-1) →
      Fin ((m-1)+1) → Bool :=
    fun v q i => p3ActualSelectedGaugeShift k t ht v q i
  let Choice :
      (p3GaugeDomain (m*t) (m-2) → Bool) →
      p3SelectedTrials (ZMod t) (m-1) →
      Bool → Bool :=
    fun v q => p3FixedBadWChoice m (Shift v q)
      (p3EligibleLinkParity (m-1)
        (Finset.univ \ p3EligibleLowerHalf m))
  obtain ⟨bits,hOdd,hAvoid⟩ :=
    p3FullSource_exists_oddLink_and_shifted_badTrial_for_all_gauges
      (G := ZMod t) m hm hCard q0 chosen Shift Choice
  exact p3BadOnePoint_of_global_shifted_source_witness
    k t hk ht root bits q0 hOdd hAvoid

/-- The exceptional p3 family of strong ordinary one-point
obstructions required by the classification induction is
unconditional. -/
theorem p3OddOnePointObstructions :
    OddP3OnePointObstructions := by
  intro j hj
  exact p3BadOnePoint_all j hj

/-- The full necessary part of the ordinary-AP classification
of constrained hypertournaments in all arities at least four,
assuming only the original standard valid type-set and central
type hypotheses. No remaining exceptional p3 premise. -/
theorem negative_classification_all_unconditional
    (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S)
    (hcentral : centralIndex n ∈ S)
    (hAP : HasAP n S) :
    NecessaryAlternatives n S := by
  exact negative_classification_all_of_p3
    p3OddOnePointObstructions n hn S hvalid hcentral hAP

end Hypertournaments
