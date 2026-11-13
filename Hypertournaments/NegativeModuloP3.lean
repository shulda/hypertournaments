import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP1CompleteNoJoint
import Hypertournaments.NegativeModuloOddToggle

/-!
# The general negative hypertournament classification reduces to n ≡ 3 (mod 4)

The entire odd exceptional n ≡ 1 (mod 4) ordinary non-AP
one-point family is supplied by the genuine explicitly certified
p1 span. In conjunction with the already proved even and
nonexceptional odd induction, the only remaining mathematical
negative-classification premise is the infinite family of
n ≡ 3 (mod 4) toggle-zero one-point obstructions (n ≥ 7).

This is a purely logical indexing reduction, not a proof of those
remaining probabilistic p3 witnesses.
-/

namespace Hypertournaments

/-- The sole higher-arity negative input not covered by actual
explicit p1 witnesses and the existing general induction. -/
def OddP3OnePointObstructions : Prop :=
  ∀ j : ℕ, 1 ≤ j →
    HasBadOnePoint (4*j+3)
      (toggleZero (switchingAllowed (4*j+3)))

/-- Complete odd exceptional one-point induction inputs follow
from p3 alone, since the p1 family is unconditional. -/
theorem oddToggleOnePointObstructions_of_p3
    (hP3 : OddP3OnePointObstructions) :
    OddToggleOnePointObstructions := by
  intro k hk
  by_cases he : k % 2 = 0
  · have hj : 1 ≤ k / 2 := by omega
    have hsize : 2*k+3 = 4*(k/2)+3 := by omega
    rw [hsize]
    exact hP3 (k/2) hj
  · have hsize : 2*k+3 = 4*(k/2)+5 := by omega
    rw [hsize]
    exact p1BadOnePoint_all (k/2)

/-- Thus the complete ordinary-AP necessary classification
in every arity at least four is conditional only on the
remaining p3 exceptional family, not on the p1 family. -/
theorem negative_classification_all_of_p3
    (hP3 : OddP3OnePointObstructions)
    (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S)
    (hcentral : centralIndex n ∈ S)
    (hAP : HasAP n S) :
    NecessaryAlternatives n S := by
  exact negative_classification_all_of_odd_toggle
    (oddToggleOnePointObstructions_of_p3 hP3)
    n hn S hvalid hcentral hAP

/-- Failure of ordinary AP for every excluded type family
also requires only p3, with no extra exception for p1. -/
theorem negativeGoal_all_of_p3
    (hP3 : OddP3OnePointObstructions)
    (n : ℕ) (hn : 4 ≤ n) :
    NegativeGoal n := by
  exact negativeGoal_all_of_odd_toggle
    (oddToggleOnePointObstructions_of_p3 hP3) n hn

end Hypertournaments
