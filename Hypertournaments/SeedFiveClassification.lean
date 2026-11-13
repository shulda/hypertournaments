import Hypertournaments.SeedFiveClassificationCases
import Hypertournaments.SeedFiveConeNoAmalgam
import Hypertournaments.SeedFiveTwoNoAmalgam
import Hypertournaments.SeedFiveExtraNoAmalgam

/-!
# Complete unconditional arity-five negative classification seed

The three necessary ordinary-AP obstructions in arity five are now
kernel-checked individually, with their finite source diagrams,
identification analysis, and mixed-packet contradictions.

The previously checked exhaustive set-of-indices reduction is
instantiated with exactly those three theorems. Thus the second base
case of the all-arity induction has *no* remaining assumptions.
The first base case, `seedFour_negativeGoal`, is in
SeedFourClassification.

The higher-arity suspension, reflection, and odd-exception
obligations in `NegativeDependencies` remain separate and
unproved; this file does not claim the general negative theorem.
-/

namespace Hypertournaments

/-- Unconditional arity-five basis of the all-arity negative
classification induction, for genuine type indices. -/
theorem seedFive_negativeGoal : NegativeGoal 5 :=
  seedFive_negativeGoal_of_three_obstructions
    seed5Cone_not_hasAP seed5Two_not_hasAP seed5Extra_not_hasAP

/-- Exported necessary condition for ordinary amalgamation in
all central-containing six-constrained 5-hypertournament ages:
type 2 must be allowed, unless the allowed set is exactly the
odd switching family {1,3}. -/
theorem negative_classification_five
    (S : Set ℕ) (hvalid : ValidTypes 5 S)
    (hcentral : centralIndex 5 ∈ S) (hAP : HasAP 5 S) :
    NecessaryAlternatives 5 S := by
  by_cases hnext : nextCentralIndex 5 ∈ S
  · exact Or.inl hnext
  · have hswitch : S = switchingAllowed 5 := by
      by_contra hneq
      exact (seedFive_negativeGoal S hvalid hcentral hnext
        (Or.inr hneq)) hAP
    exact Or.inr ⟨by decide, hswitch⟩

end Hypertournaments
