import Hypertournaments.SeedFourBadOnePoint
import Hypertournaments.SeedFiveClassification

/-!
# Strengthened arity-five negative base: bad ordinary one-point witnesses

All three non-switching negative arity-five classes are already
represented by explicit, computer-certified, genuinely ordinary bad
one-point spans. This file promotes the three existing witnesses to
the HasBadOnePoint predicate, then runs the exact finite type-set
analysis used in the original arity-five classification.

Together with the corresponding arity-four seed this supplies both
strong witnesses for two-step induction through concrete suspensions.
No new SAT computation or hidden AP normalization is required.
-/

namespace Hypertournaments

theorem seed5Cone_badOnePoint :
    HasBadOnePoint 5 ({3} : Set ℕ) := by
  refine ⟨8, seed5ConeBase, seed5ConeLeft, seed5ConeRight,
    seed5Cone_base_admissible, seed5Cone_left_admissible,
    seed5Cone_right_admissible,
    seed5Cone_base_left, seed5Cone_base_right, ?_⟩
  apply no_onePoint_amalgam_of_disagreement_and_no_joint
    ({3} : Set ℕ) seed5ConeBase seed5ConeLeft seed5ConeRight
    seed5Cone_disagreement
  intro E hE hL hR
  exact seed5Cone_no_joint E hE hL hR

theorem seed5Two_badOnePoint :
    HasBadOnePoint 5 ({0,3} : Set ℕ) := by
  refine ⟨7, seed5TwoBase, seed5TwoLeft, seed5TwoRight,
    seed5Two_base_admissible, seed5Two_left_admissible,
    seed5Two_right_admissible,
    seed5Two_base_left, seed5Two_base_right, ?_⟩
  apply no_onePoint_amalgam_of_disagreement_and_no_joint
    ({0,3} : Set ℕ) seed5TwoBase seed5TwoLeft seed5TwoRight
    seed5Two_disagreement
  intro E hE hL hR
  exact seed5Two_no_joint E hE hL hR

theorem seed5Extra_badOnePoint :
    HasBadOnePoint 5 ({0,1,3} : Set ℕ) := by
  refine ⟨6, seed5ExtraBase, seed5ExtraLeft, seed5ExtraRight,
    seed5Extra_base_admissible, seed5Extra_left_admissible,
    seed5Extra_right_admissible,
    seed5Extra_base_left, seed5Extra_base_right, ?_⟩
  apply no_onePoint_amalgam_of_disagreement_and_no_joint
    ({0,1,3} : Set ℕ) seed5ExtraBase seed5ExtraLeft seed5ExtraRight
    seed5Extra_disagreement
  intro E hE hL hR
  exact seed5Extra_no_joint E hE hL hR

theorem seedFive_negativeOnePointGoal_of_three_witnesses
    (hOnly : HasBadOnePoint 5 ({3} : Set ℕ))
    (hZero : HasBadOnePoint 5 ({0,3} : Set ℕ))
    (hBoth : HasBadOnePoint 5 ({0,1,3} : Set ℕ)) :
    NegativeOnePointGoal 5 := by
  intro S hvalid hcentral hmissing hnon
  have h3 : (3 : ℕ) ∈ S := by
    simpa [centralIndex] using hcentral
  have h2 : (2 : ℕ) ∉ S := by
    simpa [nextCentralIndex, centralIndex] using hmissing
  have hcases (d : ℕ) (hd : d ∈ S) : d = 0 ∨ d = 1 ∨ d = 3 := by
    have hbound : d ≤ 3 := by
      simpa [centralIndex] using hvalid d hd
    have hne : d ≠ 2 := by
      intro he
      subst d
      exact h2 hd
    omega
  by_cases h0 : (0 : ℕ) ∈ S
  · by_cases h1 : (1 : ℕ) ∈ S
    · have heq : S = ({0,1,3} : Set ℕ) := by
        apply Set.Subset.antisymm
        · intro d hd
          rcases hcases d hd with rfl | rfl | rfl <;> simp
        · intro d hd
          have hmem : d = 0 ∨ d = 1 ∨ d = 3 := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hd
          rcases hmem with rfl | rfl | rfl
          · exact h0
          · exact h1
          · exact h3
      simpa [heq] using hBoth
    · have heq : S = ({0,3} : Set ℕ) := by
        apply Set.Subset.antisymm
        · intro d hd
          rcases hcases d hd with rfl | rfl | rfl
          · simp
          · exact False.elim (h1 hd)
          · simp
        · intro d hd
          have hmem : d = 0 ∨ d = 3 := by
            simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hd
          rcases hmem with rfl | rfl
          · exact h0
          · exact h3
      simpa [heq] using hZero
  · by_cases h1 : (1 : ℕ) ∈ S
    · have heq : S = switchingAllowed 5 := by
        apply Set.Subset.antisymm
        · intro d hd
          rcases hcases d hd with rfl | rfl | rfl
          · exact False.elim (h0 hd)
          · change (1 : ℕ) ≤ centralIndex 5 ∧ 1 % 2 = centralIndex 5 % 2
            decide
          · change (3 : ℕ) ≤ centralIndex 5 ∧ 3 % 2 = centralIndex 5 % 2
            decide
        · intro d hd
          have hsmall : d = 1 ∨ d = 3 := by
            change d ≤ centralIndex 5 ∧ d % 2 = centralIndex 5 % 2 at hd
            dsimp [centralIndex] at hd
            omega
          rcases hsmall with rfl | rfl
          · exact h1
          · exact h3
      have hnot : S ≠ switchingAllowed 5 := by
        rcases hnon with he | hnot
        · exact False.elim ((by decide : ¬ Even 5) he)
        · exact hnot
      exact False.elim (hnot heq)
    · have heq : S = ({3} : Set ℕ) := by
        apply Set.Subset.antisymm
        · intro d hd
          rcases hcases d hd with rfl | rfl | rfl
          · exact False.elim (h0 hd)
          · exact False.elim (h1 hd)
          · simp
        · intro d hd
          have he : d = 3 := by
            simpa only [Set.mem_singleton_iff] using hd
          subst d
          exact h3
      simpa [heq] using hOnly

/-- Full strengthened arity-five induction basis, with no additional
assumptions and a concrete bad ordinary one-point span in every case. -/
theorem seedFive_negativeOnePointGoal : NegativeOnePointGoal 5 :=
  seedFive_negativeOnePointGoal_of_three_witnesses
    seed5Cone_badOnePoint seed5Two_badOnePoint seed5Extra_badOnePoint

end Hypertournaments
