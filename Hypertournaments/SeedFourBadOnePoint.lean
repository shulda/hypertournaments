import Hypertournaments.EvenOnePointWitness
import Hypertournaments.SeedFourClassification

/-!
# Strengthened arity-four negative base: explicit bad one-point spans

The two unconditional ordinary AP obstructions already proved for
four-hypertournaments are actual canonical one-point diagrams.
Here we export them as witnesses of the stronger HasBadOnePoint
predicate and carry out the same finite allowed-type case split
used for the existing NegativeGoal 4 theorem.

No new finite classification or search computation is needed.
-/

namespace Hypertournaments

/-- Stronger induction goal: an actual bad ordinary one-point span
in every negative central-containing allowed-type class. -/
def NegativeOnePointGoal (n : ℕ) : Prop :=
  ∀ S : Set ℕ, ValidTypes n S →
    centralIndex n ∈ S →
    nextCentralIndex n ∉ S →
    (Even n ∨ S ≠ switchingAllowed n) →
    HasBadOnePoint n S

/-- The central-only arity-four obstruction is a genuinely bad
ordinary one-point span, not merely an abstract failure of AP. -/
theorem centralOnlyFour_badOnePoint :
    HasBadOnePoint 4 ({2} : Set ℕ) := by
  refine ⟨7, seed4Base, seed4Left, seed4Right,
    seed4_base_admissible, seed4_left_admissible,
    seed4_right_admissible, seed4_base_left, seed4_base_right, ?_⟩
  apply no_onePoint_amalgam_of_disagreement_and_no_joint
    ({2} : Set ℕ) seed4Base seed4Left seed4Right seed4_disagreement
  intro E hE hL hR
  exact seed4_no_joint E hE hL hR

/-- The {0,2} arity-four obstruction is also an actual ordinary
bad one-point span. -/
theorem forbidOneFour_badOnePoint :
    HasBadOnePoint 4 ({0,2} : Set ℕ) := by
  refine ⟨6, forbidOneBase, forbidOneLeft, forbidOneRight,
    forbidOne_base_admissible, forbidOne_left_admissible,
    forbidOne_right_admissible,
    forbidOne_base_left, forbidOne_base_right, ?_⟩
  apply no_onePoint_amalgam_of_disagreement_and_no_joint
    ({0,2} : Set ℕ) forbidOneBase forbidOneLeft forbidOneRight
    forbidOne_disagreement
  intro E hE hL hR
  exact forbidOne_no_joint E hE hL hR

/-- Every valid negative arity-four type set admits one of these
explicit bad one-point spans. This is stronger than NegativeGoal 4. -/
theorem seedFour_negativeOnePointGoal : NegativeOnePointGoal 4 := by
  intro S hvalid hcentral hnext _
  have h2 : (2 : ℕ) ∈ S := by
    simpa [centralIndex] using hcentral
  have h1 : (1 : ℕ) ∉ S := by
    simpa [nextCentralIndex, centralIndex] using hnext
  have hsubset : S ⊆ ({0,2} : Set ℕ) := by
    intro d hd
    have hle : d ≤ 2 := by
      have hbound := hvalid d hd
      simpa [centralIndex] using hbound
    have hne : d ≠ 1 := by
      intro h
      subst d
      exact h1 hd
    have hcases : d = 0 ∨ d = 2 := by omega
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hcases
  by_cases h0 : (0 : ℕ) ∈ S
  · have heq : S = ({0,2} : Set ℕ) := by
      apply Set.Subset.antisymm hsubset
      intro d hd
      have hc : d = 0 ∨ d = 2 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hd
      rcases hc with rfl | rfl
      · exact h0
      · exact h2
    rw [heq]
    exact forbidOneFour_badOnePoint
  · have heq : S = ({2} : Set ℕ) := by
      apply Set.Subset.antisymm
      · intro d hd
        have hc : d = 0 ∨ d = 2 := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff]
            using hsubset hd
        rcases hc with rfl | rfl
        · exact False.elim (h0 hd)
        · simp
      · intro d hd
        have hd2 : d = 2 := by
          simpa only [Set.mem_singleton_iff] using hd
        subst d
        exact h2
    rw [heq]
    exact centralOnlyFour_badOnePoint

end Hypertournaments
