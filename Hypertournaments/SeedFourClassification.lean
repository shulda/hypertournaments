import Lean.Elab.Tactic.Omega
import Hypertournaments.NegativeReduction
import Hypertournaments.SeedFourNoAmalgam
import Hypertournaments.SeedFourForbidOneNoAmalgam

/-!
# Complete arity-four seed for the negative classification

If the central local type T_{4,2} is allowed, the next-to-central
type T_{4,1} is forbidden, and only genuine indices 0,1,2 are
permitted, then the allowed set is exactly {2} or {0,2}. Both
cases are kernel-checked ordinary non-amalgamation obstructions.

This theorem discharges `NegativeDependencies.seedFour` without
any external axioms. Arity two is deliberately excluded.
-/

namespace Hypertournaments

/-- The unconditional arity-four base case of the all-arity
negative-classification induction. -/
theorem seedFour_negativeGoal : NegativeGoal 4 := by
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
      have hcases : d = 0 ∨ d = 2 := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hd
      rcases hcases with rfl | rfl
      · exact h0
      · exact h2
    rw [heq]
    exact forbidOneFour_not_hasAP
  · have heq : S = ({2} : Set ℕ) := by
      apply Set.Subset.antisymm
      · intro d hd
        have hcases : d = 0 ∨ d = 2 := by
          simpa only [Set.mem_insert_iff, Set.mem_singleton_iff]
            using hsubset hd
        rcases hcases with rfl | rfl
        · exact False.elim (h0 hd)
        · simp
      · intro d hd
        have hd2 : d = 2 := by
          simpa only [Set.mem_singleton_iff] using hd
        subst d
        exact h2
    rw [heq]
    exact centralOnlyFour_not_hasAP

/-- Exportable even-arity-four necessary condition, already with
ordinary AP and intrinsic local-type indices. -/
theorem negative_classification_four
    (S : Set ℕ) (hvalid : ValidTypes 4 S)
    (hcentral : centralIndex 4 ∈ S) (hAP : HasAP 4 S) :
    nextCentralIndex 4 ∈ S := by
  by_contra hmissing
  exact (seedFour_negativeGoal S hvalid hcentral hmissing
    (Or.inl (by decide))) hAP

end Hypertournaments
