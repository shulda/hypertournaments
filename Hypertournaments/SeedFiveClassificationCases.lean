import Hypertournaments.NegativeReduction

/-!
# Exhaustive logical reduction of the arity-five base case

With 5-hypertournaments, the actual local indices are 0,1,2,3.
If the central index 3 is allowed and the next-to-central index 2
is missing, the only nonswitching possibilities are exactly

  {3}, {0,3}, {0,1,3}.

This theorem does not fabricate the three non-amalgamation proofs:
they occur as explicit arguments. The {0,3} case has now been
reduced separately to an independently checked finite SAT core.
-/

namespace Hypertournaments

/-- The arity-five induction seed is a consequence of exactly
three named ordinary AP obstructions.  No other negative cases
need separate witnesses. -/
theorem seedFive_negativeGoal_of_three_obstructions
    (hOnly : ¬ HasAP 5 ({3} : Set ℕ))
    (hZero : ¬ HasAP 5 ({0,3} : Set ℕ))
    (hBoth : ¬ HasAP 5 ({0,1,3} : Set ℕ)) :
    NegativeGoal 5 := by
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

end Hypertournaments
