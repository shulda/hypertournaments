import Hypertournaments.Amalgamation

/-!
# Logical assembly of the negative classification

This module intentionally separates the *logical induction* from the
mathematical seed and suspension proofs. The final theorem here is
conditional on the named dependencies in `NegativeDependencies`.

No dependencies are postulated as axioms. They are structure fields,
so this is not yet the unconditional negative AP classification.
The proof makes the precise remaining proof obligations auditable.
-/

namespace Hypertournaments

/-- Allowed local type indices in the lower arity, obtained by
subtracting one from all positive indices of the higher arity. -/
def shiftedAllowed (S : Set ℕ) : Set ℕ := {d | d + 1 ∈ S}

/-- The central index grows by one when arity grows by two. -/
theorem centralIndex_add_two (n : ℕ) :
    centralIndex (n + 2) = centralIndex n + 1 := by
  unfold centralIndex
  omega

theorem nextCentralIndex_add_two (n : ℕ) (h : 1 ≤ centralIndex n) :
    nextCentralIndex (n + 2) = nextCentralIndex n + 1 := by
  unfold nextCentralIndex
  rw [centralIndex_add_two]
  omega

/-- Well-formed allowed higher-arity types induce well-formed types
on the lower arity by shifting positive indices. -/
theorem shiftedAllowed_valid (n : ℕ) (S : Set ℕ)
    (hvalid : ValidTypes (n + 2) S) :
    ValidTypes n (shiftedAllowed S) := by
  intro d hd
  have hd' := hvalid (d + 1) hd
  rw [centralIndex_add_two] at hd'
  omega

theorem shiftedAllowed_central (n : ℕ) (S : Set ℕ)
    (hcentral : centralIndex (n + 2) ∈ S) :
    centralIndex n ∈ shiftedAllowed S := by
  change centralIndex n + 1 ∈ S
  simpa [centralIndex_add_two] using hcentral

theorem shiftedAllowed_next_missing (n : ℕ) (S : Set ℕ)
    (hn : 4 ≤ n) (hmissing : nextCentralIndex (n + 2) ∉ S) :
    nextCentralIndex n ∉ shiftedAllowed S := by
  intro h
  have hle : 1 ≤ centralIndex n := by
    unfold centralIndex
    omega
  apply hmissing
  simpa [shiftedAllowed, nextCentralIndex_add_two n hle] using h

/-- The negative cases which remain after excluding the unrestricted
positive-index family and the odd switching family. -/
def NegativeGoal (n : ℕ) : Prop :=
  ∀ S : Set ℕ, ValidTypes n S →
    centralIndex n ∈ S →
    nextCentralIndex n ∉ S →
    (Even n ∨ S ≠ switchingAllowed n) →
    ¬ HasAP n S

/--
The exact mathematical ingredients needed by the negative direction.

* The two seed implications (arity four and arity five).
* Even and odd two-coordinate arity transfers.
* The leftover odd exceptional parity family.

The actual seed and transfer constructions are NOT proved here.
-/
structure NegativeDependencies where
  seedFour : NegativeGoal 4
  seedFive : NegativeGoal 5
  evenTransfer :
    ∀ (n : ℕ), 4 ≤ n → Even n →
      ∀ (S : Set ℕ), ValidTypes (n + 2) S →
        centralIndex (n + 2) ∈ S →
        nextCentralIndex (n + 2) ∉ S →
        ¬ HasAP n (shiftedAllowed S) →
        ¬ HasAP (n + 2) S
  oddTransfer :
    ∀ (n : ℕ), 5 ≤ n → Odd n →
      ∀ (S : Set ℕ), ValidTypes (n + 2) S →
        centralIndex (n + 2) ∈ S →
        nextCentralIndex (n + 2) ∉ S →
        shiftedAllowed S ≠ switchingAllowed n →
        ¬ HasAP n (shiftedAllowed S) →
        ¬ HasAP (n + 2) S
  oddExceptional :
    ∀ (n : ℕ), 5 ≤ n → Odd n →
      ∀ (S : Set ℕ), ValidTypes (n + 2) S →
        centralIndex (n + 2) ∈ S →
        nextCentralIndex (n + 2) ∉ S →
        shiftedAllowed S = switchingAllowed n →
        S ≠ switchingAllowed (n + 2) →
        ¬ HasAP (n + 2) S

/-- The step from n to n+2 needs only one lower-arity
negative-classification premise. -/
theorem negativeGoal_add_two (D : NegativeDependencies)
    (n : ℕ) (hn : 4 ≤ n) (hind : NegativeGoal n) :
    NegativeGoal (n + 2) := by
  intro S hv hc hm hnon
  have hvlow := shiftedAllowed_valid n S hv
  have hclow := shiftedAllowed_central n S hc
  have hmlow := shiftedAllowed_next_missing n S hn hm
  by_cases he : Even n
  · have hb := hind (shiftedAllowed S) hvlow hclow hmlow (Or.inl he)
    exact D.evenTransfer n hn he S hv hc hm hb
  · have ho : Odd n := Nat.not_even_iff_odd.mp he
    have hn5 : 5 ≤ n := by
      rcases ho with ⟨k, hk⟩
      omega
    by_cases hs : shiftedAllowed S = switchingAllowed n
    · have hnot : S ≠ switchingAllowed (n + 2) := by
        rcases hnon with heup | hdifferent
        · exfalso
          apply he
          rcases heup with ⟨k, hk⟩
          exact ⟨k - 1, by omega⟩
        · exact hdifferent
      exact D.oddExceptional n hn5 ho S hv hc hm hs hnot
    · have hb := hind (shiftedAllowed S) hvlow hclow hmlow (Or.inr hs)
      exact D.oddTransfer n hn5 ho S hv hc hm hs hb

/-- The seed and arity-transfer hypotheses cover every arity at
least four. This proof is elementary two-step induction. -/
theorem negativeGoal_all (D : NegativeDependencies)
    (n : ℕ) (hn : 4 ≤ n) : NegativeGoal n := by
  have hall : ∀ k : ℕ, NegativeGoal (k + 4) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
        simpa using D.seedFour
    | one =>
        simpa using D.seedFive
    | more k hk hk1 =>
        have hstep := negativeGoal_add_two D (k + 4) (by omega) hk
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hstep
  obtain ⟨k, hk⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [hk]
  exact hall k

/--
Exportable negative classification, conditional on all explicitly
named mathematical inputs. Later source files will construct those
inputs, thereby yielding the unconditional theorem with the *same*
conclusion and AP definition.
-/
theorem negative_classification_of_dependencies
    (D : NegativeDependencies) (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S)
    (hcentral : centralIndex n ∈ S)
    (hAP : HasAP n S) :
    NecessaryAlternatives n S := by
  by_cases hnext : nextCentralIndex n ∈ S
  · exact Or.inl hnext
  · by_cases he : Even n
    · have hb := (negativeGoal_all D n hn) S hvalid hcentral hnext (Or.inl he)
      exact False.elim (hb hAP)
    · have ho : Odd n := Nat.not_even_iff_odd.mp he
      right
      refine ⟨ho, ?_⟩
      by_contra hdiff
      have hb := (negativeGoal_all D n hn) S hvalid hcentral hnext (Or.inr hdiff)
      exact hb hAP

end Hypertournaments
