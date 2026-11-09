import Hypertournaments.OddNonExceptionalNegativeStep
import Hypertournaments.NegativeEvenAll
import Hypertournaments.SeedFiveBadOnePoint
import Hypertournaments.SwitchingShift

/-!
# Complete negative induction modulo the exceptional odd toggle-zero classes

All even arities have unconditional negative ordinary-AP witnesses.
Every nonexceptional odd arity has a witness by the concrete rooted
odd suspension, using actual one-point spans, not a normalization of
arbitrary failures of AP.

The sole remaining proof input in this module is an explicit bad
ordinary one-point span for each odd-arity toggle-zero switching
class in arities >= 7. We do *not* assert that input as an axiom.
It appears only as the hypothesis `OddToggleOnePointObstructions`.

This gives a fully formalized and transparent reduction of the
negative classification to the remaining mathematical family.
-/

namespace Hypertournaments

/-- The one remaining family of negative one-point obligations.
The index `k >= 2` corresponds to odd arities `2*k+3 >= 7`.
A witness is deliberately stronger than merely `¬ HasAP`, so
it can be propagated by the concrete suspension induction. -/
def OddToggleOnePointObstructions : Prop :=
  ∀ k : ℕ, 2 ≤ k →
    HasBadOnePoint (2*k+3)
      (toggleZero (switchingAllowed (2*k+3)))

/-- A full step in the odd negative induction, conditional precisely
on the higher-arity toggle-zero bad one-point witness. -/
theorem negativeOnePointGoal_odd_step_of_toggle
    (k : ℕ) (hk : 2 ≤ k)
    (hind : NegativeOnePointGoal (2*k+1))
    (htoggle : HasBadOnePoint (2*k+3)
      (toggleZero (switchingAllowed (2*k+3)))) :
    NegativeOnePointGoal (2*k+3) := by
  intro T hvalid hcentral hmissing hnon
  by_cases hshift : shiftedAllowed T = switchingAllowed (2*k+1)
  · have hnot : T ≠ switchingAllowed (2*k+3) := by
      intro heq
      rcases hnon with heven | hdiff
      · obtain ⟨j, hj⟩ := heven
        omega
      · exact hdiff heq
    have hsize : (2*k+1)+2 = 2*k+3 := by omega
    rcases shiftedAllowed_switching_two_choices (2*k+1) T hshift with
      hsame | hflipped
    · rw [hsize] at hsame
      exact False.elim (hnot hsame)
    · rw [hsize] at hflipped
      rw [hflipped]
      exact htoggle
  · exact negativeOnePointGoal_odd_nonexceptional_step
      k hk hind T hvalid hcentral hmissing hshift

/-- The odd-arity negative one-point goal follows in every odd arity
at least five, assuming only the uniformly indexed toggle-zero
witnesses in odd arities at least seven. The arity-five case is
unconditional and already has three explicit finite witnesses. -/
theorem negativeOnePointGoal_odd_all_of_toggle
    (h : OddToggleOnePointObstructions)
    (k : ℕ) (hk : 2 ≤ k) :
    NegativeOnePointGoal (2*k+1) := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, k = j+2 :=
    ⟨k-2, by omega⟩
  subst k
  have hall : ∀ j : ℕ, NegativeOnePointGoal (2*(j+2)+1) := by
    intro j
    induction j with
    | zero =>
        simpa using seedFive_negativeOnePointGoal
    | succ j ih =>
        have hstep := negativeOnePointGoal_odd_step_of_toggle
          (j+2) (by omega) ih (h (j+2) (by omega))
        have heq : 2*(Nat.succ j+2)+1 = 2*(j+2)+3 := by omega
        rw [heq]
        exact hstep
  exact hall j

/-- All negative central-containing type families have actual bad
ordinary one-point spans, provided the sole exceptional odd
toggle-zero witness family is supplied. -/
theorem negativeOnePointGoal_all_of_odd_toggle
    (h : OddToggleOnePointObstructions)
    (n : ℕ) (hn : 4 ≤ n) :
    NegativeOnePointGoal n := by
  by_cases he : Even n
  · exact negativeOnePointGoal_even_all n hn he
  · have ho : Odd n := Nat.not_even_iff_odd.mp he
    obtain ⟨k, hk⟩ := ho
    have hodd : n = 2*k+1 := by omega
    have hk2 : 2 ≤ k := by omega
    rw [hodd]
    exact negativeOnePointGoal_odd_all_of_toggle h k hk2

/-- The negative non-amalgamation statement, with the single
explicit odd exceptional dependency and no opaque transfer axioms. -/
theorem negativeGoal_all_of_odd_toggle
    (h : OddToggleOnePointObstructions)
    (n : ℕ) (hn : 4 ≤ n) :
    NegativeGoal n := by
  intro S hvalid hcentral hmissing hnon
  exact not_hasAP_of_bad_onePoint
    ((negativeOnePointGoal_all_of_odd_toggle h n hn)
      S hvalid hcentral hmissing hnon)

/-- The desired necessary implication for ordinary AP at every
arity >= 4. Its *only* mathematical input not already formalized
unconditionally is `OddToggleOnePointObstructions`. -/
theorem negative_classification_all_of_odd_toggle
    (h : OddToggleOnePointObstructions)
    (n : ℕ) (hn : 4 ≤ n)
    (S : Set ℕ) (hvalid : ValidTypes n S)
    (hcentral : centralIndex n ∈ S)
    (hAP : HasAP n S) :
    NecessaryAlternatives n S := by
  by_cases hnext : nextCentralIndex n ∈ S
  · exact Or.inl hnext
  · by_cases he : Even n
    · have hbad : HasBadOnePoint n S :=
        (negativeOnePointGoal_all_of_odd_toggle h n hn)
          S hvalid hcentral hnext (Or.inl he)
      exact False.elim ((not_hasAP_of_bad_onePoint hbad) hAP)
    · right
      refine ⟨Nat.not_even_iff_odd.mp he, ?_⟩
      by_contra hdiff
      have hbad : HasBadOnePoint n S :=
        (negativeOnePointGoal_all_of_odd_toggle h n hn)
          S hvalid hcentral hnext (Or.inr hdiff)
      exact (not_hasAP_of_bad_onePoint hbad) hAP

end Hypertournaments
