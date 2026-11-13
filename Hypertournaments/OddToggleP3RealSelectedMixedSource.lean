import Hypertournaments.OddToggleP3RealTwoSideLinkParity

/-!
# Complementary actual link coefficients on a single zero-sum facet

A true selected puncture deletes one uniquely specified block i.
With complementary eligible halves, exactly one of the two
canonical side potentials contributes to this facet. The total
F₂ value is therefore the UNIQUE globally independent link bit
indexed by that deleted coordinate.

This is the exact h(Q\{v_i}) source identity required for evaluating
the full mixed gauge on selected zero-sum transversals.
-/

namespace Hypertournaments

open scoped Classical

/-- On every selected genuine punctured old subset, the sum of
the left and right complementary eligible side coefficients is
exactly the corresponding global independent source bit. -/
theorem p3RealSelectedTwoSideFacet_eq_linkSource
    (s t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin (s+1)))
    (bits : p3FullSourceSpace (ZMod t) s → Bool)
    (q : p3SelectedTrials (ZMod t) s) (i : Fin (s+1)) :
    (if p3IsEligibleMissingTransversal (s+1) t eligible
          (p3ActualPunctureSubsetIndex s t ht (q,i))
      then p3RealLinkFromSources s t ht bits
          (p3ActualPunctureSubsetIndex s t ht (q,i))
      else 0) +
    (if p3IsEligibleMissingTransversal (s+1) t
          (Finset.univ \ eligible)
          (p3ActualPunctureSubsetIndex s t ht (q,i))
      then p3RealLinkFromSources s t ht bits
          (p3ActualPunctureSubsetIndex s t ht (q,i))
      else 0) =
    p1BitToZMod
      (bits (p3FullTrialSourceIndex s (q,Sum.inl i))) := by
  classical
  rw [p3RealSelectedPuncture_linkValue
    s t ht eligible bits q i,
    p3RealSelectedPuncture_linkValue
    s t ht (Finset.univ \ eligible) bits q i]
  by_cases hi : i ∈ eligible
  · simp [hi]
  · simp [hi]

end Hypertournaments
