import Hypertournaments.OddToggleP3RealSourcePotentials
import Hypertournaments.OddToggleP3CochainSideLinks

/-!
# Evaluate eligible actual selected zero-sum link facets

A selected zero-sum tuple q : Fin(s+1) → ZMod t gives the true
old full transversal Q ⊆ Fin((s+1)*t). Removing its vertex from
block i gives a genuine missing-block transversal with *unique*
missing block i. Thus the side's eligibility predicate at that
facet is equivalent to i belonging to the specified eligible half.

Combined with the exact source-to-potential extension, every
selected facet reads precisely the global Boolean link source
indexed by p3FullTrialSourceIndex, or zero outside the eligible
half. No artificial independent-link assumption is introduced.
-/

namespace Hypertournaments

/-- The true missing-block facet selected by deleting block i
is eligible exactly when i lies in the designated eligible set. -/
theorem p3ActualSelectedPuncture_eligible_iff
    (s t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin (s+1)))
    (q : p3SelectedTrials (ZMod t) s) (i : Fin (s+1)) :
    p3IsEligibleMissingTransversal (s+1) t eligible
      (p3ActualPunctureSubsetIndex s t ht (q,i)) ↔
      i ∈ eligible := by
  classical
  constructor
  · intro h
    obtain ⟨_, j, hj, _hjzero, hrest⟩ := h
    have hiZero :=
      (p3ActualPunctureSubset_occupancies s t ht q i).1
    have hij : i = j := by
      by_contra hne
      have hiOne := hrest i hne
      omega
    simpa only [hij] using hj
  · intro hi
    simpa only [p3ActualPunctureSubsetIndex,
      p3ActualPunctureSourceIndex] using
      (p3CoordinatePuncture_isEligibleMissing
        (s+1) t ht eligible q.1 i hi)

/-- Exact evaluation of the genuine eligible L/R side potential
on a selected punctured old subset. -/
theorem p3RealSelectedPuncture_linkValue
    (s t : ℕ) (ht : 0 < t)
    (eligible : Finset (Fin (s+1)))
    (bits : p3FullSourceSpace (ZMod t) s → Bool)
    (q : p3SelectedTrials (ZMod t) s) (i : Fin (s+1)) :
    (if p3IsEligibleMissingTransversal (s+1) t eligible
          (p3ActualPunctureSubsetIndex s t ht (q,i))
      then p3RealLinkFromSources s t ht bits
          (p3ActualPunctureSubsetIndex s t ht (q,i))
      else 0) =
      if i ∈ eligible then
        p1BitToZMod
          (bits (p3FullTrialSourceIndex s (q,Sum.inl i)))
      else 0 := by
  classical
  rw [p3ActualSelectedPuncture_eligible_iff s t ht eligible q i]
  by_cases hi : i ∈ eligible
  · simp only [if_pos hi]
    exact p3RealLinkFromSources_selected s t ht bits (q,i)
  · simp [hi]

end Hypertournaments
