import Hypertournaments.OddToggleP3ActualPunctureIndependent

/-!
# The real punctured old subset ALONE identifies its zero-sum source

In actual one-point p3 potentials, L and R are functions of old
finite subsets, without an accompanying missing-block label.
The previous injectivity of (missing block, subset) therefore does
not yet prove that different selected zero-sum sources occupy
different actual potential coefficients.

The strengthened theorem below removes the label. A source
puncture at block i is a genuine eligible-missing transversal
for the singleton eligible set {i}; its unique missing block is
therefore exactly i. Equality of two actual subsets forces their
deleted block labels to coincide. Injectivity of the labelled
source map then finishes the proof.
-/

namespace Hypertournaments

/-- The actual old potential coefficient index is ONLY its finite
subset; the deleted block is not supplied to L or R. -/
def p3ActualPunctureSubsetIndex
    (s t : ℕ) (ht : 0 < t)
    (qi : p3SelectedTrials (ZMod t) s × Fin (s+1)) :
    Finset (Fin ((s+1)*t)) :=
  (p3ActualPunctureSourceIndex s t ht qi).2

/-- On the true source subset, the specified deleted block has
zero occupancy while every other block has occupancy one. -/
theorem p3ActualPunctureSubset_occupancies
    (s t : ℕ) (ht : 0 < t)
    (q : p3SelectedTrials (ZMod t) s)
    (i : Fin (s+1)) :
    p3BlockOccupancy (s+1) t
      (p3ActualPunctureSubsetIndex s t ht (q,i)) i = 0 ∧
    ∀ j : Fin (s+1), j ≠ i →
      p3BlockOccupancy (s+1) t
        (p3ActualPunctureSubsetIndex s t ht (q,i)) j = 1 := by
  classical
  have h := p3CoordinatePuncture_isEligibleMissing
    (s+1) t ht ({i} : Finset (Fin (s+1))) q.1 i
    (Finset.mem_singleton_self i)
  obtain ⟨_, missing, hmissing, hzero, hrest⟩ := h
  have hEq : missing = i := Finset.mem_singleton.mp hmissing
  subst missing
  exact ⟨hzero, hrest⟩

/-- The actual old finite subset of every selected zero-sum
puncture is unique across all selected trials and deleted
coordinates. This is the exact no-source-reuse assertion
needed for assigning independent random L/R potential bits. -/
theorem p3ActualPunctureSubsetIndex_injective
    (s t : ℕ) (ht : 0 < t) :
    Function.Injective (p3ActualPunctureSubsetIndex s t ht) := by
  classical
  intro x y hxy
  have hx := p3ActualPunctureSubset_occupancies
    s t ht x.1 x.2
  have hy := p3ActualPunctureSubset_occupancies
    s t ht y.1 y.2
  have hi : x.2 = y.2 := by
    by_contra hne
    have hz :
        p3BlockOccupancy (s+1) t
          (p3ActualPunctureSubsetIndex s t ht y) x.2 = 0 := by
      rw [← hxy]
      exact hx.1
    have ho :
        p3BlockOccupancy (s+1) t
          (p3ActualPunctureSubsetIndex s t ht y) x.2 = 1 :=
      hy.2 x.2 hne
    omega
  apply p3ActualPunctureSourceIndex_injective s t ht
  change (x.2, p3ActualPunctureSubsetIndex s t ht x) =
    (y.2, p3ActualPunctureSubsetIndex s t ht y)
  exact Prod.ext hi hxy

end Hypertournaments
