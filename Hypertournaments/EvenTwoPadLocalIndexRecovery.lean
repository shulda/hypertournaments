import Mathlib.Tactic.Ext
import Hypertournaments.EvenSuspensionRecovery
import Hypertournaments.TwoPadIndexShift

/-!
# Exact source local-index recovery in the even two-pad slice

The explicit even suspension recovers every ordered old orientation,
not merely canonical increasing tuples. Consequently each normalized
old facet and its exact local minority index agree with the source.

This is the construction-specific lower-index identity needed in
the h=2 case. The separate raw equality of the two ambient one-pad
facets is needed to invoke the +1 shift theorem.
-/

namespace Hypertournaments

/-- If two intrinsic hypertournaments have identical orientation on
every ordered tuple, their normalized positive facet counts agree. -/
theorem positiveFacetCount_eq_of_orient_eq
    {n : ℕ} {V : Type*}
    (A B : Hyper n V)
    (h : ∀ u : Fin n ↪ V, A.orient u = B.orient u)
    (t : Fin (n + 1) ↪ V) :
    positiveFacetCount A t = positiveFacetCount B t := by
  unfold positiveFacetCount
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  unfold normalizedFacet
  rw [h (facet t i)]

/-- Identical orientations give the same local type on every tuple
at every arity. The intrinsic ordering of the tuples is unrestricted. -/
theorem localIndex_eq_of_orient_eq
    {n : ℕ} {V : Type*}
    (A B : Hyper n V)
    (h : ∀ u : Fin n ↪ V, A.orient u = B.orient u)
    (t : Fin (n + 1) ↪ V) :
    localIndex A t = localIndex B t := by
  unfold localIndex
  rw [positiveFacetCount_eq_of_orient_eq A B h t]

/-- In the concrete even two-coordinate suspension, fixing any
two increasing pads recovers exactly the old local minority index,
for ALL ordered old (n+1)-tuples. -/
theorem Hyper.evenSuspension_twoPadSlice_localIndex
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (x y : Fin m) (hxy : x < y)
    (t : Fin (n + 1) ↪ Fin k) :
    localIndex
      ((A.evenSuspension m k).twoPadSlice (evenOldShift m k)
        (evenPadShift m k x) (evenPadShift m k y)
        (evenPadShift_not_mem_old m k x)
        (evenPadShift_not_mem_old m k y)
        (fun he => (ne_of_lt hxy) ((evenPadShift m k).injective he))) t =
      localIndex A t := by
  apply localIndex_eq_of_orient_eq
  intro u
  change (A.evenSuspension m k).orient
    (evenPaddedTuple m k x y hxy u) = A.orient u
  exact evenSuspension_orient_twoPads m k A x y hxy u

end Hypertournaments
