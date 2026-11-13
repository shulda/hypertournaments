import Hypertournaments.OddToggleP3ActualPunctureSubsetInjective
import Hypertournaments.OddToggleP3GaugeChoices

/-!
# The actual p3 selected mixed-facet gauge uses only finitely many bits

For the exceptional arity n=4k+3, the universal mixed-gauge
u on all finite old subsets enters every selected mixed facet
only as δu(U), where U is an old (4k+1)-set obtained by deleting
one vertex of a zero-sum full block transversal.

The coboundary on that degree sees only u on old 4k-sets.
The prior exact finite gauge normalisation therefore applies
simultaneously to all *actual selected old facets*. The resulting
finite gauge domain has size choose((4k+2)*t,4k), as required by
the already certified strict full-source union-bound estimate.

No hypothetical joint or random event is assumed here.
-/

namespace Hypertournaments

/-- Every real selected zero-sum puncture has precisely n-2=4k+1
old vertices, the exact degree of the mixed n-facet. -/
theorem p3ActualSelectedPuncture_card
    (k t : ℕ) (ht : 0 < t)
    (q : p3SelectedTrials (ZMod t) (4*k+1))
    (i : Fin (4*k+2)) :
    (p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i)).card =
      4*k+1 := by
  have h := (p3CoordinatePuncture_isEligibleMissing
    (4*k+2) t ht
    (Finset.univ : Finset (Fin (4*k+2))) q.1 i
    (Finset.mem_univ i)).1
  change
    (p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i)).card =
      (4*k+2)-1 at h
  omega

/-- Every old cochain is replaceable on ALL selected true
mixed facets by a gauge whose only input bits are on old
4k-element subsets. Thus no unused larger-degree cochain
coordinates contribute to the real obstruction or its count. -/
theorem p3ActualSelectedGauge_has_finite_support
    (k t : ℕ) (ht : 0 < t)
    (u : Finset (Fin ((4*k+2)*t)) → ZMod 2) :
    ∃ v : p3GaugeDomain ((4*k+2)*t) (4*k) → ZMod 2,
      ∀ (q : p3SelectedTrials (ZMod t) (4*k+1))
        (i : Fin (4*k+2)),
        coboundary
          (p3GaugeExtend ((4*k+2)*t) (4*k) v)
          (p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i)) =
        coboundary u
          (p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i)) := by
  refine ⟨p3GaugeRestrict ((4*k+2)*t) (4*k) u, ?_⟩
  intro q i
  exact p3GaugeRestrictExtend_coboundary
    ((4*k+2)*t) (4*k) u
    (p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i))
    (p3ActualSelectedPuncture_card k t ht q i)

/-- Exactly 2^choose(a,4k) supported Boolean gauges suffice for
every possible real selected mixed-facet sign pattern. -/
theorem p3ActualSelectedBoolGauge_count (k t : ℕ) :
    Fintype.card
      (p3GaugeDomain ((4*k+2)*t) (4*k) → Bool) =
    2 ^ (((4*k+2)*t).choose (4*k)) :=
  p3BoolGaugeChoices_card ((4*k+2)*t) (4*k)

end Hypertournaments
