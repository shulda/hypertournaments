import Hypertournaments.OddToggleP3ActualSelectedGaugeSupport
import Hypertournaments.OddToggleP3PotentialPresentation

/-!
# Every actual selected mixed F₂ gauge is one FINITE Boolean XOR shift

The universal actual mixed-joint gauge is a ZMod 2-valued
cochain u on all old subsets. The previous certified
selected-facet support theorem shows that for every chosen
zero-sum trial q and every deleted coordinate i, δu of the
actual puncture depends only on the coefficients on old
4k-element sets.

Those finitely supported ZMod 2 coefficients encode
bijectively as Boolean bits. Here we define the *actual*
selected Boolean gauge-shift word and prove that ONE finite
Boolean gauge v reproduces δu on ALL selected trial facets
simultaneously. This is precisely the gauge input of the
certified finite all-gauge union-bound theorem.
-/

namespace Hypertournaments

/-- The actual selected old facet's Boolean gauge shift
determined by a finitely supported Boolean gauge table. -/
noncomputable def p3ActualSelectedGaugeShift
    (k t : ℕ) (ht : 0 < t)
    (v : p3GaugeDomain ((4*k+2)*t) (4*k) → Bool)
    (q : p3SelectedTrials (ZMod t) (4*k+1))
    (i : Fin (4*k+2)) : Bool :=
  p3ZMod2ToBool
    (coboundary
      (p3GaugeExtend ((4*k+2)*t) (4*k)
        (fun D => p1BitToZMod (v D)))
      (p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i)))

/-- Any actual old cochain u yields ONE finite Boolean gauge
that realizes its Boolean coboundary shift on every actual
selected zero-sum punctured old facet simultaneously. -/
theorem p3ActualSelectedGaugeShift_complete
    (k t : ℕ) (ht : 0 < t)
    (u : Finset (Fin ((4*k+2)*t)) → ZMod 2) :
    ∃ v : p3GaugeDomain ((4*k+2)*t) (4*k) → Bool,
      ∀ (q : p3SelectedTrials (ZMod t) (4*k+1))
        (i : Fin (4*k+2)),
        p3ActualSelectedGaugeShift k t ht v q i =
          p3ZMod2ToBool
            (coboundary u
              (p3ActualPunctureSubsetIndex (4*k+1) t ht (q,i))) := by
  classical
  obtain ⟨v0,hv0⟩ :=
    p3ActualSelectedGauge_has_finite_support k t ht u
  let v : p3GaugeDomain ((4*k+2)*t) (4*k) → Bool :=
    fun D => p3ZMod2ToBool (v0 D)
  have hEnc :
      (fun D : p3GaugeDomain ((4*k+2)*t) (4*k) =>
        p1BitToZMod (v D)) = v0 := by
    funext D
    exact p3BitToZMod_roundtrip (v0 D)
  refine ⟨v, ?_⟩
  intro q i
  unfold p3ActualSelectedGaugeShift
  rw [hEnc, hv0 q i]

end Hypertournaments
