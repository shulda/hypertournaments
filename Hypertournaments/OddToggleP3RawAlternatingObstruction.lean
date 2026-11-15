import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3BoolPhases
import Hypertournaments.OddToggleP3AgeSplit
import Hypertournaments.LocalTypes

/-!
# An actual alternating raw packet is a forbidden homogeneous type

The canonical order's raw signs in an intrinsic hypertournament
packet are the alternating word of some Boolean phase precisely
when all normalized signs are equal. Thus either no normalized
facet is positive or every normalized facet is positive.
The minority-count local index is zero in either case.

This implication is uniform in all arities and independent of
any gauge, ambient ordering, or probability model. It is the
exact intrinsic bridge needed to convert a forced forbidden
alternating mixed packet into a violation of the homogeneous-free
p3 age.
-/

namespace Hypertournaments

/-- Every actual intrinsic packet whose RAW facet orientations
are an alternating Boolean word has homogeneous type index zero,
regardless of the phase of the alternating word. -/
theorem Hyper.localIndex_zero_of_raw_alternating
    {n : ℕ} {V : Type*}
    (A : Hyper n V) (f : Fin (n+1) ↪ V)
    (phase : Bool)
    (hraw : ∀ i : Fin (n+1),
      A.orient (facet f i) = p3AlternatingWord (n+1) phase i) :
    localIndex A f = 0 := by
  have hnorm (i : Fin (n+1)) :
      normalizedFacet A f i = phase := by
    unfold normalizedFacet
    rw [hraw i]
    unfold p3AlternatingWord
    by_cases heven : i.val % 2 = 0
    · have hodd : i.val % 2 ≠ 1 := by omega
      simp [heven,hodd]
    · have hodd : i.val % 2 = 1 := by omega
      cases phase <;> simp [heven,hodd]
  cases phase with
  | false =>
      have hpos : positiveFacetCount A f = 0 := by
        unfold positiveFacetCount
        have hempty :
            (Finset.univ.filter
              (fun i : Fin (n+1) => normalizedFacet A f i = true)) =
              ∅ := by
          ext i
          simp [hnorm i]
        rw [hempty]
        rfl
      unfold localIndex
      rw [hpos]
      simp
  | true =>
      have hpos : positiveFacetCount A f = n+1 := by
        unfold positiveFacetCount
        have hall :
            (Finset.univ.filter
              (fun i : Fin (n+1) => normalizedFacet A f i = true)) =
              Finset.univ := by
          ext i
          simp [hnorm i]
        rw [hall]
        simp
      unfold localIndex
      rw [hpos]
      simp

/-- In every exceptional arity n=4k+3, an alternating raw packet
violates the homogeneous-free switching age outright. -/
theorem Hyper.raw_alternating_not_p3ToggleAllowed
    (k : ℕ) {V : Type*}
    (A : Hyper (4*k+3) V)
    (f : Fin (4*k+4) ↪ V) (phase : Bool)
    (hraw : ∀ i : Fin (4*k+4),
      A.orient (facet f i) = p3AlternatingWord (4*k+4) phase i) :
    localIndex A f ∉ toggleZero (switchingAllowed (4*k+3)) := by
  have hzero : localIndex A f = 0 :=
    A.localIndex_zero_of_raw_alternating f phase hraw
  change ¬(if localIndex A f = 0
    then localIndex A f ∉ switchingAllowed (4*k+3)
    else localIndex A f ∈ switchingAllowed (4*k+3))
  simp [hzero, p3Zero_mem_switchingAllowed k]

end Hypertournaments
