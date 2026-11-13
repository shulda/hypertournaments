import Hypertournaments.OddToggleP3AgeSplit

/-!
# The genuine homogeneous-free p3 age is a switching subage

The p3 negative construction asks about the genuine age
toggleZero(switchingAllowed (4k+3)), which excludes homogeneous
local packets but retains the parity-constrained switching
condition. The already certified arbitrary-joint mixed-gauge
theorems are phrased for switchingAllowed.

This module proves the exact reduction: every genuinely admissible
joint of the *smaller* homogeneous-free age is also switching-
admissible, without assumptions on the joint embedding or on
its choice of orientation. Thus the full mixed-gauge proof applies
to every possible distinct-fresh-point amalgam in the actual age.
-/

namespace Hypertournaments

/-- Every permitted p3 nonhomogeneous switching index remains
permitted for the underlying switching parity family. -/
theorem p3ToggleZero_subset_switchingAllowed (k : ℕ) :
    toggleZero (switchingAllowed (4*k+3)) ⊆
      switchingAllowed (4*k+3) := by
  intro j hj
  change (if j = 0 then
    j ∉ switchingAllowed (4*k+3)
    else j ∈ switchingAllowed (4*k+3)) at hj
  by_cases hz : j = 0
  · have hzero := p3Zero_mem_switchingAllowed k
    simp [hz, hzero] at hj
  · simpa only [if_neg hz] using hj

/-- An arbitrary actual intrinsic p3 homogeneous-free joint
automatically satisfies the necessary full switching parity
condition for the certified universal mixed-gauge construction. -/
theorem Hyper.p3ToggleAdmissible_switchingAllowed
    (k a : ℕ)
    (E : Hyper (4*k+3) (Fin a))
    (hE : Admissible (toggleZero (switchingAllowed (4*k+3))) E) :
    Admissible (switchingAllowed (4*k+3)) E := by
  intro f
  exact p3ToggleZero_subset_switchingAllowed k (hE f)

end Hypertournaments
