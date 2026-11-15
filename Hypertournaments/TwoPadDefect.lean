import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Convert
import Hypertournaments.NegativeReduction

/-!
# Defect arithmetic for the two-pad reflection

Once two equal one-pad Boolean profiles are chosen, the initial two
normalized facets of each mixed (n+3)-tuple have opposite signs.
Its other facets are exactly the old normalized (n+1)-packet.

If the old packet has m facets and c positive signs, the new packet
has m+2 facets and c+1 positives. This yields the shift of minority
index by exactly one, and in particular the new packet cannot have
the homogeneous type zero.

The combinatorial correspondence between the actual packet facets
and these counts is a separate structural proof obligation.
-/

namespace Hypertournaments

/-- Appending one positive and one negative facet raises the
minority number by precisely one. -/
theorem twoPad_minority_shift (m c : ℕ) (hc : c ≤ m) :
    min (c + 1) ((m + 2) - (c + 1)) =
      min c (m - c) + 1 := by
  omega

/-- A packet whose first two facets have opposite signs cannot
have homogeneous local type. -/
theorem twoPad_shift_nonzero (m c : ℕ) (hc : c ≤ m) :
    0 < min (c + 1) ((m + 2) - (c + 1)) := by
  rw [twoPad_minority_shift m c hc]
  omega

/-- Convenient index form: an old (n+1)-facet packet shifted by
two pads has minority index one above its original minority. -/
theorem twoPad_localIndex_count_shift
    (n c : ℕ) (hc : c ≤ n + 1) :
    min (c + 1) ((n + 3) - (c + 1)) =
      min c ((n + 1) - c) + 1 := by
  convert twoPad_minority_shift (n + 1) c hc using 1 <;> omega

end Hypertournaments
