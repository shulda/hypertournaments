import Hypertournaments.OddToggleP1SideAdmissibilityReduction
import Hypertournaments.OddToggleP1RowMatchesBase
import Hypertournaments.OddToggleP1RightProtectedActualZero

/-!
# Unconditional intrinsic admissibility of both explicit p1 one-point sides

For n=4k+5 the canonical left side has matching raw row parity at
every omitted-old local packet. On the right every packet except
the ones omitting a0 and a4 has matching parity; the two exceptions
have intrinsic homogeneous local type zero. The unique old-only
packet is inherited from the admissible common base.

This finishes the age-membership part of the p1 non-amalgamation
diagram. It does not yet prove no strong/ordinary amalgam exists.
-/

namespace Hypertournaments

theorem p1LeftSide_admissible (k : ℕ) :
    Admissible (toggleZero (switchingAllowed (4*k+5)))
      (p1SideHyper k true) := by
  apply p1Side_admissible_of_rows_or_zero k true
  intro v hQ
  left
  exact p1CanonicalLeft_row_matches_base k v

theorem p1RightSide_admissible (k : ℕ) :
    Admissible (toggleZero (switchingAllowed (4*k+5)))
      (p1SideHyper k false) := by
  apply p1Side_admissible_of_rows_or_zero k false
  intro v hQ
  by_cases hzero : v = p1CoreAt k (0 : Fin 6)
  · subst v
    right
    exact p1RightCoreZero_packet_localIndex k hQ
  · by_cases hfour : v = p1CoreAt k (4 : Fin 6)
    · subst v
      right
      exact p1RightCoreFour_packet_localIndex k hQ
    · left
      exact p1CanonicalRight_row_matches_base_unprotected k v hzero hfour

end Hypertournaments
