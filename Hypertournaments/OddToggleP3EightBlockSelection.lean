import Hypertournaments.OddToggleP3SixBlockGeometry

/-!
# Larger protected-block pigeonholes for the p3 one-fresh sides

For n=4k+3 and k≥2 we have m=4k+2≥10 old blocks.
When a one-fresh packet meets all m blocks, there is exactly one
nonsingleton block; among any four consecutive protected labels
there must be adjacent singleton blocks. When exactly one old block
is absent, at most two others are nonsingleton, so at most three of
the first eight labels are defective; one of four disjoint adjacent
block pairs remains entirely singleton.

Both finite selections have small exhaustive Boolean proofs (2^4
and 2^8 cases), independent of the random potential coefficients.
The proofs that actual numeric occupancy supports the respective
bad-label count premises are separate.
-/

namespace Hypertournaments

/-- At most one bad block among four consecutive labels leaves
some adjacent pair of singleton blocks. -/
theorem p3FourBlocks_good_consecutive_pair
    (bad : Fin 4 → Bool)
    (hbad :
      (Finset.univ.filter (fun i : Fin 4 => bad i = true)).card ≤ 1) :
    (bad 0 = false ∧ bad 1 = false) ∨
    (bad 1 = false ∧ bad 2 = false) ∨
    (bad 2 = false ∧ bad 3 = false) := by
  have hfinite : ∀ b : Fin 4 → Bool,
      (Finset.univ.filter (fun i : Fin 4 => b i = true)).card ≤ 1 →
      (b 0 = false ∧ b 1 = false) ∨
      (b 1 = false ∧ b 2 = false) ∨
      (b 2 = false ∧ b 3 = false) := by decide
  exact hfinite bad hbad

/-- At most three defective blocks among eight consecutive labels
leave at least one of four disjoint adjacent pairs fully singleton. -/
theorem p3EightBlocks_good_consecutive_pair
    (bad : Fin 8 → Bool)
    (hbad :
      (Finset.univ.filter (fun i : Fin 8 => bad i = true)).card ≤ 3) :
    (bad 0 = false ∧ bad 1 = false) ∨
    (bad 2 = false ∧ bad 3 = false) ∨
    (bad 4 = false ∧ bad 5 = false) ∨
    (bad 6 = false ∧ bad 7 = false) := by
  have hfinite : ∀ b : Fin 8 → Bool,
      (Finset.univ.filter (fun i : Fin 8 => b i = true)).card ≤ 3 →
      (b 0 = false ∧ b 1 = false) ∨
      (b 2 = false ∧ b 3 = false) ∨
      (b 4 = false ∧ b 5 = false) ∨
      (b 6 = false ∧ b 7 = false) := by decide
  exact hfinite bad hbad

end Hypertournaments
