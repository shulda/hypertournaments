import Hypertournaments.OddToggleP3SixBlockGeometry

/-!
# The exceptional five-occupied-block pattern in the p3 side proof

When m=6, a one-fresh packet using exactly m-1=5 blocks
has two excess vertices, so at most two blocks are nonsingleton.
Either two consecutive occupied block labels are singleton, or
the exact alternating singleton/double profile occurs:
  singleton, double, singleton, double, singleton.
In that exceptional profile, the singleton vertices appear
at positions start, start+3, start+6, so opposite parities
are still forced.

These are exact finite Boolean and arithmetic observations;
the later actual packet proof must connect occupied block
cardinalities and their increasing sorted vertex positions.
-/

namespace Hypertournaments

/-- At most two bad blocks among five: either an adjacent good pair,
or the unique no-adjacent-good pattern is S,D,S,D,S. -/
theorem p3FiveBlocks_goodAdjacent_or_alternating
    (bad : Fin 5 → Bool)
    (hbad :
      (Finset.univ.filter (fun i : Fin 5 => bad i = true)).card ≤ 2) :
    (bad 0 = false ∧ bad 1 = false) ∨
    (bad 1 = false ∧ bad 2 = false) ∨
    (bad 2 = false ∧ bad 3 = false) ∨
    (bad 3 = false ∧ bad 4 = false) ∨
    (bad 0 = false ∧ bad 1 = true ∧ bad 2 = false ∧
      bad 3 = true ∧ bad 4 = false) := by
  have hfinite : ∀ b : Fin 5 → Bool,
      (Finset.univ.filter (fun i : Fin 5 => b i = true)).card ≤ 2 →
      (b 0 = false ∧ b 1 = false) ∨
      (b 1 = false ∧ b 2 = false) ∨
      (b 2 = false ∧ b 3 = false) ∨
      (b 3 = false ∧ b 4 = false) ∨
      (b 0 = false ∧ b 1 = true ∧ b 2 = false ∧
        b 3 = true ∧ b 4 = false) := by decide
  exact hfinite bad hbad

/-- With block occupancy S,D,S,D,S, the three singleton
positions are separated by triples of vertices. The first
two singleton positions have opposite parity, for every
offset start. -/
theorem p3FiveBlockAlternating_singletons_oppositeParity
    (start : ℕ) :
    (start+3)%2 ≠ start%2 := by
  omega

end Hypertournaments
