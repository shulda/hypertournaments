import Mathlib.Data.Fintype.Pi
import Hypertournaments.Basic

/-!
# Uniform six-edge selector for sparse one-fresh p3 packets

A one-fresh p3 packet has m+1 old vertices. When exactly m−1 old
blocks are occupied, there are TWO excess old vertices, hence only
two equal-adjacent-block edges in its increasing block-label word.

An edge joining two consecutive positions of that word is "bad"
when the two labels agree. A position whose incident edges are all
good represents a singleton block; deleting it removes its block.

Among the first six consecutive EDGES, if at most two are bad,
there must be a singleton vertex of EVEN deletion-position parity
(among positions 0,2,4) and a singleton vertex of ODD parity
(among positions 1,3,5). Each bad edge blocks at most one candidate
of each parity, and we have three candidates on each side.

This local finite statement works uniformly for ALL m≥6 and
removes the need for separate five-occupied-block case splits
once the actual count of repeated edges has been transferred
from true block occupancies.
-/

namespace Hypertournaments

/-- With at most two bad edges among the first six consecutive
block-label edges, there is a vertex of each parity among the
first six positions whose incident edges are all good.
The six Boolean choices encode the edges (0,1),...,(5,6).
An incident-good vertex in an actual monotone block word
must be a singleton-block vertex. -/
theorem p3SixEdgeFlags_two_parity_singletons
    (bad : Fin 6 → Bool)
    (hbad :
      (Finset.univ.filter (fun i : Fin 6 => bad i = true)).card ≤ 2) :
    ((bad 0 = false) ∨
      (bad 1 = false ∧ bad 2 = false) ∨
      (bad 3 = false ∧ bad 4 = false)) ∧
    ((bad 0 = false ∧ bad 1 = false) ∨
      (bad 2 = false ∧ bad 3 = false) ∨
      (bad 4 = false ∧ bad 5 = false)) := by
  have hfinite : ∀ b : Fin 6 → Bool,
      (Finset.univ.filter (fun i : Fin 6 => b i = true)).card ≤ 2 →
      ((b 0 = false) ∨
        (b 1 = false ∧ b 2 = false) ∨
        (b 3 = false ∧ b 4 = false)) ∧
      ((b 0 = false ∧ b 1 = false) ∨
        (b 2 = false ∧ b 3 = false) ∨
        (b 4 = false ∧ b 5 = false)) := by decide
  exact hfinite bad hbad

end Hypertournaments
