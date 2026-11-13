import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Hypertournaments.SeedFourPacket

/-!
# The arity-four mixed packet as a genuine local type index

The earlier Boolean implications were phrased in elementary bits.
This module identifies them with `localIndex` on an actual
intrinsic 4-hypertournament, for any injective five-tuple.

No finite seed or list of signs is assumed in the proof.
-/

namespace Hypertournaments

/-- The explicit mixed-packet count is definitionally the number
of positive normalized facets of the five-tuple. -/
theorem mixedPacketPositiveCount4_eq
    {V : Type*} (D : Hyper 4 V) (f : Fin 5 ↪ V) :
    mixedPacketPositiveCount4
      (D.orient (facet f 4)) (D.orient (facet f 0))
      (D.orient (facet f 3)) (D.orient (facet f 2))
      (D.orient (facet f 1)) =
    positiveFacetCount D f := by
  unfold mixedPacketPositiveCount4 positiveFacetCount
  congr 1
  ext i
  fin_cases i <;> simp [normalizedFacet, Bool.xor]

/-- Centrality of an actual five-tuple is precisely the
2-or-3-positive-sign condition of the mixed packet. -/
theorem localIndex_four_central_iff
    {V : Type*} (D : Hyper 4 V) (f : Fin 5 ↪ V) :
    localIndex D f = 2 ↔
    mixedPacketCentral4
      (D.orient (facet f 4)) (D.orient (facet f 0))
      (D.orient (facet f 3)) (D.orient (facet f 2))
      (D.orient (facet f 1)) := by
  have hbound := positiveFacetCount_le D f
  unfold localIndex mixedPacketCentral4
  rw [mixedPacketPositiveCount4_eq D f]
  omega

/-- A central five-tuple with negative endpoint facets satisfies
the three elementary negative-packet constraints. -/
theorem negativePacketRule_of_localIndex
    {V : Type*} (D : Hyper 4 V) (f : Fin 5 ↪ V)
    (hl : D.orient (facet f 4) = false)
    (hr : D.orient (facet f 0) = false)
    (hc : localIndex D f = 2) :
    negativePacketRule
      (D.orient (facet f 3))
      (D.orient (facet f 2))
      (D.orient (facet f 1)) := by
  have hh := (localIndex_four_central_iff D f).mp hc
  rw [hl, hr] at hh
  exact (mixedPacket_negative_rule_iff _ _ _).mp hh

/-- The analogous positive-packet rule. -/
theorem positivePacketRule_of_localIndex
    {V : Type*} (D : Hyper 4 V) (f : Fin 5 ↪ V)
    (hl : D.orient (facet f 4) = true)
    (hr : D.orient (facet f 0) = true)
    (hc : localIndex D f = 2) :
    positivePacketRule
      (D.orient (facet f 3))
      (D.orient (facet f 2))
      (D.orient (facet f 1)) := by
  have hh := (localIndex_four_central_iff D f).mp hc
  rw [hl, hr] at hh
  exact (mixedPacket_positive_rule_iff _ _ _).mp hh

end Hypertournaments
