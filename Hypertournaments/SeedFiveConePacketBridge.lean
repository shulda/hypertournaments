import Mathlib.Data.Fin.VecNotation
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Hypertournaments.SeedFiveConeData
import Hypertournaments.SeedFiveTwoPacketBridge
import Hypertournaments.SeedFourPacket

/-!
# Finite reflection of central six-facets to central five-facets

Consider a six-tuple (cone, left, i, j, k, right).
Its normalized facet signs are

  (y, !beta, x_jk, !x_ik, x_ij, !alpha)

where y is the unconstrained facet without the cone vertex and
alpha,beta are the two fixed side-link signs. Centrality of the
six-tuple forces exactly three positive normalized facets. Removing
the initial y shows that the other five facet signs have two or three
positives. They are precisely the complements of the normalized
five-facet packet for the original arity-four witness.

Here we encode this as two general kernel-checkable implications,
one for each of the negative/positive packet rules used by the
already verified seven-rule arity-four Boolean contradiction.

The algebraic lemmas are independent of the concrete cone tables.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- A central cone six-packet with both original endpoint signs
negative forces the arity-four negative implication rule. -/
theorem coneNegativeRule_of_count (y xij xik xjk : Bool)
    (hc : seed5TwoMixedPositiveCount y false xij xik xjk false = 3) :
    negativePacketRule xij xik xjk := by
  rw [seed5TwoMixedPositiveCount_eq_sum] at hc
  cases y <;> cases xij <;> cases xik <;> cases xjk <;>
    norm_num [negativePacketRule] at *

/-- The same fact for two positive endpoint signs. -/
theorem conePositiveRule_of_count (y xij xik xjk : Bool)
    (hc : seed5TwoMixedPositiveCount y true xij xik xjk true = 3) :
    positivePacketRule xij xik xjk := by
  rw [seed5TwoMixedPositiveCount_eq_sum] at hc
  cases y <;> cases xij <;> cases xik <;> cases xjk <;>
    norm_num [positivePacketRule] at *

/-- A six-element packet of local type 3 has exactly three positive
normalized facets, not merely three as the minority count. -/
theorem positiveFacetCount_eq_three_of_central5
    {V : Type*} (E : Hyper 5 V) (t : Fin 6 ↪ V)
    (hcentral : localIndex E t = 3) :
    positiveFacetCount E t = 3 := by
  have hbound := positiveFacetCount_le E t
  unfold localIndex at hcentral
  omega

/-- Actual mixed central six-packets with negative source endpoints
satisfy the original arity-four negative packet rule. -/
theorem coneNegativeRule_of_localIndex
    {V : Type*} (E : Hyper 5 V) (t : Fin 6 ↪ V)
    (xij xik xjk : Bool)
    (h1 : E.orient (facet t 1) = false)
    (h2 : E.orient (facet t 2) = xjk)
    (h3 : E.orient (facet t 3) = xik)
    (h4 : E.orient (facet t 4) = xij)
    (h5 : E.orient (facet t 5) = false)
    (hcentral : localIndex E t = 3) :
    negativePacketRule xij xik xjk := by
  let y : Bool := E.orient (facet t 0)
  have hfacet (i : Fin 6) :
      normalizedFacet E t i =
        (![y, !false, xjk, !xik, xij, !false] : Fin 6 → Bool) i := by
    fin_cases i <;> simp [normalizedFacet, h1, h2, h3, h4, h5, y]
  have hcount :
      positiveFacetCount E t =
        seed5TwoMixedPositiveCount y false xij xik xjk false := by
    unfold positiveFacetCount seed5TwoMixedPositiveCount
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfacet i]
  have hthree : positiveFacetCount E t = 3 :=
    positiveFacetCount_eq_three_of_central5 E t hcentral
  exact coneNegativeRule_of_count y xij xik xjk (hcount.symm.trans hthree)

/-- Actual mixed central six-packets with positive source endpoints
satisfy the original arity-four positive packet rule. -/
theorem conePositiveRule_of_localIndex
    {V : Type*} (E : Hyper 5 V) (t : Fin 6 ↪ V)
    (xij xik xjk : Bool)
    (h1 : E.orient (facet t 1) = true)
    (h2 : E.orient (facet t 2) = xjk)
    (h3 : E.orient (facet t 3) = xik)
    (h4 : E.orient (facet t 4) = xij)
    (h5 : E.orient (facet t 5) = true)
    (hcentral : localIndex E t = 3) :
    positivePacketRule xij xik xjk := by
  let y : Bool := E.orient (facet t 0)
  have hfacet (i : Fin 6) :
      normalizedFacet E t i =
        (![y, !true, xjk, !xik, xij, !true] : Fin 6 → Bool) i := by
    fin_cases i <;> simp [normalizedFacet, h1, h2, h3, h4, h5, y]
  have hcount :
      positiveFacetCount E t =
        seed5TwoMixedPositiveCount y true xij xik xjk true := by
    unfold positiveFacetCount seed5TwoMixedPositiveCount
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfacet i]
  have hthree : positiveFacetCount E t = 3 :=
    positiveFacetCount_eq_three_of_central5 E t hcentral
  exact conePositiveRule_of_count y xij xik xjk (hcount.symm.trans hthree)

end Hypertournaments
