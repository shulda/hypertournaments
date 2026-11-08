import Hypertournaments.SeedFiveTwoBoolean
import Hypertournaments.OnePointJoint

/-!
# Local five-ary packet semantics for mixed ordinary amalgams

Given the orientations of the two endpoint facets and the four mixed
inner facets of an ordered six-tuple, the local index is 0 or 3
exactly when the corresponding finite Boolean rule holds.

This module contains no specific finite witness.  It is the bridge
from actual intrinsic local-type admissibility to the kernel-checked
Boolean UNSAT core in SeedFiveTwoBoolean.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- The Boolean rule selected by the two fixed endpoint signs. -/
def seed5TwoMixedRule (beta alpha a b c d : Bool) : Prop :=
  if beta = alpha then seed5TwoRuleSame a b c d
  else if beta = false then seed5TwoRuleZeroOne a b c d
  else seed5TwoRuleOneZero a b c d

/-- Number of positive normalized signs in the mixed six-facet
packet (beta, !d, c, !b, a, !alpha). -/
def seed5TwoMixedPositiveCount (beta alpha a b c d : Bool) : ℕ :=
  (Finset.univ.filter (fun i : Fin 6 =>
    (![beta, !d, c, !b, a, !alpha] : Fin 6 → Bool) i = true)).card

/-- Direct finite verification of the *exact* packet-rule interface. -/
theorem seed5TwoMixedAllowed_iff_rule
    (beta alpha a b c d : Bool) :
    (min (seed5TwoMixedPositiveCount beta alpha a b c d)
         (6 - seed5TwoMixedPositiveCount beta alpha a b c d) = 0 ∨
      min (seed5TwoMixedPositiveCount beta alpha a b c d)
         (6 - seed5TwoMixedPositiveCount beta alpha a b c d) = 3) ↔
      seed5TwoMixedRule beta alpha a b c d := by
  classical
  cases beta <;> cases alpha <;> cases a <;> cases b <;>
    cases c <;> cases d <;>
    norm_num [seed5TwoMixedRule, seed5TwoMixedPositiveCount,
      seed5TwoRuleSame, seed5TwoRuleZeroOne, seed5TwoRuleOneZero,
      Finset.univ]

/-- Any genuinely admissible mixed six-tuple satisfies its
corresponding Boolean packet rule, with no auxiliary linear order
assumed on the ambient hypertournament. -/
theorem seed5TwoMixedRule_of_admissible
    {V : Type*} (E : Hyper 5 V) (t : Fin 6 ↪ V)
    (beta alpha a b c d : Bool)
    (h0 : E.orient (facet t 0) = beta)
    (h1 : E.orient (facet t 1) = d)
    (h2 : E.orient (facet t 2) = c)
    (h3 : E.orient (facet t 3) = b)
    (h4 : E.orient (facet t 4) = a)
    (h5 : E.orient (facet t 5) = alpha)
    (hallowed : localIndex E t ∈ ({0,3} : Set ℕ)) :
    seed5TwoMixedRule beta alpha a b c d := by
  have hfacet (i : Fin 6) :
      normalizedFacet E t i =
        (![beta, !d, c, !b, a, !alpha] : Fin 6 → Bool) i := by
    fin_cases i <;> simp [normalizedFacet, h0, h1, h2, h3, h4, h5]
  have hcount :
      positiveFacetCount E t =
        seed5TwoMixedPositiveCount beta alpha a b c d := by
    unfold positiveFacetCount seed5TwoMixedPositiveCount
    apply congrArg Finset.card
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rw [hfacet i]
  have hallowed' :
      min (seed5TwoMixedPositiveCount beta alpha a b c d)
          (6 - seed5TwoMixedPositiveCount beta alpha a b c d) = 0 ∨
      min (seed5TwoMixedPositiveCount beta alpha a b c d)
          (6 - seed5TwoMixedPositiveCount beta alpha a b c d) = 3 := by
    simpa [localIndex, hcount, Set.mem_insert_iff, Set.mem_singleton_iff]
      using hallowed
  exact (seed5TwoMixedAllowed_iff_rule beta alpha a b c d).mp hallowed'

end Hypertournaments
