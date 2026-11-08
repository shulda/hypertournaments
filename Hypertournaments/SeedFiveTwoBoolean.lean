import Hypertournaments.SeedFiveTwoData

/-!
# Finite Boolean obstruction for the first arity-five mixed case

The 35 variables x_T represent the oriented five-tuples
(left-new, i, j, k, right-new) for all triples i<j<k of the
seven old vertices.  We use lexicographic triple indices.

The side links fix the first and last facets of every mixed
six-packet.  For a quadruple a<b<c<d the remaining facets are
(!x_bcd, x_acd, !x_abd, x_abc).  The three following predicates
are the complete finite lists of permitted assignments when the
six-packet is homogeneous (type 0) or central (type 3).

The final SAT contradiction uses a *subset* of twenty mixed
quadruples, rather than the full thirty-five.  It is a genuine
Boolean UNSAT theorem; the later AP proof must separately connect
the finite rules to an arbitrary proposed amalgam.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

/-- Permitted mixed-facet assignments for link-endpoint pattern Same. -/
def seed5TwoRuleSame (a b c d : Bool) : Prop :=
  (a = false ∧ b = false ∧ c = false ∧ d = false) ∨
  (a = false ∧ b = false ∧ c = true ∧ d = true) ∨
  (a = false ∧ b = true ∧ c = true ∧ d = false) ∨
  (a = true ∧ b = false ∧ c = false ∧ d = true) ∨
  (a = true ∧ b = true ∧ c = false ∧ d = false) ∨
  (a = true ∧ b = true ∧ c = true ∧ d = true)

/-- Permitted mixed-facet assignments for link-endpoint pattern ZeroOne. -/
def seed5TwoRuleZeroOne (a b c d : Bool) : Prop :=
  (a = false ∧ b = false ∧ c = true ∧ d = false) ∨
  (a = false ∧ b = true ∧ c = false ∧ d = true) ∨
  (a = true ∧ b = false ∧ c = false ∧ d = false) ∨
  (a = true ∧ b = false ∧ c = true ∧ d = true) ∨
  (a = true ∧ b = true ∧ c = true ∧ d = false)

/-- Permitted mixed-facet assignments for link-endpoint pattern OneZero. -/
def seed5TwoRuleOneZero (a b c d : Bool) : Prop :=
  (a = false ∧ b = false ∧ c = false ∧ d = true) ∨
  (a = false ∧ b = true ∧ c = false ∧ d = false) ∨
  (a = false ∧ b = true ∧ c = true ∧ d = true) ∨
  (a = true ∧ b = false ∧ c = true ∧ d = false) ∨
  (a = true ∧ b = true ∧ c = false ∧ d = true)

/-- Unconditional finite impossibility of satisfying these twenty
mixed six-packet constraints. The SAT proof is checked by Lean
using the LRAT certificate produced by bv_decide. -/
theorem seed5Two_mixed_boolean_unsat
    (x : Fin 35 → Bool)
    (h0125 : seed5TwoRuleZeroOne (x 0) (x 3) (x 7) (x 17))
    (h0134 : seed5TwoRuleOneZero (x 1) (x 2) (x 9) (x 19))
    (h0136 : seed5TwoRuleSame (x 1) (x 4) (x 11) (x 21))
    (h0156 : seed5TwoRuleOneZero (x 3) (x 4) (x 14) (x 24))
    (h0235 : seed5TwoRuleSame (x 5) (x 7) (x 10) (x 26))
    (h0236 : seed5TwoRuleOneZero (x 5) (x 8) (x 11) (x 27))
    (h0246 : seed5TwoRuleSame (x 6) (x 8) (x 13) (x 29))
    (h0256 : seed5TwoRuleOneZero (x 7) (x 8) (x 14) (x 30))
    (h0345 : seed5TwoRuleZeroOne (x 9) (x 10) (x 12) (x 31))
    (h0356 : seed5TwoRuleOneZero (x 10) (x 11) (x 14) (x 33))
    (h0456 : seed5TwoRuleSame (x 12) (x 13) (x 14) (x 34))
    (h1236 : seed5TwoRuleOneZero (x 15) (x 18) (x 21) (x 27))
    (h1246 : seed5TwoRuleSame (x 16) (x 18) (x 23) (x 29))
    (h1256 : seed5TwoRuleSame (x 17) (x 18) (x 24) (x 30))
    (h1345 : seed5TwoRuleSame (x 19) (x 20) (x 22) (x 31))
    (h1356 : seed5TwoRuleOneZero (x 20) (x 21) (x 24) (x 33))
    (h1456 : seed5TwoRuleOneZero (x 22) (x 23) (x 24) (x 34))
    (h2345 : seed5TwoRuleSame (x 25) (x 26) (x 28) (x 31))
    (h2346 : seed5TwoRuleOneZero (x 25) (x 27) (x 29) (x 32))
    (h2456 : seed5TwoRuleSame (x 28) (x 29) (x 30) (x 34)) :
    False := by
  unfold seed5TwoRuleSame seed5TwoRuleZeroOne seed5TwoRuleOneZero at *
  bv_decide

end Hypertournaments
