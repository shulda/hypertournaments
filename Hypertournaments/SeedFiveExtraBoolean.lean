import Hypertournaments.SeedFiveExtraData

/-!
# A nine-packet unsatisfiable core for the exceptional arity-five class

This finite SAT certificate comes from the k=0 uniform 1 mod 4
obstruction.  There are 20 orientations of mixed five-tuples
(left-new, i, j, k, right-new). The complete diagram has fifteen
mixed six-packets, but only the nine listed below are needed.

The four middle bits are ordered x_abc, x_abd, x_acd, x_bcd for an
increasing old quadruple a<b<c<d.  The endpoint signs alpha/beta
select one of three rules.

Allowing local types 0,1,3 in arity five is equivalent to allowing
odd normalized positive counts 1,3,5, or the two homogeneous counts
0,6. The 'same endpoint' rule is XOR-even; unequal endpoints
require XOR-odd, except for one homogeneous alternating assignment.

This file certifies only the abstract Boolean obstruction.
The bridge to actual amalgamation is a separate proof obligation.
-/

namespace Hypertournaments

set_option maxRecDepth 8192
set_option maxHeartbeats 6000000

/-- Equal endpoint signs: admissibility forces even parity of
the four middle orientation bits. -/
def seed5ExtraRuleSame (a b c d : Bool) : Prop :=
  Bool.xor (Bool.xor a b) (Bool.xor c d) = false

/-- Right endpoint beta=0, left endpoint alpha=1:
odd parity or homogeneous all-zero normalized signs. -/
def seed5ExtraRuleZeroOne (a b c d : Bool) : Prop :=
  Bool.xor (Bool.xor a b) (Bool.xor c d) = true ∨
    (a = false ∧ b = true ∧ c = false ∧ d = true)

/-- Right endpoint beta=1, left endpoint alpha=0:
odd parity or homogeneous all-one normalized signs. -/
def seed5ExtraRuleOneZero (a b c d : Bool) : Prop :=
  Bool.xor (Bool.xor a b) (Bool.xor c d) = true ∨
    (a = true ∧ b = false ∧ c = true ∧ d = false)

/-- A finite certificate: the nine selected actual-link packet rules
have no simultaneous assignment of the twenty mixed orientations.
The bitvector SAT certificate is checked by the Lean kernel. -/
theorem seed5Extra_mixed_boolean_unsat
    (x : Fin 20 → Bool)
    (h0123 : seed5ExtraRuleSame (x 0) (x 1) (x 4) (x 10))
    (h0125 : seed5ExtraRuleSame (x 0) (x 3) (x 6) (x 12))
    (h0134 : seed5ExtraRuleOneZero (x 1) (x 2) (x 7) (x 13))
    (h0135 : seed5ExtraRuleZeroOne (x 1) (x 3) (x 8) (x 14))
    (h0145 : seed5ExtraRuleSame (x 2) (x 3) (x 9) (x 15))
    (h0235 : seed5ExtraRuleSame (x 4) (x 6) (x 8) (x 17))
    (h0345 : seed5ExtraRuleSame (x 7) (x 8) (x 9) (x 19))
    (h1235 : seed5ExtraRuleSame (x 10) (x 12) (x 14) (x 17))
    (h1345 : seed5ExtraRuleSame (x 13) (x 14) (x 15) (x 19)) :
    False := by
  unfold seed5ExtraRuleSame seed5ExtraRuleZeroOne
    seed5ExtraRuleOneZero at *
  bv_decide

end Hypertournaments
