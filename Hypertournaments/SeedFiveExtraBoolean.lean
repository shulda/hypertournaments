import Hypertournaments.FiniteCertificates.SeedFiveExtra
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

set_option maxRecDepth 16384
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

private theorem seed5ExtraRuleSame_cnf : ∀ a b c d : Bool,
    seed5ExtraRuleSame a b c d →
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ (c = true) ∧ ¬ (d = true))) := by
  intro a b c d
  unfold seed5ExtraRuleSame
  cases a <;> cases b <;> cases c <;> cases d <;> simp

private theorem seed5ExtraRuleZeroOne_cnf : ∀ a b c d : Bool,
    seed5ExtraRuleZeroOne a b c d →
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ (c = true) ∧ (d = true))) := by
  intro a b c d
  unfold seed5ExtraRuleZeroOne
  cases a <;> cases b <;> cases c <;> cases d <;> simp

private theorem seed5ExtraRuleOneZero_cnf : ∀ a b c d : Bool,
    seed5ExtraRuleOneZero a b c d →
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ (c = true) ∧ (d = true))) := by
  intro a b c d
  unfold seed5ExtraRuleOneZero
  cases a <;> cases b <;> cases c <;> cases d <;> simp

/-- A finite certificate: the nine selected actual-link packet rules
have no simultaneous assignment of the twenty mixed orientations.
The LRAT certificate is checked by kernel reduction, without native-evaluation axioms. -/
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
  obtain ⟨h0123_0, h0123_1, h0123_2, h0123_3, h0123_4, h0123_5, h0123_6, h0123_7⟩ := (seed5ExtraRuleSame_cnf (x 0) (x 1) (x 4) (x 10)) h0123
  obtain ⟨h0125_0, h0125_1, h0125_2, h0125_3, h0125_4, h0125_5, h0125_6, h0125_7⟩ := (seed5ExtraRuleSame_cnf (x 0) (x 3) (x 6) (x 12)) h0125
  obtain ⟨h0134_0, h0134_1, h0134_2, h0134_3, h0134_4, h0134_5, h0134_6⟩ := (seed5ExtraRuleOneZero_cnf (x 1) (x 2) (x 7) (x 13)) h0134
  obtain ⟨h0135_0, h0135_1, h0135_2, h0135_3, h0135_4, h0135_5, h0135_6⟩ := (seed5ExtraRuleZeroOne_cnf (x 1) (x 3) (x 8) (x 14)) h0135
  obtain ⟨h0145_0, h0145_1, h0145_2, h0145_3, h0145_4, h0145_5, h0145_6, h0145_7⟩ := (seed5ExtraRuleSame_cnf (x 2) (x 3) (x 9) (x 15)) h0145
  obtain ⟨h0235_0, h0235_1, h0235_2, h0235_3, h0235_4, h0235_5, h0235_6, h0235_7⟩ := (seed5ExtraRuleSame_cnf (x 4) (x 6) (x 8) (x 17)) h0235
  obtain ⟨h0345_0, h0345_1, h0345_2, h0345_3, h0345_4, h0345_5, h0345_6, h0345_7⟩ := (seed5ExtraRuleSame_cnf (x 7) (x 8) (x 9) (x 19)) h0345
  obtain ⟨h1235_0, h1235_1, h1235_2, h1235_3, h1235_4, h1235_5, h1235_6, h1235_7⟩ := (seed5ExtraRuleSame_cnf (x 10) (x 12) (x 14) (x 17)) h1235
  obtain ⟨h1345_0, h1345_1, h1345_2, h1345_3, h1345_4, h1345_5, h1345_6, h1345_7⟩ := (seed5ExtraRuleSame_cnf (x 13) (x 14) (x 15) (x 19)) h1345
  rcases FiniteCertificates.SeedFiveExtra (x 0 = true) (x 1 = true) (x 2 = true) (x 3 = true) (x 4 = true) (x 5 = true) (x 6 = true) (x 7 = true) (x 8 = true) (x 9 = true) (x 10 = true) (x 11 = true) (x 12 = true) (x 13 = true) (x 14 = true) (x 15 = true) (x 16 = true) (x 17 = true) (x 18 = true) (x 19 = true) with
    ((((((h0 | h1) | (h2 | h3)) | ((h4 | h5) | (h6 | h7))) | (((h8 | h9) | (h10 | h11)) | ((h12 | h13) | (h14 | (h15 | h16))))) | ((((h17 | h18) | (h19 | h20)) | ((h21 | h22) | (h23 | (h24 | h25)))) | (((h26 | h27) | (h28 | h29)) | ((h30 | h31) | (h32 | (h33 | h34)))))) | (((((h35 | h36) | (h37 | h38)) | ((h39 | h40) | (h41 | h42))) | (((h43 | h44) | (h45 | h46)) | ((h47 | h48) | (h49 | (h50 | h51))))) | ((((h52 | h53) | (h54 | h55)) | ((h56 | h57) | (h58 | (h59 | h60)))) | (((h61 | h62) | (h63 | h64)) | ((h65 | h66) | (h67 | (h68 | h69)))))))
  · exact h0123_0 h0
  · exact h0123_1 h1
  · exact h0123_2 h2
  · exact h0123_3 h3
  · exact h0123_4 h4
  · exact h0123_5 h5
  · exact h0123_6 h6
  · exact h0123_7 h7
  · exact h0125_0 h8
  · exact h0125_1 h9
  · exact h0125_2 h10
  · exact h0125_3 h11
  · exact h0125_4 h12
  · exact h0125_5 h13
  · exact h0125_6 h14
  · exact h0125_7 h15
  · exact h0134_0 h16
  · exact h0134_1 h17
  · exact h0134_2 h18
  · exact h0134_3 h19
  · exact h0134_4 h20
  · exact h0134_5 h21
  · exact h0134_6 h22
  · exact h0135_0 h23
  · exact h0135_1 h24
  · exact h0135_2 h25
  · exact h0135_3 h26
  · exact h0135_4 h27
  · exact h0135_5 h28
  · exact h0135_6 h29
  · exact h0145_0 h30
  · exact h0145_1 h31
  · exact h0145_2 h32
  · exact h0145_3 h33
  · exact h0145_4 h34
  · exact h0145_5 h35
  · exact h0145_6 h36
  · exact h0145_7 h37
  · exact h0235_0 h38
  · exact h0235_1 h39
  · exact h0235_2 h40
  · exact h0235_3 h41
  · exact h0235_4 h42
  · exact h0235_5 h43
  · exact h0235_6 h44
  · exact h0235_7 h45
  · exact h0345_0 h46
  · exact h0345_1 h47
  · exact h0345_2 h48
  · exact h0345_3 h49
  · exact h0345_4 h50
  · exact h0345_5 h51
  · exact h0345_6 h52
  · exact h0345_7 h53
  · exact h1235_0 h54
  · exact h1235_1 h55
  · exact h1235_2 h56
  · exact h1235_3 h57
  · exact h1235_4 h58
  · exact h1235_5 h59
  · exact h1235_6 h60
  · exact h1235_7 h61
  · exact h1345_0 h62
  · exact h1345_1 h63
  · exact h1345_2 h64
  · exact h1345_3 h65
  · exact h1345_4 h66
  · exact h1345_5 h67
  · exact h1345_6 h68
  · exact h1345_7 h69

end Hypertournaments
