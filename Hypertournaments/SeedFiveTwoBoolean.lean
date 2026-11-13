import Hypertournaments.FiniteCertificates.SeedFiveTwo
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

set_option maxRecDepth 16384
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

private theorem seed5TwoRuleSame_cnf : ∀ a b c d : Bool,
    seed5TwoRuleSame a b c d →
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ (c = true) ∧ ¬ (d = true))) := by
  intro a b c d
  unfold seed5TwoRuleSame
  cases a <;> cases b <;> cases c <;> cases d <;> simp

private theorem seed5TwoRuleZeroOne_cnf : ∀ a b c d : Bool,
    seed5TwoRuleZeroOne a b c d →
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ (c = true) ∧ (d = true))) := by
  intro a b c d
  unfold seed5TwoRuleZeroOne
  cases a <;> cases b <;> cases c <;> cases d <;> simp

private theorem seed5TwoRuleOneZero_cnf : ∀ a b c d : Bool,
    seed5TwoRuleOneZero a b c d →
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ ¬ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ (c = true) ∧ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ ¬ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ (c = true) ∧ ¬ (d = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ (c = true) ∧ (d = true))) := by
  intro a b c d
  unfold seed5TwoRuleOneZero
  cases a <;> cases b <;> cases c <;> cases d <;> simp

/-- Unconditional finite impossibility of satisfying these twenty
mixed six-packet constraints. The SAT proof is checked by Lean
by reducing the LRAT checker in the Lean kernel. -/
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
  obtain ⟨h0125_0, h0125_1, h0125_2, h0125_3, h0125_4, h0125_5, h0125_6, h0125_7, h0125_8, h0125_9, h0125_10⟩ := (seed5TwoRuleZeroOne_cnf (x 0) (x 3) (x 7) (x 17)) h0125
  obtain ⟨h0134_0, h0134_1, h0134_2, h0134_3, h0134_4, h0134_5, h0134_6, h0134_7, h0134_8, h0134_9, h0134_10⟩ := (seed5TwoRuleOneZero_cnf (x 1) (x 2) (x 9) (x 19)) h0134
  obtain ⟨h0136_0, h0136_1, h0136_2, h0136_3, h0136_4, h0136_5, h0136_6, h0136_7, h0136_8, h0136_9⟩ := (seed5TwoRuleSame_cnf (x 1) (x 4) (x 11) (x 21)) h0136
  obtain ⟨h0156_0, h0156_1, h0156_2, h0156_3, h0156_4, h0156_5, h0156_6, h0156_7, h0156_8, h0156_9, h0156_10⟩ := (seed5TwoRuleOneZero_cnf (x 3) (x 4) (x 14) (x 24)) h0156
  obtain ⟨h0235_0, h0235_1, h0235_2, h0235_3, h0235_4, h0235_5, h0235_6, h0235_7, h0235_8, h0235_9⟩ := (seed5TwoRuleSame_cnf (x 5) (x 7) (x 10) (x 26)) h0235
  obtain ⟨h0236_0, h0236_1, h0236_2, h0236_3, h0236_4, h0236_5, h0236_6, h0236_7, h0236_8, h0236_9, h0236_10⟩ := (seed5TwoRuleOneZero_cnf (x 5) (x 8) (x 11) (x 27)) h0236
  obtain ⟨h0246_0, h0246_1, h0246_2, h0246_3, h0246_4, h0246_5, h0246_6, h0246_7, h0246_8, h0246_9⟩ := (seed5TwoRuleSame_cnf (x 6) (x 8) (x 13) (x 29)) h0246
  obtain ⟨h0256_0, h0256_1, h0256_2, h0256_3, h0256_4, h0256_5, h0256_6, h0256_7, h0256_8, h0256_9, h0256_10⟩ := (seed5TwoRuleOneZero_cnf (x 7) (x 8) (x 14) (x 30)) h0256
  obtain ⟨h0345_0, h0345_1, h0345_2, h0345_3, h0345_4, h0345_5, h0345_6, h0345_7, h0345_8, h0345_9, h0345_10⟩ := (seed5TwoRuleZeroOne_cnf (x 9) (x 10) (x 12) (x 31)) h0345
  obtain ⟨h0356_0, h0356_1, h0356_2, h0356_3, h0356_4, h0356_5, h0356_6, h0356_7, h0356_8, h0356_9, h0356_10⟩ := (seed5TwoRuleOneZero_cnf (x 10) (x 11) (x 14) (x 33)) h0356
  obtain ⟨h0456_0, h0456_1, h0456_2, h0456_3, h0456_4, h0456_5, h0456_6, h0456_7, h0456_8, h0456_9⟩ := (seed5TwoRuleSame_cnf (x 12) (x 13) (x 14) (x 34)) h0456
  obtain ⟨h1236_0, h1236_1, h1236_2, h1236_3, h1236_4, h1236_5, h1236_6, h1236_7, h1236_8, h1236_9, h1236_10⟩ := (seed5TwoRuleOneZero_cnf (x 15) (x 18) (x 21) (x 27)) h1236
  obtain ⟨h1246_0, h1246_1, h1246_2, h1246_3, h1246_4, h1246_5, h1246_6, h1246_7, h1246_8, h1246_9⟩ := (seed5TwoRuleSame_cnf (x 16) (x 18) (x 23) (x 29)) h1246
  obtain ⟨h1256_0, h1256_1, h1256_2, h1256_3, h1256_4, h1256_5, h1256_6, h1256_7, h1256_8, h1256_9⟩ := (seed5TwoRuleSame_cnf (x 17) (x 18) (x 24) (x 30)) h1256
  obtain ⟨h1345_0, h1345_1, h1345_2, h1345_3, h1345_4, h1345_5, h1345_6, h1345_7, h1345_8, h1345_9⟩ := (seed5TwoRuleSame_cnf (x 19) (x 20) (x 22) (x 31)) h1345
  obtain ⟨h1356_0, h1356_1, h1356_2, h1356_3, h1356_4, h1356_5, h1356_6, h1356_7, h1356_8, h1356_9, h1356_10⟩ := (seed5TwoRuleOneZero_cnf (x 20) (x 21) (x 24) (x 33)) h1356
  obtain ⟨h1456_0, h1456_1, h1456_2, h1456_3, h1456_4, h1456_5, h1456_6, h1456_7, h1456_8, h1456_9, h1456_10⟩ := (seed5TwoRuleOneZero_cnf (x 22) (x 23) (x 24) (x 34)) h1456
  obtain ⟨h2345_0, h2345_1, h2345_2, h2345_3, h2345_4, h2345_5, h2345_6, h2345_7, h2345_8, h2345_9⟩ := (seed5TwoRuleSame_cnf (x 25) (x 26) (x 28) (x 31)) h2345
  obtain ⟨h2346_0, h2346_1, h2346_2, h2346_3, h2346_4, h2346_5, h2346_6, h2346_7, h2346_8, h2346_9, h2346_10⟩ := (seed5TwoRuleOneZero_cnf (x 25) (x 27) (x 29) (x 32)) h2346
  obtain ⟨h2456_0, h2456_1, h2456_2, h2456_3, h2456_4, h2456_5, h2456_6, h2456_7, h2456_8, h2456_9⟩ := (seed5TwoRuleSame_cnf (x 28) (x 29) (x 30) (x 34)) h2456
  rcases FiniteCertificates.SeedFiveTwo (x 0 = true) (x 1 = true) (x 2 = true) (x 3 = true) (x 4 = true) (x 5 = true) (x 6 = true) (x 7 = true) (x 8 = true) (x 9 = true) (x 10 = true) (x 11 = true) (x 12 = true) (x 13 = true) (x 14 = true) (x 15 = true) (x 16 = true) (x 17 = true) (x 18 = true) (x 19 = true) (x 20 = true) (x 21 = true) (x 22 = true) (x 23 = true) (x 24 = true) (x 25 = true) (x 26 = true) (x 27 = true) (x 28 = true) (x 29 = true) (x 30 = true) (x 31 = true) (x 32 = true) (x 33 = true) (x 34 = true) with
    (((((((h0 | (h1 | h2)) | (h3 | (h4 | h5))) | ((h6 | (h7 | h8)) | ((h9 | h10) | (h11 | h12)))) | (((h13 | (h14 | h15)) | (h16 | (h17 | h18))) | ((h19 | (h20 | h21)) | ((h22 | h23) | (h24 | h25))))) | ((((h26 | (h27 | h28)) | (h29 | (h30 | h31))) | ((h32 | (h33 | h34)) | ((h35 | h36) | (h37 | h38)))) | (((h39 | (h40 | h41)) | (h42 | (h43 | h44))) | ((h45 | (h46 | h47)) | ((h48 | h49) | (h50 | h51)))))) | (((((h52 | (h53 | h54)) | (h55 | (h56 | h57))) | ((h58 | (h59 | h60)) | ((h61 | h62) | (h63 | h64)))) | (((h65 | (h66 | h67)) | (h68 | (h69 | h70))) | ((h71 | (h72 | h73)) | ((h74 | h75) | (h76 | h77))))) | ((((h78 | (h79 | h80)) | (h81 | (h82 | h83))) | ((h84 | (h85 | h86)) | ((h87 | h88) | (h89 | h90)))) | (((h91 | (h92 | h93)) | ((h94 | h95) | (h96 | h97))) | ((h98 | (h99 | h100)) | ((h101 | h102) | (h103 | h104))))))) | ((((((h105 | (h106 | h107)) | (h108 | (h109 | h110))) | ((h111 | (h112 | h113)) | ((h114 | h115) | (h116 | h117)))) | (((h118 | (h119 | h120)) | (h121 | (h122 | h123))) | ((h124 | (h125 | h126)) | ((h127 | h128) | (h129 | h130))))) | ((((h131 | (h132 | h133)) | (h134 | (h135 | h136))) | ((h137 | (h138 | h139)) | ((h140 | h141) | (h142 | h143)))) | (((h144 | (h145 | h146)) | ((h147 | h148) | (h149 | h150))) | ((h151 | (h152 | h153)) | ((h154 | h155) | (h156 | h157)))))) | (((((h158 | (h159 | h160)) | (h161 | (h162 | h163))) | ((h164 | (h165 | h166)) | ((h167 | h168) | (h169 | h170)))) | (((h171 | (h172 | h173)) | (h174 | (h175 | h176))) | ((h177 | (h178 | h179)) | ((h180 | h181) | (h182 | h183))))) | ((((h184 | (h185 | h186)) | (h187 | (h188 | h189))) | ((h190 | (h191 | h192)) | ((h193 | h194) | (h195 | h196)))) | (((h197 | (h198 | h199)) | ((h200 | h201) | (h202 | h203))) | ((h204 | (h205 | h206)) | ((h207 | h208) | (h209 | h210))))))))
  · exact h0125_0 h0
  · exact h0125_1 h1
  · exact h0125_2 h2
  · exact h0125_3 h3
  · exact h0125_4 h4
  · exact h0125_5 h5
  · exact h0125_6 h6
  · exact h0125_7 h7
  · exact h0125_8 h8
  · exact h0125_9 h9
  · exact h0125_10 h10
  · exact h0134_0 h11
  · exact h0134_1 h12
  · exact h0134_2 h13
  · exact h0134_3 h14
  · exact h0134_4 h15
  · exact h0134_5 h16
  · exact h0134_6 h17
  · exact h0134_7 h18
  · exact h0134_8 h19
  · exact h0134_9 h20
  · exact h0134_10 h21
  · exact h0136_0 h22
  · exact h0136_1 h23
  · exact h0136_2 h24
  · exact h0136_3 h25
  · exact h0136_4 h26
  · exact h0136_5 h27
  · exact h0136_6 h28
  · exact h0136_7 h29
  · exact h0136_8 h30
  · exact h0136_9 h31
  · exact h0156_0 h32
  · exact h0156_1 h33
  · exact h0156_2 h34
  · exact h0156_3 h35
  · exact h0156_4 h36
  · exact h0156_5 h37
  · exact h0156_6 h38
  · exact h0156_7 h39
  · exact h0156_8 h40
  · exact h0156_9 h41
  · exact h0156_10 h42
  · exact h0235_0 h43
  · exact h0235_1 h44
  · exact h0235_2 h45
  · exact h0235_3 h46
  · exact h0235_4 h47
  · exact h0235_5 h48
  · exact h0235_6 h49
  · exact h0235_7 h50
  · exact h0235_8 h51
  · exact h0235_9 h52
  · exact h0236_0 h53
  · exact h0236_1 h54
  · exact h0236_2 h55
  · exact h0236_3 h56
  · exact h0236_4 h57
  · exact h0236_5 h58
  · exact h0236_6 h59
  · exact h0236_7 h60
  · exact h0236_8 h61
  · exact h0236_9 h62
  · exact h0236_10 h63
  · exact h0246_0 h64
  · exact h0246_1 h65
  · exact h0246_2 h66
  · exact h0246_3 h67
  · exact h0246_4 h68
  · exact h0246_5 h69
  · exact h0246_6 h70
  · exact h0246_7 h71
  · exact h0246_8 h72
  · exact h0246_9 h73
  · exact h0256_0 h74
  · exact h0256_1 h75
  · exact h0256_2 h76
  · exact h0256_3 h77
  · exact h0256_4 h78
  · exact h0256_5 h79
  · exact h0256_6 h80
  · exact h0256_7 h81
  · exact h0256_8 h82
  · exact h0256_9 h83
  · exact h0256_10 h84
  · exact h0345_0 h85
  · exact h0345_1 h86
  · exact h0345_2 h87
  · exact h0345_3 h88
  · exact h0345_4 h89
  · exact h0345_5 h90
  · exact h0345_6 h91
  · exact h0345_7 h92
  · exact h0345_8 h93
  · exact h0345_9 h94
  · exact h0345_10 h95
  · exact h0356_0 h96
  · exact h0356_1 h97
  · exact h0356_2 h98
  · exact h0356_3 h99
  · exact h0356_4 h100
  · exact h0356_5 h101
  · exact h0356_6 h102
  · exact h0356_7 h103
  · exact h0356_8 h104
  · exact h0356_9 h105
  · exact h0356_10 h106
  · exact h0456_0 h107
  · exact h0456_1 h108
  · exact h0456_2 h109
  · exact h0456_3 h110
  · exact h0456_4 h111
  · exact h0456_5 h112
  · exact h0456_6 h113
  · exact h0456_7 h114
  · exact h0456_8 h115
  · exact h0456_9 h116
  · exact h1236_0 h117
  · exact h1236_1 h118
  · exact h1236_2 h119
  · exact h1236_3 h120
  · exact h1236_4 h121
  · exact h1236_5 h122
  · exact h1236_6 h123
  · exact h1236_7 h124
  · exact h1236_8 h125
  · exact h1236_9 h126
  · exact h1236_10 h127
  · exact h1246_0 h128
  · exact h1246_1 h129
  · exact h1246_2 h130
  · exact h1246_3 h131
  · exact h1246_4 h132
  · exact h1246_5 h133
  · exact h1246_6 h134
  · exact h1246_7 h135
  · exact h1246_8 h136
  · exact h1246_9 h137
  · exact h1256_0 h138
  · exact h1256_1 h139
  · exact h1256_2 h140
  · exact h1256_3 h141
  · exact h1256_4 h142
  · exact h1256_5 h143
  · exact h1256_6 h144
  · exact h1256_7 h145
  · exact h1256_8 h146
  · exact h1256_9 h147
  · exact h1345_0 h148
  · exact h1345_1 h149
  · exact h1345_2 h150
  · exact h1345_3 h151
  · exact h1345_4 h152
  · exact h1345_5 h153
  · exact h1345_6 h154
  · exact h1345_7 h155
  · exact h1345_8 h156
  · exact h1345_9 h157
  · exact h1356_0 h158
  · exact h1356_1 h159
  · exact h1356_2 h160
  · exact h1356_3 h161
  · exact h1356_4 h162
  · exact h1356_5 h163
  · exact h1356_6 h164
  · exact h1356_7 h165
  · exact h1356_8 h166
  · exact h1356_9 h167
  · exact h1356_10 h168
  · exact h1456_0 h169
  · exact h1456_1 h170
  · exact h1456_2 h171
  · exact h1456_3 h172
  · exact h1456_4 h173
  · exact h1456_5 h174
  · exact h1456_6 h175
  · exact h1456_7 h176
  · exact h1456_8 h177
  · exact h1456_9 h178
  · exact h1456_10 h179
  · exact h2345_0 h180
  · exact h2345_1 h181
  · exact h2345_2 h182
  · exact h2345_3 h183
  · exact h2345_4 h184
  · exact h2345_5 h185
  · exact h2345_6 h186
  · exact h2345_7 h187
  · exact h2345_8 h188
  · exact h2345_9 h189
  · exact h2346_0 h190
  · exact h2346_1 h191
  · exact h2346_2 h192
  · exact h2346_3 h193
  · exact h2346_4 h194
  · exact h2346_5 h195
  · exact h2346_6 h196
  · exact h2346_7 h197
  · exact h2346_8 h198
  · exact h2346_9 h199
  · exact h2346_10 h200
  · exact h2456_0 h201
  · exact h2456_1 h202
  · exact h2456_2 h203
  · exact h2456_3 h204
  · exact h2456_4 h205
  · exact h2456_5 h206
  · exact h2456_6 h207
  · exact h2456_7 h208
  · exact h2456_8 h209
  · exact h2456_9 h210

end Hypertournaments
