import Hypertournaments.FiniteCertificates.SeedFourRaw
import Hypertournaments.SeedFourForbidOneLogic

/-!
# Unpacked 15-Boolean unsatisfiability certificate

This is the same twenty local constraints as in
`forbidOne_fifteen_bit_unsat`, but expressed directly on fifteen
Boolean inputs rather than via a 10-bit/5-bit numerical encoding.

There is no reliance on source tuple orientations here. The point is
to allow a later semantic proof to substitute those orientations
directly without proving separate bit-packing arithmetic lemmas.
-/

namespace Hypertournaments

set_option maxRecDepth 16384
set_option maxHeartbeats 8000000

/-- Indices 0..9 stand for 12,13,14,15,23,24,25,34,35,45.
Indices 10..14 stand for 01,02,03,04,05. -/
def rawTopOk (b : Fin 15 → Bool) : Bool :=
  ruleT  (b 0) (b 1) (b 4) &&
  ruleT  (b 0) (b 2) (b 5) &&
  ruleT  (b 0) (b 3) (b 6) &&
  ruleCm (b 1) (b 2) (b 7) &&
  ruleCp (b 1) (b 3) (b 8) &&
  ruleT  (b 2) (b 3) (b 9) &&
  ruleT  (b 4) (b 5) (b 7) &&
  ruleCp (b 4) (b 6) (b 8) &&
  ruleCm (b 5) (b 6) (b 9) &&
  ruleT  (b 7) (b 8) (b 9)

/-- Ten additional constraints involving base vertex 0. -/
def rawOuterOk (b : Fin 15 → Bool) : Bool :=
  ruleCm (b 10) (b 11) (b 0) &&
  ruleT  (b 10) (b 12) (b 1) &&
  ruleT  (b 10) (b 13) (b 2) &&
  ruleT  (b 10) (b 14) (b 3) &&
  ruleT  (b 11) (b 12) (b 4) &&
  ruleT  (b 11) (b 13) (b 5) &&
  ruleT  (b 11) (b 14) (b 6) &&
  ruleCm (b 12) (b 13) (b 7) &&
  ruleT  (b 12) (b 14) (b 8) &&
  ruleCm (b 13) (b 14) (b 9)

private theorem ruleT_cnf : ∀ a b c : Bool,
    ruleT a b c = true →
    (¬ (¬ (a = true) ∧ (b = true) ∧ ¬ (c = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ (c = true))) := by
  intro a b c
  unfold ruleT
  cases a <;> cases b <;> cases c <;> decide +kernel

private theorem ruleCm_cnf : ∀ a b c : Bool,
    ruleCm a b c = true →
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ (c = true))) ∧
    (¬ ((a = true) ∧ ¬ (b = true) ∧ ¬ (c = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ (c = true))) := by
  intro a b c
  unfold ruleCm
  cases a <;> cases b <;> cases c <;> decide +kernel

private theorem ruleCp_cnf : ∀ a b c : Bool,
    ruleCp a b c = true →
    (¬ (¬ (a = true) ∧ ¬ (b = true) ∧ ¬ (c = true))) ∧
    (¬ (¬ (a = true) ∧ (b = true) ∧ (c = true))) ∧
    (¬ ((a = true) ∧ (b = true) ∧ ¬ (c = true))) := by
  intro a b c
  unfold ruleCp
  cases a <;> cases b <;> cases c <;> decide +kernel

/-- All 2^15 bit assignments are impossible. The already certified
17-pattern factorization in `SeedFourForbidOneLogic` remains available
as the human-readable compact certificate. -/
theorem no_raw_forbidOne_assignment :
    ∀ b : Fin 15 → Bool, rawTopOk b = true → rawOuterOk b = true → False := by
  intro b htop houter
  simp only [rawTopOk, rawOuterOk, Bool.and_eq_true, and_assoc] at htop houter
  rcases htop with ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
  rcases houter with ⟨h10, h11, h12, h13, h14, h15, h16, h17, h18, h19⟩
  obtain ⟨h0_0, h0_1⟩ := (ruleT_cnf (b 0) (b 1) (b 4)) h0
  obtain ⟨h1_0, h1_1⟩ := (ruleT_cnf (b 0) (b 2) (b 5)) h1
  obtain ⟨h2_0, h2_1⟩ := (ruleT_cnf (b 0) (b 3) (b 6)) h2
  obtain ⟨h3_0, h3_1, h3_2⟩ := (ruleCm_cnf (b 1) (b 2) (b 7)) h3
  obtain ⟨h4_0, h4_1, h4_2⟩ := (ruleCp_cnf (b 1) (b 3) (b 8)) h4
  obtain ⟨h5_0, h5_1⟩ := (ruleT_cnf (b 2) (b 3) (b 9)) h5
  obtain ⟨h6_0, h6_1⟩ := (ruleT_cnf (b 4) (b 5) (b 7)) h6
  obtain ⟨h7_0, h7_1, h7_2⟩ := (ruleCp_cnf (b 4) (b 6) (b 8)) h7
  obtain ⟨h8_0, h8_1, h8_2⟩ := (ruleCm_cnf (b 5) (b 6) (b 9)) h8
  obtain ⟨h9_0, h9_1⟩ := (ruleT_cnf (b 7) (b 8) (b 9)) h9
  obtain ⟨h10_0, h10_1, h10_2⟩ := (ruleCm_cnf (b 10) (b 11) (b 0)) h10
  obtain ⟨h11_0, h11_1⟩ := (ruleT_cnf (b 10) (b 12) (b 1)) h11
  obtain ⟨h12_0, h12_1⟩ := (ruleT_cnf (b 10) (b 13) (b 2)) h12
  obtain ⟨h13_0, h13_1⟩ := (ruleT_cnf (b 10) (b 14) (b 3)) h13
  obtain ⟨h14_0, h14_1⟩ := (ruleT_cnf (b 11) (b 12) (b 4)) h14
  obtain ⟨h15_0, h15_1⟩ := (ruleT_cnf (b 11) (b 13) (b 5)) h15
  obtain ⟨h16_0, h16_1⟩ := (ruleT_cnf (b 11) (b 14) (b 6)) h16
  obtain ⟨h17_0, h17_1, h17_2⟩ := (ruleCm_cnf (b 12) (b 13) (b 7)) h17
  obtain ⟨h18_0, h18_1⟩ := (ruleT_cnf (b 12) (b 14) (b 8)) h18
  obtain ⟨h19_0, h19_1, h19_2⟩ := (ruleCm_cnf (b 13) (b 14) (b 9)) h19
  rcases FiniteCertificates.SeedFourRaw (b 0 = true) (b 1 = true) (b 2 = true) (b 3 = true) (b 4 = true) (b 5 = true) (b 6 = true) (b 7 = true) (b 8 = true) (b 9 = true) (b 10 = true) (b 11 = true) (b 12 = true) (b 13 = true) (b 14 = true) with
    (((((h0 | h1) | (h2 | (h3 | h4))) | ((h5 | (h6 | h7)) | (h8 | (h9 | h10)))) | (((h11 | (h12 | h13)) | (h14 | (h15 | h16))) | ((h17 | (h18 | h19)) | (h20 | (h21 | h22))))) | ((((h23 | (h24 | h25)) | (h26 | (h27 | h28))) | ((h29 | (h30 | h31)) | (h32 | (h33 | h34)))) | (((h35 | (h36 | h37)) | (h38 | (h39 | h40))) | ((h41 | (h42 | h43)) | (h44 | (h45 | h46))))))
  · exact h0_0 h0
  · exact h0_1 h1
  · exact h1_0 h2
  · exact h1_1 h3
  · exact h2_0 h4
  · exact h2_1 h5
  · exact h3_0 h6
  · exact h3_1 h7
  · exact h3_2 h8
  · exact h4_0 h9
  · exact h4_1 h10
  · exact h4_2 h11
  · exact h5_0 h12
  · exact h5_1 h13
  · exact h6_0 h14
  · exact h6_1 h15
  · exact h7_0 h16
  · exact h7_1 h17
  · exact h7_2 h18
  · exact h8_0 h19
  · exact h8_1 h20
  · exact h8_2 h21
  · exact h9_0 h22
  · exact h9_1 h23
  · exact h10_0 h24
  · exact h10_1 h25
  · exact h10_2 h26
  · exact h11_0 h27
  · exact h11_1 h28
  · exact h12_0 h29
  · exact h12_1 h30
  · exact h13_0 h31
  · exact h13_1 h32
  · exact h14_0 h33
  · exact h14_1 h34
  · exact h15_0 h35
  · exact h15_1 h36
  · exact h16_0 h37
  · exact h16_1 h38
  · exact h17_0 h39
  · exact h17_1 h40
  · exact h17_2 h41
  · exact h18_0 h42
  · exact h18_1 h43
  · exact h19_0 h44
  · exact h19_1 h45
  · exact h19_2 h46

end Hypertournaments
