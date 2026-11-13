import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Hypertournaments.Basic

/-!
# Explicit integer Bernoulli bounds for the p3 random obstruction

The finite p3 proof uses M=2^m independent trials per group.
A single trial is forbidden on exactly one out of M equally likely
finite outcomes, so the number of M-trial all-avoiding patterns is
(M-1)^M out of M^M. Bernoulli's inequality proves the strict
integer estimate
  2*(M-1)^M < M^M  (M>=2).

For K independent groups, this amplifies to
  2^K*(M-1)^(M*K) < M^(M*K).
Consequently, if K>=D+1, even the union over 2^D possible gauges
occupies less than HALF the full finite sample space:
  2^(D+1)*(M-1)^(M*K) < M^(M*K).

All results are strict inequalities of NATURAL NUMBERS,
not analytic probability statements. The separate p3 witness
parameter lemma ensures K is large compared with the number
D=binom(m*t,m-2) of gauges.
-/

namespace Hypertournaments

/-- After M independent M-way trials each with one forbidden outcome,
strictly fewer than half of the M^M assignments avoid all forbidden
outcomes, for every M>=2. This is Bernoulli's inequality in Nat. -/
theorem p3Bernoulli_Mtrials_strict_half
    (M : ℕ) (hM : 2 ≤ M) :
    2 * (M-1)^M < M^M := by
  let a : ℕ := M-1
  have ha : 0 < a := by dsimp [a]; omega
  have hM_eq : M = a+1 := by dsimp [a]; omega
  have hApos : (0 : ℝ) ≤ (a : ℝ) := by positivity
  have hTwo : (0 : ℝ) ≤ 2 * (a : ℝ) + 1 := by positivity
  have hBern :
      (a : ℝ)^M + (M : ℝ) * (a : ℝ)^(M-1) * 1 ≤
        ((a : ℝ) + 1)^M :=
    pow_add_mul_le_add_pow hApos hTwo M
  have hpos : 0 < (a : ℝ)^(M-1) :=
    pow_pos (by exact_mod_cast ha) _
  have hltA : (a : ℝ) < (M : ℝ) := by
    have hnat : a < M := by omega
    exact_mod_cast hnat
  have hmPow : (a : ℝ)^M = (a : ℝ)^(M-1) * a := by
    nth_rewrite 1 [hM_eq]
    rw [pow_succ]
  have hstrict :
      (a : ℝ)^M < (M : ℝ) * (a : ℝ)^(M-1) := by
    have hmul :=
      mul_lt_mul_of_pos_left hltA hpos
    rw [hmPow]
    nlinarith
  have hreal : (2 : ℝ) * (a : ℝ)^M < (M : ℝ)^M := by
    have heq : (a : ℝ)+1 = M := by
      exact_mod_cast hM_eq.symm
    rw [heq] at hBern
    nlinarith
  change 2 * a^M < M^M
  exact_mod_cast hreal

/-- Repeating K>=1 independent blocks of M trials amplifies the
strict half bound by K factors. -/
theorem p3Bernoulli_Kgroups_integer
    (M K : ℕ) (hM : 2 ≤ M) (hK : 0 < K) :
    2^K * (M-1)^(M*K) < M^(M*K) := by
  have hbase := p3Bernoulli_Mtrials_strict_half M hM
  have hpow : (2 * (M-1)^M)^K < (M^M)^K := by
    gcongr
  calc
    2^K * (M-1)^(M*K) =
        (2 * (M-1)^M)^K := by rw [mul_pow, pow_mul]
    _ < (M^M)^K := hpow
    _ = M^(M*K) := by rw [pow_mul]

/-- A union over 2^D gauges has strictly less than half the total
space whenever there are at least D+1 independent M-trial groups. -/
theorem p3Bernoulli_gauge_union_strict_half
    (M K D : ℕ) (hM : 2 ≤ M) (hK : 0 < K)
    (hDK : D+1 ≤ K) :
    2^(D+1) * (M-1)^(M*K) < M^(M*K) := by
  have hp : 2^(D+1) ≤ 2^K := by gcongr
  have hbound := p3Bernoulli_Kgroups_integer M K hM hK
  have hmul :
      2^(D+1) * (M-1)^(M*K) ≤
        2^K * (M-1)^(M*K) :=
    Nat.mul_le_mul_right _ hp
  exact lt_of_le_of_lt hmul hbound

end Hypertournaments
