import Hypertournaments.OddToggleP3FiniteBernoulliBound
import Hypertournaments.OddToggleP3WitnessParameters

/-!
# The explicit p3 witness parameters beat the finite gauge union bound

The probabilistic obstruction uses m=n-1>=6, M=2^m, block size
t=2^(m+1)*m^(m-2), and K=2*(m*t)^(m-2) groups of M independent
zero-sum transversals. There are at most
  2^D, D = (m*t).choose(m-2)
possible mixed gauge cochains on old (m-2)-subsets.

The existing witness-partition theorem proves t^(m-1)=M*K
exactly. Nat.choose_le_pow gives D<= (m*t)^(m-2), so the
explicit choice K>=D+1. The Bernoulli M-trial estimate then
yields the strict all-Nat inequality
  2^(D+1)*(M-1)^(t^(m-1)) < M^(t^(m-1)).
This is precisely the finite strict LESS THAN ONE HALF bound
needed to combine the gauge union bound with the independent
nonidentification event of probability one half.

These are numerical prerequisites only: no assertion of random
side age or ordinary non-amalgamation is made in this module.
-/

namespace Hypertournaments

/-- The explicit number of independent trial groups beats by at
least one the exponent of the number of possible p3 gauge cochains. -/
theorem p3Witness_gaugeExponent_lt_groups
    (m : ℕ) (hm : 2 ≤ m) :
    (m*p3WitnessBlockSize m).choose (m-2) + 1 ≤
      p3WitnessTrialGroupCount m := by
  let t : ℕ := p3WitnessBlockSize m
  let C : ℕ := (m*t)^(m-2)
  have ht : 0 < t := p3WitnessBlockSize_pos m hm
  have hmt : 0 < m*t := by
    have hmpos : 0 < m := by omega
    positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hchoose : (m*t).choose (m-2) ≤ C :=
    Nat.choose_le_pow _ _
  change (m*t).choose (m-2)+1 ≤ 2*C
  omega

/-- A nontrivial p3 trial group has at least two equally likely
possible outcomes, for every m>=2. -/
theorem p3Witness_trialGroupSize_ge_two
    (m : ℕ) (hm : 2 ≤ m) :
    2 ≤ p3WitnessTrialGroupSize m := by
  change 2 ≤ 2^m
  have hmpos : 0 < m := by omega
  rcases m with _ | q
  · omega
  · rw [pow_succ]
    have hp : 0 < 2^q := pow_pos (by decide) _
    omega

/-- The exact selected-trial integer count yields a strict
less-than-half gauge union bound for the explicit finite witness. -/
theorem p3Witness_finiteGaugeUnion_strict_half
    (m : ℕ) (hm : 2 ≤ m) :
    2 ^ (((m*p3WitnessBlockSize m).choose (m-2)) + 1) *
      ((p3WitnessTrialGroupSize m) - 1) ^
        ((p3WitnessBlockSize m)^(m-1)) <
      (p3WitnessTrialGroupSize m) ^
        ((p3WitnessBlockSize m)^(m-1)) := by
  have hM := p3Witness_trialGroupSize_ge_two m hm
  have hK : 0 < p3WitnessTrialGroupCount m := by
    have ht : 0 < p3WitnessBlockSize m :=
      p3WitnessBlockSize_pos m hm
    unfold p3WitnessTrialGroupCount
    positivity
  have hDK := p3Witness_gaugeExponent_lt_groups m hm
  have hBern := p3Bernoulli_gauge_union_strict_half
    (p3WitnessTrialGroupSize m)
    (p3WitnessTrialGroupCount m)
    ((m*p3WitnessBlockSize m).choose (m-2)) hM hK hDK
  have hpartition : (p3WitnessBlockSize m)^(m-1) =
    p3WitnessTrialGroupSize m * p3WitnessTrialGroupCount m :=
      p3WitnessTrialPartition m hm
  rw [← hpartition] at hBern
  exact hBern

end Hypertournaments
