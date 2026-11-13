import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring
import Hypertournaments.OddToggleP3WitnessHalfBound

/-!
# Explicit finite strict gauge bound for complete W/link source words

The existing witness arithmetic bounds bad-gauge events using
M = 2^m outcomes per zero-sum transversal and N = t^(m-1)
independent trials, where t = 2^(m+1)*m^(m-2).

The actual finite source words have m+1 independent bits each,
and exactly TWO forbidden words out of 2^(m+1). Multiplying
numerator and denominator by 2^N converts the already certified
Bernoulli bound into the EXACT integer inequality for the full
source words:
  2^(D+1) * (2^(m+1)-2)^N < 2^((m+1)*N),
  D=choose(m*t,m-2).

This is the numerical input to the finite denominator-free gauge
union bound; no abstract probability axiom or AP conclusion.
-/

namespace Hypertournaments

/-- The fully specified p3 witness parameters make even the
union over 2^D gauges occupy strictly less than HALF the
independent full W/link source words. -/
theorem p3Witness_fullSourceGauge_strict_half
    (m : ℕ) (hm : 2 ≤ m) :
    2 ^ (((m*p3WitnessBlockSize m).choose (m-2)) + 1) *
      (2^(m+1)-2) ^ ((p3WitnessBlockSize m)^(m-1)) <
    2 ^ ((m+1)*((p3WitnessBlockSize m)^(m-1))) := by
  let t : ℕ := p3WitnessBlockSize m
  let N : ℕ := t^(m-1)
  let D : ℕ := (m*t).choose (m-2)
  have hNum :
      2^(D+1)*(2^m-1)^N < (2^m)^N := by
    simpa only [t, N, D, p3WitnessTrialGroupSize] using
      (p3Witness_finiteGaugeUnion_strict_half m hm)
  have hTwo : 2^(m+1)-2 = 2*(2^m-1) := by
    have hpos : 0 < (2:ℕ)^m := pow_pos (by decide) _
    rw [pow_succ]
    omega
  have hTwoPower : 0 < (2:ℕ)^N := pow_pos (by decide) _
  have hscaled :
      (2^(D+1)*(2^m-1)^N) * 2^N <
        ((2^m)^N) * 2^N :=
    mul_lt_mul_of_pos_right hNum hTwoPower
  change 2^(D+1)*(2^(m+1)-2)^N < 2^((m+1)*N)
  calc
    2^(D+1)*(2^(m+1)-2)^N =
        2^(D+1)*(2*(2^m-1))^N := by rw [hTwo]
    _ = (2^(D+1)*(2^m-1)^N)*2^N := by
      rw [mul_pow]
      ring
    _ < ((2^m)^N)*2^N := hscaled
    _ = 2^((m+1)*N) := by
      simp only [add_mul, one_mul, pow_add, pow_mul]

end Hypertournaments
