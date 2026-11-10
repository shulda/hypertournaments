import Hypertournaments.Basic

/-!
# Exact finite parameter arithmetic in the p3 probabilistic obstruction

The mathematical proof for n ≡ 3 (mod 4) uses m=n-1≥6,
M=2^m and a deliberately large block size t=2^(m+1)*m^(m-2).
It selects t^(m-1) zero-sum transversals and divides them into
K=2*(m*t)^(m-2) groups of M transversals. The equality M*K=t^(m-1)
is exact, independent of probability theory, and is verified here
symbolically for all m≥2.

This does not establish the probabilistic construction, admissibility
of its sides, or non-amalgamation by itself.
-/

namespace Hypertournaments

def p3WitnessBlockSize (m : ℕ) : ℕ :=
  2^(m+1) * m^(m-2)

def p3WitnessTrialGroupSize (m : ℕ) : ℕ :=
  2^m

def p3WitnessTrialGroupCount (m : ℕ) : ℕ :=
  2 * (m * p3WitnessBlockSize m)^(m-2)

/-- The block-size parameter is positive in the only relevant
range (and is, in particular, a legal positive cyclic modulus). -/
theorem p3WitnessBlockSize_pos (m : ℕ) (hm : 2 ≤ m) :
    0 < p3WitnessBlockSize m := by
  have hmpos : 0 < m := by omega
  unfold p3WitnessBlockSize
  positivity

/-- The chosen number of zero-sum transversals decomposes exactly
into blocks of 2^m trials, with twice the relevant monomial count
of blocks. No asymptotic inequality is used. -/
theorem p3WitnessTrialPartition (m : ℕ) (hm : 2 ≤ m) :
    (p3WitnessBlockSize m)^(m-1) =
      p3WitnessTrialGroupSize m * p3WitnessTrialGroupCount m := by
  let t : ℕ := p3WitnessBlockSize m
  have ht : t = (2^m)*2*m^(m-2) := by
    dsimp [t, p3WitnessBlockSize]
    rw [pow_succ]
    ring
  change t^(m-1) = (2^m) * (2 * (m*t)^(m-2))
  have hm1 : m-1 = (m-2)+1 := by omega
  calc
    t^(m-1) = t^(m-2)*t := by rw [hm1, pow_succ]
    _ = t^(m-2)*((2^m)*2*m^(m-2)) :=
      congrArg (fun z : ℕ => t^(m-2)*z) ht
    _ = (2^m)*(2*(m*t)^(m-2)) := by
      rw [mul_pow]
      ring

end Hypertournaments
