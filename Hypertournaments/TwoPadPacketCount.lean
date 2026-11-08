import Hypertournaments.TwoPadIntrinsic

/-!
# Counting Boolean normalized facets with two prefixed pad coordinates

This gives the exact finite combinatorial statement needed for the
two-coordinate reflection lemma. The new (n+3)-facet packet has
two initial signs of opposite parity and the remaining (n+1) signs
are the old packet. Its positive count increases by exactly one,
and its intrinsic minority index consequently increases by one.

Unlike a mere numerical min identity, these theorems take the actual
Boolean facet sequences and prove the cardinality formula uniformly
in arity. The identification of real hypertournament facets with
this Boolean packet will be established in a later module.
-/

namespace Hypertournaments

/-- Positive entries of a Boolean finite packet. -/
def boolPacketPositiveCount {m : ℕ} (bits : Fin m → Bool) : ℕ :=
  (Finset.univ.filter (fun i => bits i = true)).card

/-- The Boolean positive-count statistic is the sum of its 0/1
indicators, giving a convenient interface to Fin.sum_univ_succ. -/
theorem boolPacketPositiveCount_eq_sum
    {m : ℕ} (bits : Fin m → Bool) :
    boolPacketPositiveCount bits =
      ∑ i : Fin m, (if bits i then (1 : ℕ) else 0) := by
  classical
  unfold boolPacketPositiveCount
  simp only [Finset.card_eq_sum_ones]
  rw [← Finset.sum_filter]

/-- The positive count of a packet with a new first facet. -/
theorem boolPacketPositiveCount_cons
    {m : ℕ} (a : Bool) (bits : Fin m → Bool) :
    boolPacketPositiveCount (Fin.cons a bits) =
      (if a then 1 else 0) + boolPacketPositiveCount bits := by
  rw [boolPacketPositiveCount_eq_sum, Fin.sum_univ_succ,
    boolPacketPositiveCount_eq_sum]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- Two arbitrary prefixed signs contribute the sum of their
indicator values. -/
theorem boolPacketPositiveCount_two_cons
    {m : ℕ} (a b : Bool) (bits : Fin m → Bool) :
    boolPacketPositiveCount (Fin.cons a (Fin.cons b bits)) =
      (if a then 1 else 0) + (if b then 1 else 0) +
        boolPacketPositiveCount bits := by
  rw [boolPacketPositiveCount_cons, boolPacketPositiveCount_cons]
  omega

/-- Exactly one of two opposite Boolean signs is positive. -/
theorem boolPacketPositiveCount_opposite
    {m : ℕ} (a b : Bool) (bits : Fin m → Bool)
    (hab : a ≠ b) :
    boolPacketPositiveCount (Fin.cons a (Fin.cons b bits)) =
      boolPacketPositiveCount bits + 1 := by
  rw [boolPacketPositiveCount_two_cons]
  cases a <;> cases b <;> simp_all <;> omega

/-- A Boolean packet's count is bounded by the number of facets. -/
theorem boolPacketPositiveCount_le
    {m : ℕ} (bits : Fin m → Bool) :
    boolPacketPositiveCount bits ≤ m := by
  unfold boolPacketPositiveCount
  simpa using
    (Finset.card_filter_le (Finset.univ : Finset (Fin m))
      (fun i => bits i = true))

/-- The precise minority-index shift for an old n+1 packet after
prepending one positive and one negative facet. -/
theorem boolPacketMinority_two_opposite
    {n : ℕ} (a b : Bool) (bits : Fin (n + 1) → Bool)
    (hab : a ≠ b) :
    min (boolPacketPositiveCount (Fin.cons a (Fin.cons b bits)))
      ((n + 3) - boolPacketPositiveCount (Fin.cons a (Fin.cons b bits))) =
      min (boolPacketPositiveCount bits)
        ((n + 1) - boolPacketPositiveCount bits) + 1 := by
  have hshift := boolPacketPositiveCount_opposite a b bits hab
  have hbound := boolPacketPositiveCount_le bits
  omega

end Hypertournaments
