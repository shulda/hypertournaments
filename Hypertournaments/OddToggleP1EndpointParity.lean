import Hypertournaments.OddToggleP1RawAlternating

/-!
# Actual homogeneous-packet endpoint orientation constraints

The explicit n≡1 (mod 4) obstruction needs a local criterion for a
mixed packet to be homogeneous: its two known endpoint facet raw
signs must agree exactly when their deletion positions have the
same parity. This lemma holds in every arity and for every actual
intrinsic hypertournament packet with localIndex=0.

The sign convention uses genuine orientations, not any auxiliary
potential or guessed switching representative.
-/

namespace Hypertournaments

/-- In a genuinely homogeneous increasing packet, two raw facet
orientations coincide iff the deletion indices have the same
alternating parity. -/
theorem Hyper.localIndex_zero_rawFacet_eq_iff_parity_eq
    {n : ℕ} {V : Type*} [LinearOrder V]
    (A : Hyper n V) (f : Fin (n+1) ↪o V)
    (hzero : localIndex A f.toEmbedding = 0)
    (i j : Fin (n+1)) :
    (A.orient (facet f.toEmbedding i) =
      A.orient (facet f.toEmbedding j)) ↔
      (decide (i.val % 2 = 1) =
        decide (j.val % 2 = 1)) := by
  obtain ⟨b, hb⟩ := A.localIndex_zero_raw_alternating f hzero
  rw [hb i, hb j]
  cases b <;>
    cases hi : decide (i.val % 2 = 1) <;>
    cases hj : decide (j.val % 2 = 1) <;>
    simp [hi, hj]

/-- Opposite raw orientations are forced at deletion indices of
opposite parity, in a truly homogeneous packet. -/
theorem Hyper.localIndex_zero_rawFacet_ne_iff_parity_ne
    {n : ℕ} {V : Type*} [LinearOrder V]
    (A : Hyper n V) (f : Fin (n+1) ↪o V)
    (hzero : localIndex A f.toEmbedding = 0)
    (i j : Fin (n+1)) :
    (A.orient (facet f.toEmbedding i) ≠
      A.orient (facet f.toEmbedding j)) ↔
      (decide (i.val % 2 = 1) ≠
        decide (j.val % 2 = 1)) := by
  simpa only [ne_eq] using
    (A.localIndex_zero_rawFacet_eq_iff_parity_eq f hzero i j).not

end Hypertournaments
