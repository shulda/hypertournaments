import Hypertournaments.OddToggleP1RawAlternating

/-!
# Protected opposite-parity zero facets exclude the homogeneous type

A genuine homogeneous packet has alternating raw facet signs, with
one common phase. Hence it is impossible for two facets at indices
of opposite parity to have the same raw sign. This is the exact
local nonhomogeneity certificate used in the p3 random one-point
side construction: the block-support argument must locate two
protected zero facets of opposite parity on every (n+1)-set.

The criterion is intrinsic, valid in all arities, and does not
presuppose any probabilistic or side-admissibility conclusion.
-/

namespace Hypertournaments

/-- Two actual facets of opposite parity with the same raw Boolean
orientation force a genuinely nonhomogeneous local packet. -/
theorem Hyper.localIndex_ne_zero_of_oppositeParity_equalRaw
    {n : ℕ} {V : Type*} [LinearOrder V]
    (A : Hyper n V) (f : Fin (n+1) ↪o V)
    (i j : Fin (n+1))
    (hpar : decide (i.val%2=1) ≠ decide (j.val%2=1))
    (hsame : A.orient (facet f.toEmbedding i) =
             A.orient (facet f.toEmbedding j)) :
    localIndex A f.toEmbedding ≠ 0 := by
  intro hz
  obtain ⟨b, hb⟩ := A.localIndex_zero_raw_alternating f hz
  have hxor : (b ^^ decide (i.val%2=1)) =
      (b ^^ decide (j.val%2=1)) := by
    exact (hb i).symm.trans (hsame.trans (hb j))
  cases b <;>
    cases hi : decide (i.val%2=1) <;>
    cases hj : decide (j.val%2=1) <;>
    simp_all

/-- A protected pair of actual zero facets at opposite parity
positions is already sufficient to exclude homogeneous local type. -/
theorem Hyper.localIndex_ne_zero_of_oppositeParity_zeroRaw
    {n : ℕ} {V : Type*} [LinearOrder V]
    (A : Hyper n V) (f : Fin (n+1) ↪o V)
    (i j : Fin (n+1))
    (hpar : decide (i.val%2=1) ≠ decide (j.val%2=1))
    (hi : A.orient (facet f.toEmbedding i) = false)
    (hj : A.orient (facet f.toEmbedding j) = false) :
    localIndex A f.toEmbedding ≠ 0 := by
  exact A.localIndex_ne_zero_of_oppositeParity_equalRaw
    f i j hpar (hi.trans hj.symm)

/-- The same opposite-parity zero certificate can be read entirely
in the genuine canonical unordered n-set orientation table. -/
theorem Hyper.localIndex_ne_zero_of_oppositeParity_zeroCanonical
    {n a : ℕ}
    (A : Hyper n (Fin a)) (f : Fin (n+1) ↪o Fin a)
    (i j : Fin (n+1))
    (hpar : decide (i.val%2=1) ≠ decide (j.val%2=1))
    (hi : A.canonicalSignTable
        (tupleVertices (facet f.toEmbedding i)) = false)
    (hj : A.canonicalSignTable
        (tupleVertices (facet f.toEmbedding j)) = false) :
    localIndex A f.toEmbedding ≠ 0 := by
  intro hz
  obtain ⟨b, hb⟩ :=
    A.localIndex_zero_canonical_sign_alternating f hz
  have hxor : (b ^^ decide (i.val%2=1)) =
      (b ^^ decide (j.val%2=1)) := by
    exact (hb i).symm.trans (hi.trans (hj.symm.trans (hb j)))
  cases b <;>
    cases hpi : decide (i.val%2=1) <;>
    cases hpj : decide (j.val%2=1) <;>
    simp_all

end Hypertournaments
