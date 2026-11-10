import Hypertournaments.OddToggleP3ZeroSumCode

/-!
# Exact cardinality of finite zero-sum transversal codes

For an additive commutative group G, the last coordinate of a
zero-sum tuple is uniquely determined by the first m coordinates.
We express this as a genuine equivalence, not just a pigeonhole
bound. If G is finite, the code on m+1 coordinates has size
|G|^m. Taking G=ZMod t yields the t^m selected zero-sum
transversals needed in the p3 probabilistic non-AP construction.

This is only a finite combinatorial code statement, not an
assertion that the random hypertournament diagram is admissible.
-/

namespace Hypertournaments

/-- Append the unique last group coordinate making the total sum
of an (m+1)-tuple equal to zero. -/
def p3ZeroSumExtend {G : Type*} [AddCommGroup G]
    (m : ℕ) (f : Fin m → G) : Fin (m+1) → G :=
  Fin.snoc f (-(∑ i : Fin m, f i))

theorem p3ZeroSumExtend_sum_zero {G : Type*} [AddCommGroup G]
    (m : ℕ) (f : Fin m → G) :
    (∑ i : Fin (m+1), p3ZeroSumExtend m f i) = 0 := by
  rw [Fin.sum_univ_castSucc]
  simp [p3ZeroSumExtend]

/-- Zero-sum tuples of length m+1 are in bijection with arbitrary
group-valued tuples of length m. -/
def p3ZeroSumTupleEquiv {G : Type*} [AddCommGroup G] (m : ℕ) :
    (Fin m → G) ≃
      {f : Fin (m+1) → G // (∑ i : Fin (m+1), f i) = 0} where
  toFun f := ⟨p3ZeroSumExtend m f, p3ZeroSumExtend_sum_zero m f⟩
  invFun g := fun i => g.1 i.castSucc
  left_inv f := by
    funext i
    simp [p3ZeroSumExtend]
  right_inv g := by
    apply Subtype.ext
    funext i
    rcases i.eq_castSucc_or_eq_last with ⟨j, rfl⟩ | rfl
    · simp [p3ZeroSumExtend]
    · have hz : (∑ j : Fin m, g.1 j.castSucc) +
          g.1 (Fin.last m) = 0 := by
        simpa only [Fin.sum_univ_castSucc] using g.2
      have hlast : -(∑ j : Fin m, g.1 j.castSucc) =
          g.1 (Fin.last m) := by
        calc
          -(∑ j : Fin m, g.1 j.castSucc) =
              g.1 (Fin.last m) -
                ((∑ j : Fin m, g.1 j.castSucc) +
                  g.1 (Fin.last m)) := by abel
          _ = g.1 (Fin.last m) - 0 := by rw [hz]
          _ = g.1 (Fin.last m) := sub_zero _
      simpa [p3ZeroSumExtend] using hlast

/-- There are exactly |G|^m zero-sum words of length m+1,
for every finite additive commutative group G. -/
theorem p3ZeroSumTuple_card {G : Type*}
    [AddCommGroup G] [Fintype G] [DecidableEq G] (m : ℕ) :
    Fintype.card
      {f : Fin (m+1) → G // (∑ i : Fin (m+1), f i) = 0} =
        (Fintype.card G)^m := by
  classical
  calc
    Fintype.card
        {f : Fin (m+1) → G // (∑ i : Fin (m+1), f i) = 0} =
      Fintype.card (Fin m → G) :=
        Fintype.card_congr (p3ZeroSumTupleEquiv m).symm
    _ = (Fintype.card G)^m := by simp

end Hypertournaments
