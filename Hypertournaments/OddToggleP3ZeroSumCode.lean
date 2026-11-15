import Hypertournaments.Basic

/-!
# Distance-two property of zero-sum transversals

The homogeneous-free exceptional family n ≡ 3 (mod 4) is handled in
the mathematical manuscript by a finite probabilistic construction.
Its independent transversals are tuples of cyclic coordinates whose
sum is zero. No two distinct such tuples can agree everywhere but
one coordinate: the final coordinate is forced by the sum equation.

This file proves the essential combinatorial code property over any
additive commutative group. Later the instance G = ZMod t gives the
selected transversals; the probabilistic argument and age verification
are not claimed here.
-/

namespace Hypertournaments

/-- Over an arbitrary additive commutative group, two zero-sum
tuples agreeing outside one coordinate are equal everywhere. -/
theorem p3ZeroSum_eq_of_agree_except
    {G : Type*} [AddCommGroup G] (m : ℕ)
    (f g : Fin (m+1) → G) (u : Fin (m+1))
    (hf : (∑ i : Fin (m+1), f i) = 0)
    (hg : (∑ i : Fin (m+1), g i) = 0)
    (hagree : ∀ i : Fin (m+1), i ≠ u → f i = g i) :
    f = g := by
  have hsum : (∑ i : Fin (m+1), (f i - g i)) = 0 := by
    rw [Finset.sum_sub_distrib, hf, hg, sub_self]
  have hone :
      (∑ i : Fin (m+1), (f i - g i)) = f u - g u := by
    apply Finset.sum_eq_single u
    · intro i _ hi
      rw [hagree i hi]
      exact sub_self _
    · intro hu
      exact False.elim (hu (Finset.mem_univ u))
  have hu : f u = g u :=
    sub_eq_zero.mp (hone.symm.trans hsum)
  funext i
  by_cases hi : i = u
  · subst i
    exact hu
  · exact hagree i hi

/-- Consequently any two distinct zero-sum tuples that disagree
at one coordinate must also disagree somewhere else. -/
theorem p3ZeroSum_second_disagreement
    {G : Type*} [AddCommGroup G] (m : ℕ)
    (f g : Fin (m+1) → G) (u : Fin (m+1))
    (hf : (∑ i : Fin (m+1), f i) = 0)
    (hg : (∑ i : Fin (m+1), g i) = 0)
    (hfg : f ≠ g) :
    ∃ v : Fin (m+1), v ≠ u ∧ f v ≠ g v := by
  by_contra hno
  have hagree : ∀ i : Fin (m+1), i ≠ u → f i = g i := by
    intro i hi
    by_contra hne
    exact hno ⟨i, hi, hne⟩
  exact hfg (p3ZeroSum_eq_of_agree_except m f g u hf hg hagree)

end Hypertournaments
