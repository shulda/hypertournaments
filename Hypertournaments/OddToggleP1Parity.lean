import Hypertournaments.DoubleCoboundary

/-!
# The double-coboundary parity half of the zero-or-two principle

Over ZMod 2, if a subset X of a finite parent has its homogeneous
indicator equal to the unsigned boundary of the raw orientation
cochain, then the number of homogeneous deleted facets is even.

This is a uniform finite result, not restricted to a particular
hypertournament arity. The proof invokes the already kernel-checked
coboundary_coboundary_zero; its only additional ingredient is the
finite sum of Boolean indicators. The identification of a concrete
localIndex-zero packet with a coboundary value is separate.
-/

namespace Hypertournaments

/-- Summing unit indicators over a finite set computes the
cardinality of the corresponding predicate filter in ZMod 2. -/
theorem p1SumIndicator_mod2 {V : Type*} [DecidableEq V]
    (Z : Finset V) (H : V → Prop) [DecidablePred H] :
    (∑ i ∈ Z, (if H i then (1 : ZMod 2) else 0)) =
      ((Z.filter H).card : ZMod 2) := by
  classical
  calc
    (∑ i ∈ Z, (if H i then (1 : ZMod 2) else 0)) =
        ∑ i ∈ Z.filter H, (1 : ZMod 2) := by
      rw [Finset.sum_filter]
    _ = ((Z.filter H).card : ZMod 2) := by
      simp

/-- Every finite family of deleted facets whose indicator is given
by an unsigned coboundary has even cardinality in ZMod 2. -/
theorem p1Cochain_homogeneous_count_even
    {V : Type*} [DecidableEq V]
    (Z : Finset V) (e : Finset V → ZMod 2)
    (H : V → Prop) [DecidablePred H]
    (hindicator : ∀ i ∈ Z,
      (if H i then (1 : ZMod 2) else 0) =
        coboundary e (Z.erase i)) :
    ((Z.filter H).card : ZMod 2) = 0 := by
  classical
  have hsum :
      (∑ i ∈ Z, (if H i then (1 : ZMod 2) else 0)) =
        ∑ i ∈ Z, coboundary e (Z.erase i) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hindicator i hi
  calc
    ((Z.filter H).card : ZMod 2) =
        ∑ i ∈ Z, (if H i then (1 : ZMod 2) else 0) :=
      (p1SumIndicator_mod2 Z H).symm
    _ = ∑ i ∈ Z, coboundary e (Z.erase i) := hsum
    _ = coboundary (coboundary e) Z := rfl
    _ = 0 := coboundary_coboundary_zero e Z

/-- If the homogeneous-facet count is at most two and its
ZMod 2 value is zero, exactly zero or two facets are homogeneous. -/
theorem p1Even_card_le_two_eq_zero_or_two
    (c : ℕ) (hle : c ≤ 2) (heven : (c : ZMod 2) = 0) :
    c = 0 ∨ c = 2 := by
  have hcases : c = 0 ∨ c = 1 ∨ c = 2 := by omega
  rcases hcases with h0 | h1 | h2
  · exact Or.inl h0
  · have hone : (1 : ZMod 2) = 0 := by
      simpa [h1] using heven
    exact False.elim ((by decide : (1 : ZMod 2) ≠ 0) hone)
  · exact Or.inr h2

end Hypertournaments
