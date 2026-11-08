import Hypertournaments.Cochain

/-!
# Squaring the unsigned coboundary

An explicit proof of δ² = 0 over F₂. Every ordered pair of
distinct deleted vertices occurs twice, and the two contributions
cancel in characteristic two. The proof uses only finite sums.
-/

namespace Hypertournaments

universe u

private theorem add_self_eq_zero_mod_two (x : ZMod 2) : x + x = 0 := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  calc
    x + x = (2 : ZMod 2) * x := by ring
    _ = 0 := by simp [htwo]

/-- In characteristic two, a symmetric sum over distinct ordered
pairs vanishes, since each unordered pair occurs twice. -/
theorem sum_over_distinct_pairs_eq_zero
    {V : Type u} [DecidableEq V]
    (s : Finset V) (F : V → V → ZMod 2)
    (hF : ∀ x y, F x y = F y x) :
    (∑ x ∈ s, ∑ y ∈ s.erase x, F x y) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      calc
        (∑ x ∈ insert a s, ∑ y ∈ (insert a s).erase x, F x y) =
            (∑ y ∈ s, F a y) +
              ∑ x ∈ s, (F x a + ∑ y ∈ s.erase x, F x y) := by
          rw [Finset.sum_insert ha, Finset.erase_insert ha]
          congr 1
          apply Finset.sum_congr rfl
          intro x hx
          have hax : a ≠ x := by
            intro h
            exact ha (h ▸ hx)
          have hnot : a ∉ s.erase x := by
            simp [ha]
          rw [Finset.erase_insert_of_ne hax, Finset.sum_insert hnot]
        _ = (∑ y ∈ s, F a y) +
              ((∑ x ∈ s, F x a) +
                (∑ x ∈ s, ∑ y ∈ s.erase x, F x y)) := by
          rw [Finset.sum_add_distrib]
        _ = (∑ y ∈ s, F a y) + (∑ y ∈ s, F a y) := by
          rw [ih, add_zero]
          congr 1
          exact Finset.sum_congr rfl (fun x _ => hF x a)
        _ = 0 := add_self_eq_zero_mod_two _

/-- The unsigned simplex coboundary squares to zero. -/
theorem coboundary_coboundary_zero
    {V : Type u} [DecidableEq V]
    (g : Finset V → ZMod 2) (s : Finset V) :
    coboundary (coboundary g) s = 0 := by
  classical
  change (∑ x ∈ s, ∑ y ∈ s.erase x, g ((s.erase x).erase y)) = 0
  apply sum_over_distinct_pairs_eq_zero s
      (fun x y => g ((s.erase x).erase y))
  intro x y
  congr 1
  ext z
  simp only [Finset.mem_erase]
  tauto

end Hypertournaments
