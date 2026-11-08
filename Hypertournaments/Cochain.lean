import Mathlib

/-!
# The simplex cochain contraction in characteristic two

A completely elementary proof of exactness of cocycles on the full
simplex. We use the *unsigned* coboundary, which is appropriate
in characteristic two, and an explicitly defined cone at a vertex.

This does not depend on abstract algebraic topology or simplicial
homology theorems.
-/

namespace Hypertournaments

universe u

/-- The unsigned coboundary of a function on finite subsets over F₂. -/
def coboundary {V : Type u} [DecidableEq V]
    (g : Finset V → ZMod 2) (s : Finset V) : ZMod 2 :=
  ∑ x ∈ s, g (s.erase x)

/-- Contract a cochain toward a chosen vertex. -/
def contractAt {V : Type u} [DecidableEq V]
    (a : V) (g : Finset V → ZMod 2) (s : Finset V) : ZMod 2 :=
  if a ∈ s then 0 else g (insert a s)

private theorem zmod_two_neg_eq_self (x : ZMod 2) : -x = x := by
  have htwo : (2 : ZMod 2) = 0 := by decide
  calc
    -x = (1 - (2 : ZMod 2)) * x := by ring
    _ = x := by simp [htwo]

/-- Contracting at a vertex already in the set recovers the cochain. -/
theorem coboundary_contractAt_of_mem {V : Type u} [DecidableEq V]
    (a : V) (g : Finset V → ZMod 2) (s : Finset V)
    (ha : a ∈ s) :
    coboundary (contractAt a g) s = g s := by
  classical
  unfold coboundary
  rw [Finset.sum_eq_single a]
  · simp [contractAt, Finset.insert_erase ha]
  · intro b hb hba
    have hab : a ≠ b := Ne.symm hba
    have hmem : a ∈ s.erase b := Finset.mem_erase.mpr ⟨hab, ha⟩
    simp [contractAt, hmem]
  · intro hnot
    exact (hnot ha).elim

/-- When the cone vertex is outside the set, the coboundary of
g on the larger set is the sum of g on the smaller set and
the coboundary of the contracted cochain. -/
theorem coboundary_insert_eq_add_contractAt {V : Type u} [DecidableEq V]
    (a : V) (g : Finset V → ZMod 2) (s : Finset V)
    (ha : a ∉ s) :
    coboundary g (insert a s) =
      g s + coboundary (contractAt a g) s := by
  classical
  unfold coboundary
  rw [Finset.sum_insert ha, Finset.erase_insert ha]
  congr 1
  apply Finset.sum_congr rfl
  intro b hb
  have hab : a ≠ b := by
    intro h
    exact ha (h ▸ hb)
  rw [Finset.erase_insert_of_ne hab]
  have hnot : a ∉ s.erase b := by
    intro hmem
    exact ha (Finset.mem_of_mem_erase hmem)
  simp [contractAt, hnot]

/-- Every cochain closed in the next degree is an unsigned
coboundary in the specified degree. In particular, this supplies
the exactness part of the parity/switching argument without any
external cohomology theorem. -/
theorem cocycle_exact_at_card {V : Type u} [DecidableEq V]
    (a : V) (r : ℕ) (g : Finset V → ZMod 2)
    (hclosed : ∀ s : Finset V, s.card = r + 1 → coboundary g s = 0) :
    ∀ s : Finset V, s.card = r →
      coboundary (contractAt a g) s = g s := by
  intro s hs
  by_cases ha : a ∈ s
  · exact coboundary_contractAt_of_mem a g s ha
  · have hcard : (insert a s).card = r + 1 := by
      simp [ha, hs]
    have hz := hclosed (insert a s) hcard
    rw [coboundary_insert_eq_add_contractAt a g s ha] at hz
    have hneg : coboundary (contractAt a g) s = -g s :=
      eq_neg_of_add_eq_zero_right hz
    simpa [zmod_two_neg_eq_self] using hneg

end Hypertournaments
