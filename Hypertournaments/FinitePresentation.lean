import Hypertournaments.Basic

/-!
# Ordered sign presentations of intrinsic hypertournaments

Given a linear order on V, the permutation that sorts any injective
tuple changes parity under a transposition of its indices.
This is the key tool for importing the explicit positive-sign
catalogues in the mathematical technical note without naming the
auxiliary linear order in the final hypertournament language.
-/

namespace Hypertournaments

variable {n : ℕ} {V : Type*} [LinearOrder V]

/-- Sorting a tuple after swapping coordinates swaps the sorting
permutation on the left. The hypothesis that the tuple is injective
is essential for uniqueness of the sorting permutation. -/
theorem sort_swap_embedding (f : Fin n ↪ V) (i j : Fin n) :
    Tuple.sort (fun x => f (Equiv.swap i j x)) =
      Equiv.swap i j * Tuple.sort (f : Fin n → V) := by
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  have hsorted :
      ((f : Fin n → V) ∘ σ) ∘ Tuple.sort ((f : Fin n → V) ∘ σ) =
        (f : Fin n → V) ∘ Tuple.sort (f : Fin n → V) :=
    Tuple.comp_perm_comp_sort_eq_comp_sort
  have hperm :
      σ * Tuple.sort ((f : Fin n → V) ∘ σ) =
        Tuple.sort (f : Fin n → V) := by
    ext x
    apply f.injective
    simpa only [Function.comp_apply, Equiv.Perm.mul_apply]
      using congrFun hsorted x
  have hcancel := congrArg (fun p : Equiv.Perm (Fin n) => σ⁻¹ * p) hperm
  simpa [σ, mul_assoc] using hcancel

/-- Swapping distinct coordinates negates the sign of the
sorting permutation. -/
theorem sort_swap_sign (f : Fin n ↪ V) (i j : Fin n) (hij : i ≠ j) :
    (Tuple.sort (fun x => f (Equiv.swap i j x))).sign =
      - (Tuple.sort (f : Fin n → V)).sign := by
  rw [sort_swap_embedding, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  simp

end Hypertournaments
