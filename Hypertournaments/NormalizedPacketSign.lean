import Hypertournaments.GeneralLocalIndexInvariant

/-!
# Exact permutation sign of the normalized facet packet

Normalized facets are permuted by the coordinate permutation. They are
simultaneously complemented exactly when that permutation is odd.
The formula holds in every arity, including zero and one.
-/

namespace Hypertournaments

/-- The Boolean parity of a permutation: true precisely for negative sign. -/
def permutationSignBit {m : ℕ} (σ : Equiv.Perm (Fin m)) : Bool :=
  decide (σ.sign ≠ (1 : ℤˣ))

@[simp] theorem permutationSignBit_one {m : ℕ} :
    permutationSignBit (1 : Equiv.Perm (Fin m)) = false := by
  simp [permutationSignBit]

theorem permutationSignBit_mul {m : ℕ} (σ τ : Equiv.Perm (Fin m)) :
    permutationSignBit (σ * τ) =
      Bool.xor (permutationSignBit σ) (permutationSignBit τ) := by
  rcases Int.units_eq_one_or σ.sign with hs | hs <;>
    rcases Int.units_eq_one_or τ.sign with ht | ht <;>
    simp [permutationSignBit, Equiv.Perm.sign_mul, hs, ht, Units.ext_iff]

@[simp] theorem permutationSignBit_swap {m : ℕ} (a b : Fin m) (hab : a ≠ b) :
    permutationSignBit (Equiv.swap a b) = true := by
  simp [permutationSignBit, Equiv.Perm.sign_swap hab, Units.ext_iff]

/-- Exact Boolean parity law for normalized facets under any permutation. -/
theorem normalizedFacet_perm_signBit
    {n : ℕ} {V : Type*} (A : Hyper n V) (f : Fin (n + 1) ↪ V)
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    normalizedFacet A (σ.toEmbedding.trans f) i =
      Bool.xor (permutationSignBit σ) (normalizedFacet A f (σ i)) := by
  let generators : Set (Equiv.Perm (Fin (n + 1))) :=
    Set.range (fun p : Fin n => adjacentSwapCoord p)
  have hgen : Submonoid.closure generators = ⊤ :=
    Equiv.Perm.mclosure_swap_castSucc_succ n
  have hall : ∀ τ : Equiv.Perm (Fin (n + 1)),
      τ ∈ Submonoid.closure generators →
        ∀ (g : Fin (n + 1) ↪ V) (j : Fin (n + 1)),
          normalizedFacet A (τ.toEmbedding.trans g) j =
            Bool.xor (permutationSignBit τ) (normalizedFacet A g (τ j)) := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      intro g j
      have hne : p.castSucc ≠ p.succ := by
        intro he
        have hh := congrArg Fin.val he
        simp only [Fin.val_castSucc, Fin.val_succ] at hh
        omega
      have hp : permutationSignBit (adjacentSwapCoord p) = true := by
        exact permutationSignBit_swap _ _ hne
      rw [normalizedFacet_adjacent_swap, hp]
      cases normalizedFacet A g (adjacentSwapCoord p j) <;> rfl
    | one =>
      intro g j
      have hh : (1 : Equiv.Perm (Fin (n + 1))).toEmbedding.trans g = g := by
        ext a
        rfl
      simp [hh]
    | mul x y hx hy ihx ihy =>
      intro g j
      have hcomp : (x * y).toEmbedding.trans g =
          y.toEmbedding.trans (x.toEmbedding.trans g) := by
        ext a
        rfl
      rw [hcomp, ihy, ihx, permutationSignBit_mul]
      change Bool.xor (permutationSignBit y)
        (Bool.xor (permutationSignBit x) (normalizedFacet A g (x (y j)))) =
        Bool.xor (Bool.xor (permutationSignBit x) (permutationSignBit y))
          (normalizedFacet A g (x (y j)))
      cases permutationSignBit x <;> cases permutationSignBit y <;>
        cases normalizedFacet A g (x (y j)) <;> rfl
  apply hall σ
  rw [hgen]
  trivial

/-- Equivalent sign-valued form of the normalized facet permutation law. -/
theorem normalizedFacet_perm
    {n : ℕ} {V : Type*} (A : Hyper n V) (f : Fin (n + 1) ↪ V)
    (σ : Equiv.Perm (Fin (n + 1))) (i : Fin (n + 1)) :
    normalizedFacet A (σ.toEmbedding.trans f) i =
      if σ.sign = (1 : ℤˣ) then normalizedFacet A f (σ i)
        else !(normalizedFacet A f (σ i)) := by
  rw [normalizedFacet_perm_signBit]
  by_cases hs : σ.sign = (1 : ℤˣ) <;> simp [permutationSignBit, hs]

/-- Every coordinate transposition complements and permutes the normalized
packet, including the two exchanged facet coordinates themselves. -/
theorem normalizedFacet_swap
    {n : ℕ} {V : Type*} (A : Hyper n V) (f : Fin (n + 1) ↪ V)
    (a b : Fin (n + 1)) (hab : a ≠ b) (i : Fin (n + 1)) :
    normalizedFacet A ((Equiv.swap a b).toEmbedding.trans f) i =
      !(normalizedFacet A f ((Equiv.swap a b) i)) := by
  rw [normalizedFacet_perm_signBit, permutationSignBit_swap a b hab]
  cases normalizedFacet A f ((Equiv.swap a b) i) <;> rfl

end Hypertournaments
