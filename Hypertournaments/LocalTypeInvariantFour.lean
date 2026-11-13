import Mathlib.Tactic.Ext
import Hypertournaments.AdjacentSignFour

/-!
# Invariance of the arity-four local type under all coordinate permutations

Mathlib proves that the finite symmetric group is generated, as a
monoid, by adjacent transpositions. We use that elementary theorem
to upgrade the kernel-checked adjacent-swap formula to arbitrary
reorderings of a five-tuple.

This is an intrinsic invariance theorem for all 4-hypertournaments,
not just the explicit seed.
-/

namespace Hypertournaments

theorem localIndex_perm4
    {V : Type*} (D : Hyper 4 V)
    (f : Fin 5 ↪ V) (σ : Equiv.Perm (Fin 5)) :
    localIndex D (σ.toEmbedding.trans f) = localIndex D f := by
  let generators : Set (Equiv.Perm (Fin 5)) :=
    Set.range (fun p : Fin 4 => Equiv.swap p.castSucc p.succ)
  have hgen : Submonoid.closure generators = ⊤ := by
    exact Equiv.Perm.mclosure_swap_castSucc_succ 4
  have hall :
      ∀ τ : Equiv.Perm (Fin 5),
        τ ∈ Submonoid.closure generators →
          ∀ g : Fin 5 ↪ V,
            localIndex D (τ.toEmbedding.trans g) = localIndex D g := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
        obtain ⟨p, rfl⟩ := hx
        intro g
        exact localIndex_adjacentSwap4 D g p
    | one =>
        intro g
        have hh : ((1 : Equiv.Perm (Fin 5)).toEmbedding.trans g) = g := by
          ext i
          rfl
        rw [hh]
    | mul x y hx hy ihx ihy =>
        intro g
        have hcomp :
            (x * y).toEmbedding.trans g =
              y.toEmbedding.trans (x.toEmbedding.trans g) := by
          ext i
          rfl
        rw [hcomp, ihy (x.toEmbedding.trans g), ihx g]
  apply hall σ
  rw [hgen]
  trivial

end Hypertournaments
