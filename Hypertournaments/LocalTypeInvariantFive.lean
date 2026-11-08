import Hypertournaments.AdjacentSignFive

/-!
# Full coordinate-permutation invariance in arity five

The group of permutations of the six packet coordinates is generated
by adjacent transpositions.  The proof upgrades the adjacent-swap
identity into intrinsic invariance under arbitrary relabeling.
-/

namespace Hypertournaments

/-- The local type of a six-vertex 5-hypertournament is independent
of the choice and ordering of its six vertex labels. -/
theorem localIndex_perm5
    {V : Type*} (D : Hyper 5 V)
    (f : Fin 6 ↪ V) (σ : Equiv.Perm (Fin 6)) :
    localIndex D (σ.toEmbedding.trans f) = localIndex D f := by
  let generators : Set (Equiv.Perm (Fin 6)) :=
    Set.range (fun p : Fin 5 => Equiv.swap p.castSucc p.succ)
  have hgen : Submonoid.closure generators = ⊤ := by
    exact Equiv.Perm.mclosure_swap_castSucc_succ 5
  have hall :
      ∀ τ : Equiv.Perm (Fin 6),
        τ ∈ Submonoid.closure generators →
          ∀ g : Fin 6 ↪ V,
            localIndex D (τ.toEmbedding.trans g) = localIndex D g := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
        obtain ⟨p, rfl⟩ := hx
        intro g
        exact localIndex_adjacentSwap5 D g p
    | one =>
        intro g
        have hh : ((1 : Equiv.Perm (Fin 6)).toEmbedding.trans g) = g := by
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
