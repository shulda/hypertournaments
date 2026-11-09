import Hypertournaments.GeneralAdjacentFacet
import Hypertournaments.UniformPacketPermutationCount

/-!
# Intrinsic invariance of the local hypertournament type

The exact all-arity facet law under adjacent swaps complements and
reorders the normalized packet. The uniform Boolean minority-count
identity then gives invariance under adjacent transpositions. Since
they generate all coordinate permutations, this proves full intrinsic
relabeling invariance of the local type for every arity.

No suspension, AP assumption, or finite fixed-arity enumeration is
used. The independent canonical-subset admissibility interface is
a subsequent consequence.
-/

namespace Hypertournaments

/-- Local index is invariant under any adjacent coordinate swap. -/
theorem localIndex_adjacent_swap_all
    {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V) (p : Fin n) :
    localIndex A ((adjacentSwapCoord p).toEmbedding.trans f) =
      localIndex A f := by
  let bits : Fin (n + 1) → Bool :=
    fun i => normalizedFacet A f i
  have hbits :
      (fun i : Fin (n + 1) =>
          normalizedFacet A
            ((adjacentSwapCoord p).toEmbedding.trans f) i) =
        (fun i => !(bits ((adjacentSwapCoord p) i))) := by
    funext i
    exact normalizedFacet_adjacent_swap A f p i
  change
    min
      (boolPacketPositiveCount
        (fun i : Fin (n + 1) =>
          normalizedFacet A
            ((adjacentSwapCoord p).toEmbedding.trans f) i))
      ((n + 1) -
        boolPacketPositiveCount
          (fun i : Fin (n + 1) =>
            normalizedFacet A
              ((adjacentSwapCoord p).toEmbedding.trans f) i)) =
      min (boolPacketPositiveCount bits)
        ((n + 1) - boolPacketPositiveCount bits)
  rw [hbits]
  exact boolPacketMinority_perm_complement bits (adjacentSwapCoord p)

/-- The local index is intrinsic under every permutation of the
(n+1) ordered tuple coordinates, uniformly in the arity n. -/
theorem localIndex_perm_all
    {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n + 1) ↪ V)
    (σ : Equiv.Perm (Fin (n + 1))) :
    localIndex A (σ.toEmbedding.trans f) = localIndex A f := by
  let generators : Set (Equiv.Perm (Fin (n + 1))) :=
    Set.range (fun p : Fin n => adjacentSwapCoord p)
  have hgen : Submonoid.closure generators = ⊤ := by
    exact Equiv.Perm.mclosure_swap_castSucc_succ n
  have hall :
      ∀ τ : Equiv.Perm (Fin (n + 1)),
        τ ∈ Submonoid.closure generators →
          ∀ g : Fin (n + 1) ↪ V,
            localIndex A (τ.toEmbedding.trans g) = localIndex A g := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
        obtain ⟨p, rfl⟩ := hx
        intro g
        exact localIndex_adjacent_swap_all A g p
    | one =>
        intro g
        have hh :
            ((1 : Equiv.Perm (Fin (n + 1))).toEmbedding.trans g) = g := by
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
