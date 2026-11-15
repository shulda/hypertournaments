import Hypertournaments.GeneralLocalIndexInvariant

/-!
# Normalized packets under arbitrary coordinate permutations

A coordinate permutation permutes the normalized facets and may complement
the whole packet. The possible global complement does not change whether
a selected tail alternates.
-/

namespace Hypertournaments

theorem normalizedFacet_perm_up_to_complement
    {n : ℕ} {V : Type*} (A : Hyper n V) (f : Fin (n + 1) ↪ V)
    (σ : Equiv.Perm (Fin (n + 1))) :
    ∃ b : Bool, ∀ i,
      normalizedFacet A (σ.toEmbedding.trans f) i =
        Bool.xor b (normalizedFacet A f (σ i)) := by
  let generators : Set (Equiv.Perm (Fin (n + 1))) :=
    Set.range (fun p : Fin n => adjacentSwapCoord p)
  have hgen : Submonoid.closure generators = ⊤ :=
    Equiv.Perm.mclosure_swap_castSucc_succ n
  have hall : ∀ τ : Equiv.Perm (Fin (n + 1)),
      τ ∈ Submonoid.closure generators →
        ∀ g : Fin (n + 1) ↪ V, ∃ b : Bool, ∀ i,
          normalizedFacet A (τ.toEmbedding.trans g) i =
            Bool.xor b (normalizedFacet A g (τ i)) := by
    intro τ hτ
    induction hτ using Submonoid.closure_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      intro g
      refine ⟨true, ?_⟩
      intro i
      rw [normalizedFacet_adjacent_swap]
      cases normalizedFacet A g (adjacentSwapCoord p i) <;> rfl
    | one =>
      intro g
      have hh : (1 : Equiv.Perm (Fin (n + 1))).toEmbedding.trans g = g := by
        ext i
        rfl
      refine ⟨false, ?_⟩
      intro i
      simp [hh]
    | mul x y hx hy ihx ihy =>
      intro g
      obtain ⟨bx, hbx⟩ := ihx g
      obtain ⟨cy, hby⟩ := ihy (x.toEmbedding.trans g)
      have hcomp : (x * y).toEmbedding.trans g =
          y.toEmbedding.trans (x.toEmbedding.trans g) := by
        ext i
        rfl
      refine ⟨Bool.xor cy bx, ?_⟩
      intro i
      rw [hcomp, hby, hbx]
      change Bool.xor cy (Bool.xor bx (normalizedFacet A g (x (y i)))) =
        Bool.xor (Bool.xor cy bx) (normalizedFacet A g (x (y i)))
      cases cy <;> cases bx <;> cases normalizedFacet A g (x (y i)) <;> rfl
  apply hall σ
  rw [hgen]
  trivial

end Hypertournaments
