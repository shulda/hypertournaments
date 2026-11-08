import Hypertournaments.SeedFourAdmissible
import Hypertournaments.DirectCertificateBridge

/-!
# Reflection soundness for arity-four direct finite-set certificates

A compact reusable interface: if every 5-subset passes a Boolean
check on its four-facet sign table, then the corresponding
intrinsic 4-hypertournament belongs to the intended age.

The allowed set S is arbitrary, not restricted to the central type.
-/

namespace Hypertournaments

theorem admissible_four_of_canonical_set
    {k : ℕ} (A : Hyper 4 (Fin k)) (S : Set ℕ)
    (h : ∀ Q : Finset (Fin k), ∀ hQ : Q.card = 5,
      localIndex A (Q.orderEmbOfFin hQ).toEmbedding ∈ S) :
    Admissible S A := by
  intro f
  let Q : Finset (Fin k) := tupleVertices f
  have hQ : Q.card = 5 := by
    dsimp [Q, tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  let g : Fin 5 ↪o Fin k := Q.orderEmbOfFin hQ
  let τ : Equiv.Perm (Fin 5) := Tuple.sort (f : Fin 5 → Fin k)
  have hmono : Monotone ((f : Fin 5 → Fin k) ∘ τ) :=
    Tuple.monotone_sort (f : Fin 5 → Fin k)
  have hinj : Function.Injective ((f : Fin 5 → Fin k) ∘ τ) :=
    f.injective.comp τ.injective
  have hsorted : (f : Fin 5 → Fin k) ∘ τ = (g : Fin 5 → Fin k) := by
    exact Finset.orderEmbOfFin_unique hQ (by
      intro i
      change f (τ i) ∈ Q
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _))
      (hmono.strictMono_of_injective hinj)
  have hreorder : τ.symm.toEmbedding.trans g.toEmbedding = f := by
    ext x
    have hx := congrFun hsorted (τ.symm x)
    exact congrArg Fin.val (by simpa [Function.comp_apply] using hx.symm)
  have hg : localIndex A g.toEmbedding ∈ S := h Q hQ
  have heq : localIndex A f = localIndex A g.toEmbedding := by
    calc
      localIndex A f =
          localIndex A (τ.symm.toEmbedding.trans g.toEmbedding) := by rw [hreorder]
      _ = localIndex A g.toEmbedding := localIndex_perm4 A g.toEmbedding τ.symm
  exact heq ▸ hg

/-- Any direct finite-set verifier whose rank-based local types
belong to S certifies ordinary admissibility for all injective
tuples, not just the canonical increasing representatives. -/
theorem fromOrderedSigns_admissible_of_direct
    {k : ℕ} (signs : Finset (Fin k) → Bool) (S : Set ℕ)
    (h : ∀ Q : Finset (Fin k), Q.card = 5 →
      min (directFacetPositiveCount signs Q)
          (5 - directFacetPositiveCount signs Q) ∈ S) :
    Admissible S (Hyper.fromOrderedSigns (n := 4) signs) := by
  apply admissible_four_of_canonical_set
    (Hyper.fromOrderedSigns (n := 4) signs) S
  intro Q hQ
  rw [localIndex_ordered_sign,
    ← directCount_eq_increasingPacket signs Q hQ]
  exact h Q hQ

end Hypertournaments
