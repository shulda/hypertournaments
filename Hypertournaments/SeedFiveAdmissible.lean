import Hypertournaments.LocalTypeInvariantFive
import Hypertournaments.CanonicalPacket

/-!
# Reusable finite admissibility checks in arity five

An arbitrary injective six-tuple is a permutation of the canonical
increasing enumeration of its six-element vertex set.  Consequently,
checking local indices on canonical six-subsets suffices for ordinary
admissibility. This works for every allowed set S, not just a
particular arity-five obstruction.
-/

namespace Hypertournaments

/-- To check admissibility of a 5-hypertournament on Fin k, it
suffices to check canonical increasing six-vertex subsets. -/
theorem admissible_five_of_canonical
    {k : ℕ} (S : Set ℕ) (A : Hyper 5 (Fin k))
    (h : ∀ (Q : Finset (Fin k)) (hQ : Q.card = 6),
      localIndex A (Q.orderEmbOfFin hQ).toEmbedding ∈ S) :
    Admissible S A := by
  intro f
  let Q : Finset (Fin k) := tupleVertices f
  have hQ : Q.card = 6 := by
    dsimp [Q, tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  let g : Fin 6 ↪o Fin k := Q.orderEmbOfFin hQ
  let τ : Equiv.Perm (Fin 6) := Tuple.sort (f : Fin 6 → Fin k)
  have hmono : Monotone ((f : Fin 6 → Fin k) ∘ τ) :=
    Tuple.monotone_sort (f : Fin 6 → Fin k)
  have hinj : Function.Injective ((f : Fin 6 → Fin k) ∘ τ) :=
    f.injective.comp τ.injective
  have hsorted : (f : Fin 6 → Fin k) ∘ τ = (g : Fin 6 → Fin k) := by
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
  have hindex : localIndex A f = localIndex A g.toEmbedding := by
    calc
      localIndex A f =
          localIndex A (τ.symm.toEmbedding.trans g.toEmbedding) := by rw [hreorder]
      _ = localIndex A g.toEmbedding := localIndex_perm5 A g.toEmbedding τ.symm
  exact hindex ▸ hg

/-- A six-subset certificate on the underlying ordered sign table
establishes full admissibility of an intrinsic 5-hypertournament. -/
theorem fromOrderedSigns_admissible_five_of_direct
    {k : ℕ} (signs : Finset (Fin k) → Bool) (S : Set ℕ)
    (h : ∀ (Q : Finset (Fin k)) (hQ : Q.card = 6),
      min (increasingPacketPositiveCount signs (Q.orderEmbOfFin hQ))
          (6 - increasingPacketPositiveCount signs (Q.orderEmbOfFin hQ)) ∈ S) :
    Admissible S (Hyper.fromOrderedSigns (n := 5) signs) := by
  apply admissible_five_of_canonical S
  intro Q hQ
  rw [localIndex_ordered_sign signs (Q.orderEmbOfFin hQ)]
  exact h Q hQ

end Hypertournaments
