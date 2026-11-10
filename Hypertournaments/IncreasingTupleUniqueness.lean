import Hypertournaments.CanonicalPacket

/-!
# Uniqueness of increasing finite hypertournament tuple presentations

Two increasing embeddings of the same finite ordinal into a finite
ordered vertex set are equal if their underlying sets of vertices
are equal. This is the exact coordinate identity needed to identify
homogeneous facets formed by erasing two vertices in either order,
without appealing to a non-order-preserving permutation or a
hypothetical canonical representative.
-/

namespace Hypertournaments

theorem increasingEmb_eq_of_tupleVertices
    {m a : ℕ} (f g : Fin m ↪o Fin a)
    (h : tupleVertices f.toEmbedding = tupleVertices g.toEmbedding) :
    f = g := by
  let Q : Finset (Fin a) := tupleVertices f.toEmbedding
  have hQ : Q.card = m := by
    dsimp [Q, tupleVertices]
    rw [Finset.card_image_of_injective _ f.injective]
    simp
  have hf : ∀ i : Fin m, f i ∈ Q := by
    intro i
    change f i ∈ (Finset.univ : Finset (Fin m)).image f.toEmbedding
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have hg : ∀ i : Fin m, g i ∈ Q := by
    intro i
    change g i ∈ tupleVertices f.toEmbedding
    rw [h]
    change g i ∈ (Finset.univ : Finset (Fin m)).image g.toEmbedding
    exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
  have heqf :
      (f : Fin m → Fin a) =
        (Q.orderEmbOfFin hQ : Fin m → Fin a) :=
    Finset.orderEmbOfFin_unique hQ hf f.strictMono
  have heqg :
      (g : Fin m → Fin a) =
        (Q.orderEmbOfFin hQ : Fin m → Fin a) :=
    Finset.orderEmbOfFin_unique hQ hg g.strictMono
  ext i
  exact congrArg Fin.val (congrFun (heqf.trans heqg.symm) i)

end Hypertournaments
