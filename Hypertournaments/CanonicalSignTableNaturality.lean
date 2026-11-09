import Hypertournaments.CanonicalSignPresentation

/-!
# Naturality of the canonical intrinsic sign presentation

The canonical sign table of a finite intrinsic hypertournament is
natural under every increasing vertex embedding preserving its
orientations. This works uniformly in the arity and, importantly,
also handles subsets of the wrong cardinality (whose table entries
are dummy values). It will be used to prove preservation of a
common base by the concrete even-suspension sign table.

This assertion does not assume or assert any amalgamation theorem.
-/

namespace Hypertournaments

/-- An order-preserving genuine vertex embedding transports the
canonical signs of *all* old finite subsets, including wrong-sized
subsets, into the larger intrinsic hypertournament. -/
theorem Hyper.canonicalSignTable_image_orderEmbedding
    {n k l : ℕ} (A : Hyper n (Fin k)) (B : Hyper n (Fin l))
    (g : Fin k ↪o Fin l)
    (hAB : Preserves A B g.toEmbedding)
    (Q : Finset (Fin k)) :
    B.canonicalSignTable (Q.image g) = A.canonicalSignTable Q := by
  classical
  by_cases hQ : Q.card = n
  · have hcard : (Q.image g).card = n := by
      rw [Finset.card_image_of_injective _ g.injective]
      exact hQ
    have hvertices :
        Finset.univ.image (Q.orderEmbOfFin hQ) = Q :=
      Finset.image_orderEmbOfFin_univ Q hQ
    have hmem (i : Fin n) :
        g (Q.orderEmbOfFin hQ i) ∈ Q.image g := by
      apply Finset.mem_image_of_mem
      rw [← hvertices]
      exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hmono :
        StrictMono (fun i : Fin n => g (Q.orderEmbOfFin hQ i)) :=
      g.strictMono.comp (Q.orderEmbOfFin hQ).strictMono
    have horder :
        (fun i : Fin n => g (Q.orderEmbOfFin hQ i)) =
          ((Q.image g).orderEmbOfFin hcard : Fin n → Fin l) := by
      exact Finset.orderEmbOfFin_unique hcard hmem hmono
    rw [Hyper.canonicalSignTable_at B _ hcard,
        Hyper.canonicalSignTable_at A _ hQ]
    have hemb :
        ((Q.image g).orderEmbOfFin hcard).toEmbedding =
          (Q.orderEmbOfFin hQ).toEmbedding.trans g.toEmbedding := by
      ext i
      exact (congrFun horder i).symm
    rw [hemb]
    exact hAB (Q.orderEmbOfFin hQ).toEmbedding
  · have hnot : (Q.image g).card ≠ n := by
      rw [Finset.card_image_of_injective _ g.injective]
      exact hQ
    simp [Hyper.canonicalSignTable, hQ, hnot]

end Hypertournaments
