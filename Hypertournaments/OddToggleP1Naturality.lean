import Hypertournaments.OddToggleP1ActualPhase
import Hypertournaments.OddToggleP1Parity
import Hypertournaments.OddToggleP1BooleanParity

/-!
# Pullback naturality for simplex coboundary and actual zero-or-two

The p1 exception is a class of intrinsic hypertournaments on finite
vertex sets, but the uniform abstract phase argument lives on the
coordinate set Fin(n+2). Under an injective ambient embedding, the
unsigned coboundary commutes exactly with taking images of finite
subsets. The proof uses the genuine image/erase identity.

As an independent consequence, an actual hypertournament has zero or
two homogeneous deleted packets once its homogeneous indicator is
proved to be the coboundary of the pulled-back raw sign table. Here
that latter assumption remains explicit, for later discharge using
the positive local-type criterion in the p1 class.
-/

namespace Hypertournaments

/-- An increasing facet's genuine vertex set is exactly the image
of the erased coordinate set under the original increasing tuple. -/
theorem p1OrderedFacet_vertices
    {n a : ℕ} (f : Fin (n+2) ↪o Fin a)
    (i : Fin (n+2)) :
    tupleVertices (p1OrderedFacet f i).toEmbedding =
      (((Finset.univ : Finset (Fin (n+2))).erase i).image
        f.toEmbedding) := by
  calc
    tupleVertices (p1OrderedFacet f i).toEmbedding =
        (tupleVertices f.toEmbedding).erase (f i) := by
          rw [p1OrderedFacet_toEmbedding, tupleVertices_facet_eq_erase]
    _ = (((Finset.univ : Finset (Fin (n+2))).erase i).image
          f.toEmbedding) := by
      rw [p1ImageErase f.toEmbedding (Finset.univ : Finset (Fin (n+2))) i]
      rfl

/-- The unsigned F₂ coboundary commutes with injective finite-set
images, without restricting to a fixed arity or degree. -/
theorem p1Coboundary_image
    {r a : ℕ} (f : Fin r ↪ Fin a)
    (e : Finset (Fin a) → ZMod 2)
    (Q : Finset (Fin r)) :
    coboundary (fun P => e (P.image f)) Q =
      coboundary e (Q.image f) := by
  unfold coboundary
  rw [Finset.sum_image (fun i _ j _ heq => f.injective heq)]
  apply Finset.sum_congr rfl
  intro i _
  rw [p1ImageErase f Q i]

/-- If the actual homogeneous indicator on each deleted packet equals
the pulled-back raw-sign coboundary, the number of homogeneous deleted
packets is zero or two. The geometric at-most-two half is already
unconditional for every actual hypertournament, in the parent PR.
-/
theorem Hyper.p1Actual_zero_or_two_of_indicator
    {n a : ℕ} (A : Hyper n (Fin a))
    (f : Fin (n+2) ↪o Fin a)
    (hindicator : ∀ i : Fin (n+2),
      (if localIndex A (facet f.toEmbedding i) = 0
        then (1 : ZMod 2) else 0) =
      coboundary
        (fun Q => p1BitToZMod
          (A.canonicalSignTable (Q.image f.toEmbedding)))
        ((Finset.univ : Finset (Fin (n+2))).erase i)) :
    (Finset.univ.filter (fun i : Fin (n+2) =>
      localIndex A (facet f.toEmbedding i) = 0)).card = 0 ∨
    (Finset.univ.filter (fun i : Fin (n+2) =>
      localIndex A (facet f.toEmbedding i) = 0)).card = 2 := by
  classical
  have hle :=
    A.p1ActualHomogeneous_card_le_two f
  have heven :
      (((Finset.univ.filter (fun i : Fin (n+2) =>
        localIndex A (facet f.toEmbedding i) = 0)).card : ℕ) : ZMod 2) =
        0 := by
    apply p1Cochain_homogeneous_count_even
      (Finset.univ : Finset (Fin (n+2)))
      (fun Q => p1BitToZMod
        (A.canonicalSignTable (Q.image f.toEmbedding)))
      (fun i => localIndex A (facet f.toEmbedding i) = 0)
    intro i _
    exact hindicator i
  exact p1Even_card_le_two_eq_zero_or_two _ hle heven

end Hypertournaments
