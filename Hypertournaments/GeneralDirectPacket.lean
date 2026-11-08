import Hypertournaments.SeedFiveAdmissible
import Hypertournaments.SeedFourDirect

/-!
# Uniform finite-set rank verifier for local packets

The direct finite-set checker already used for the arity-four seeds
works in every arity: the number of smaller vertices in a packet is
the index of the omitted facet in its increasing enumeration.

This module proves that general bridge rather than repeating an
arity-specific finite computation, and exposes it for the arity-five
seed certificates.
-/

namespace Hypertournaments

/-- Rank-based finite-set packet counting agrees with the intrinsic
normalized-facet count on the canonical increasing enumeration,
uniformly for any arity n. -/
theorem directCount_eq_increasingPacket_general
    {n k : ℕ} (signs : Finset (Fin k) → Bool)
    (Q : Finset (Fin k)) (hQ : Q.card = n + 1) :
    directFacetPositiveCount signs Q =
      increasingPacketPositiveCount signs (Q.orderEmbOfFin hQ) := by
  classical
  let f : Fin (n + 1) ↪o Fin k := Q.orderEmbOfFin hQ
  have himage : (Finset.univ : Finset (Fin (n + 1))).image f = Q :=
    Finset.image_orderEmbOfFin_univ Q hQ
  have hvertices : tupleVertices f.toEmbedding = Q := by
    simpa [tupleVertices] using himage
  let P : Fin k → Prop := fun v =>
    Bool.xor (signs (Q.erase v))
      (decide ((Q.filter (· < v)).card % 2 = 1)) = true
  have hpoint (i : Fin (n + 1)) :
      P (f i) ↔
      Bool.xor (signs (tupleVertices (facet f.toEmbedding i)))
        (decide (i.val % 2 = 1)) = true := by
    have hrank := card_lt_tupleVertices_eq f i
    rw [hvertices] at hrank
    have hfacet : Q.erase (f i) =
        tupleVertices (facet f.toEmbedding i) := by
      simpa [hvertices] using
        (tupleVertices_facet_eq_erase f.toEmbedding i).symm
    dsimp [P]
    rw [hfacet, hrank]
  have hfilter :
      Q.filter P =
        ((Finset.univ : Finset (Fin (n + 1))).filter
          (fun i => P (f i))).image f := by
    calc
      Q.filter P =
          (((Finset.univ : Finset (Fin (n + 1))).image f).filter P) :=
        congrArg (fun T : Finset (Fin k) => T.filter P) himage.symm
      _ = _ := Finset.filter_image
  unfold directFacetPositiveCount increasingPacketPositiveCount
  change (Q.filter P).card =
    ((Finset.univ : Finset (Fin (n + 1))).filter (fun i =>
      Bool.xor (signs (tupleVertices (facet f.toEmbedding i)))
        (decide (i.val % 2 = 1)) = true)).card
  calc
    (Q.filter P).card =
        (((Finset.univ : Finset (Fin (n + 1))).filter
          (fun i => P (f i))).image f).card :=
      congrArg Finset.card hfilter
    _ = ((Finset.univ : Finset (Fin (n + 1))).filter
          (fun i => P (f i))).card :=
      Finset.card_image_of_injective _ f.injective
    _ = _ := by
      congr 1
      ext i
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and]
        using hpoint i

/-- Rank-based checks on six-subsets imply full (unordered)
admissibility of a 5-hypertournament presented by a sign table. -/
theorem fromOrderedSigns_admissible_five_of_direct_count
    {k : ℕ} (signs : Finset (Fin k) → Bool) (S : Set ℕ)
    (h : ∀ Q : Finset (Fin k), Q.card = 6 →
      min (directFacetPositiveCount signs Q)
          (6 - directFacetPositiveCount signs Q) ∈ S) :
    Admissible S (Hyper.fromOrderedSigns (n := 5) signs) := by
  apply fromOrderedSigns_admissible_five_of_direct signs S
  intro Q hQ
  rw [← directCount_eq_increasingPacket_general (n := 5) signs Q hQ]
  exact h Q hQ

end Hypertournaments
