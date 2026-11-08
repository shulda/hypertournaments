import Hypertournaments.SeedFourDirect
import Hypertournaments.SeedFourCanonical

/-!
# Connect direct finite-set rank certificates with intrinsic local type

The direct certificate uses the rank of an omitted vertex inside a
five-set. The intrinsic local index uses the index of that vertex in
the increasing enumeration. The two approaches agree, by a bijection
between the five indices and the five vertices.

This is a mathematical proof of the correctness of the finite test,
not an assumption about the particular witness.
-/

namespace Hypertournaments

/-- Direct rank counting on a five-set agrees with counting
normalized facets of its increasing enumeration. -/
theorem directCount_eq_increasingPacket
    {k : ℕ} (signs : Finset (Fin k) → Bool)
    (Q : Finset (Fin k)) (hQ : Q.card = 5) :
    directFacetPositiveCount signs Q =
      increasingPacketPositiveCount signs (Q.orderEmbOfFin hQ) := by
  classical
  let f : Fin 5 ↪o Fin k := Q.orderEmbOfFin hQ
  have himage : (Finset.univ : Finset (Fin 5)).image f = Q :=
    Finset.image_orderEmbOfFin_univ Q hQ
  have hvertices : tupleVertices f.toEmbedding = Q := by
    simpa [tupleVertices] using himage
  let P : Fin k → Prop := fun v =>
    Bool.xor (signs (Q.erase v))
      (decide ((Q.filter (· < v)).card % 2 = 1)) = true
  have hpoint (i : Fin 5) :
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
        ((Finset.univ : Finset (Fin 5)).filter
          (fun i => P (f i))).image f := by
    calc
      Q.filter P =
          (((Finset.univ : Finset (Fin 5)).image f).filter P) :=
        congrArg (fun T : Finset (Fin k) => T.filter P) himage.symm
      _ = _ := Finset.filter_image
  unfold directFacetPositiveCount increasingPacketPositiveCount
  change (Q.filter P).card =
    ((Finset.univ : Finset (Fin 5)).filter (fun i =>
      Bool.xor (signs (tupleVertices (facet f.toEmbedding i)))
        (decide (i.val % 2 = 1)) = true)).card
  calc
    (Q.filter P).card =
        (((Finset.univ : Finset (Fin 5)).filter
          (fun i => P (f i))).image f).card :=
      congrArg Finset.card hfilter
    _ = ((Finset.univ : Finset (Fin 5)).filter
          (fun i => P (f i))).card :=
      Finset.card_image_of_injective _ f.injective
    _ = _ := by
      congr 1
      ext i
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and]
        using hpoint i

/-- A direct centrality check is exactly the canonical intrinsic
centrality check on the unique increasing five-tuple. -/
theorem directCentral4_iff_canonical
    {k : ℕ} (signs : Finset (Fin k) → Bool)
    (Q : Finset (Fin k)) :
    directCentral4At signs Q ↔
      canonicalCentral4At (Hyper.fromOrderedSigns signs) Q := by
  by_cases h : Q.card = 5
  · constructor
    · intro hc
      have hcnt := hc h
      have hgoal : localIndex (Hyper.fromOrderedSigns signs)
          (Q.orderEmbOfFin h).toEmbedding = 2 := by
        rw [localIndex_ordered_sign,
          ← directCount_eq_increasingPacket signs Q h]
        exact hcnt
      simpa [canonicalCentral4At, h] using hgoal
    · intro hc
      intro _
      have hcnt : localIndex (Hyper.fromOrderedSigns signs)
          (Q.orderEmbOfFin h).toEmbedding = 2 := by
        simpa [canonicalCentral4At, h] using hc
      rw [localIndex_ordered_sign, ← directCount_eq_increasingPacket signs Q h] at hcnt
      exact hcnt
  · constructor
    · intro _; simp [canonicalCentral4At, h]
    · intro _; exact fun hc => False.elim (h hc)

/-- The complete direct finite certificate for the base now yields
the corresponding canonical local-index statement. -/
theorem seed4_base_canonicalCentral :
    ∀ Q : Finset (Fin 7), canonicalCentral4At seed4Base Q := by
  intro Q
  exact (directCentral4_iff_canonical seed4BaseSigns Q).mp
    (seed4_base_directCentral Q)

/-- The same transfer applies to both one-point extensions. -/
theorem seed4_left_canonicalCentral :
    ∀ Q : Finset (Fin 8), canonicalCentral4At seed4Left Q := by
  intro Q
  exact (directCentral4_iff_canonical seed4LeftSigns Q).mp
    (seed4_left_directCentral Q)

theorem seed4_right_canonicalCentral :
    ∀ Q : Finset (Fin 8), canonicalCentral4At seed4Right Q := by
  intro Q
  exact (directCentral4_iff_canonical seed4RightSigns Q).mp
    (seed4_right_directCentral Q)

end Hypertournaments
