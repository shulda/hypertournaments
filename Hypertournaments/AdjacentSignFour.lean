import Hypertournaments.AdjacentPacketFour
import Hypertournaments.LocalTypes

/-!
# Adjacent-swap law for actual 4-hypertournament orientations

The previous module checked the 20 finite coordinate equalities and
the five-bit minority identity. Here we use the alternating law of a
hypertournament to turn those finite facts into a transformation
formula for the actual normalized five-facet packet.

No source-specific assumptions are used.
-/

namespace Hypertournaments

/-- The Boolean parity identity behind every adjacent transposition
of a normalized five-facet packet. -/
theorem adjacent_normalized_bool_identity
    (p : Fin 4) (k : Fin 5) (b : Bool) :
    Bool.xor
      (if (facetSwap4 p k).sign = (1 : ℤˣ) then b else !b)
      (decide (k.val % 2 = 1)) =
    !(Bool.xor b
        (decide (((adjacentSwap4 p) k).val % 2 = 1))) := by
  fin_cases p <;> fin_cases k <;> cases b <;> decide

/-- Applying a five-coordinate adjacent swap before taking a facet
is the same as taking the corresponding facet first, then applying
the induced four-coordinate permutation. -/
theorem facet_adjacentSwap4
    {V : Type*} (f : Fin 5 ↪ V) (p : Fin 4) (k : Fin 5) :
    facet ((adjacentSwap4 p).toEmbedding.trans f) k =
      (facetSwap4 p k).toEmbedding.trans
        (facet f ((adjacentSwap4 p) k)) := by
  ext i
  change f ((adjacentSwap4 p) (k.succAbove i)) =
    f (((adjacentSwap4 p) k).succAbove ((facetSwap4 p k) i))
  exact congrArg f (DFunLike.congr_fun (facetSwap4_correct p k) i)

/-- The actual raw orientation of the facet after an adjacent
coordinate swap, including its induced parity. -/
theorem orient_facet_adjacentSwap4
    {V : Type*} (D : Hyper 4 V)
    (f : Fin 5 ↪ V) (p : Fin 4) (k : Fin 5) :
    D.orient (facet ((adjacentSwap4 p).toEmbedding.trans f) k) =
    if (facetSwap4 p k).sign = (1 : ℤˣ) then
      D.orient (facet f ((adjacentSwap4 p) k))
    else
      !(D.orient (facet f ((adjacentSwap4 p) k))) := by
  rw [facet_adjacentSwap4]
  exact D.orient_perm (facet f ((adjacentSwap4 p) k))
    (facetSwap4 p k)

/-- An adjacent swap complements every normalized facet sign and
swaps the positions of the two affected coordinates. -/
theorem normalizedFacet_adjacentSwap4
    {V : Type*} (D : Hyper 4 V)
    (f : Fin 5 ↪ V) (p : Fin 4) (k : Fin 5) :
    normalizedFacet D ((adjacentSwap4 p).toEmbedding.trans f) k =
      !(normalizedFacet D f ((adjacentSwap4 p) k)) := by
  unfold normalizedFacet
  rw [orient_facet_adjacentSwap4]
  exact adjacent_normalized_bool_identity p k
    (D.orient (facet f ((adjacentSwap4 p) k)))

/-- The actual local type index is invariant under every adjacent
swap of the five tuple coordinates. -/
theorem localIndex_adjacentSwap4
    {V : Type*} (D : Hyper 4 V) (f : Fin 5 ↪ V) (p : Fin 4) :
    localIndex D ((adjacentSwap4 p).toEmbedding.trans f) =
      localIndex D f := by
  change minority5 (fun k : Fin 5 =>
      normalizedFacet D ((adjacentSwap4 p).toEmbedding.trans f) k) =
    minority5 (fun k : Fin 5 => normalizedFacet D f k)
  have hfun :
      (fun k : Fin 5 =>
        normalizedFacet D ((adjacentSwap4 p).toEmbedding.trans f) k) =
      (fun k : Fin 5 =>
        !(normalizedFacet D f ((adjacentSwap4 p) k))) := by
    funext k
    exact normalizedFacet_adjacentSwap4 D f p k
  rw [hfun]
  exact minority5_adjacent_complement
    (fun k : Fin 5 => normalizedFacet D f k) p

end Hypertournaments
