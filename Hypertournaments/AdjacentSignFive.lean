import Mathlib.Tactic.Ext
import Mathlib.Tactic.FinCases
import Hypertournaments.AdjacentPacketFive
import Hypertournaments.LocalTypes

/-!
# Invariance under adjacent swaps for 5-hypertournament packets

The explicit finite coordinate tables in AdjacentPacketFive are
combined with the intrinsic alternating orientation law.  Every
adjacent transposition complements the normalized six-facet signs
and permutes their coordinates.
-/

namespace Hypertournaments

theorem adjacent_normalized_bool_identity5
    (p : Fin 5) (k : Fin 6) (b : Bool) :
    Bool.xor
      (if (facetSwap5 p k).sign = (1 : ℤˣ) then b else !b)
      (decide (k.val % 2 = 1)) =
    !(Bool.xor b
        (decide (((adjacentSwap5 p) k).val % 2 = 1))) := by
  fin_cases p <;> fin_cases k <;> cases b <;> decide

theorem facet_adjacentSwap5
    {V : Type*} (f : Fin 6 ↪ V) (p : Fin 5) (k : Fin 6) :
    facet ((adjacentSwap5 p).toEmbedding.trans f) k =
      (facetSwap5 p k).toEmbedding.trans
        (facet f ((adjacentSwap5 p) k)) := by
  ext i
  change f ((adjacentSwap5 p) (k.succAbove i)) =
    f (((adjacentSwap5 p) k).succAbove ((facetSwap5 p k) i))
  exact congrArg f (DFunLike.congr_fun (facetSwap5_correct p k) i)

theorem orient_facet_adjacentSwap5
    {V : Type*} (D : Hyper 5 V)
    (f : Fin 6 ↪ V) (p : Fin 5) (k : Fin 6) :
    D.orient (facet ((adjacentSwap5 p).toEmbedding.trans f) k) =
    if (facetSwap5 p k).sign = (1 : ℤˣ) then
      D.orient (facet f ((adjacentSwap5 p) k))
    else
      !(D.orient (facet f ((adjacentSwap5 p) k))) := by
  rw [facet_adjacentSwap5]
  exact D.orient_perm (facet f ((adjacentSwap5 p) k))
    (facetSwap5 p k)

theorem normalizedFacet_adjacentSwap5
    {V : Type*} (D : Hyper 5 V)
    (f : Fin 6 ↪ V) (p : Fin 5) (k : Fin 6) :
    normalizedFacet D ((adjacentSwap5 p).toEmbedding.trans f) k =
      !(normalizedFacet D f ((adjacentSwap5 p) k)) := by
  unfold normalizedFacet
  rw [orient_facet_adjacentSwap5]
  exact adjacent_normalized_bool_identity5 p k
    (D.orient (facet f ((adjacentSwap5 p) k)))

/-- Minority local type is invariant under each adjacent swap of a
six-tuple; this applies to every 5-hypertournament. -/
theorem localIndex_adjacentSwap5
    {V : Type*} (D : Hyper 5 V) (f : Fin 6 ↪ V) (p : Fin 5) :
    localIndex D ((adjacentSwap5 p).toEmbedding.trans f) =
      localIndex D f := by
  change minority6 (fun k : Fin 6 =>
      normalizedFacet D ((adjacentSwap5 p).toEmbedding.trans f) k) =
    minority6 (fun k : Fin 6 => normalizedFacet D f k)
  have hfun :
      (fun k : Fin 6 =>
        normalizedFacet D ((adjacentSwap5 p).toEmbedding.trans f) k) =
      (fun k : Fin 6 =>
        !(normalizedFacet D f ((adjacentSwap5 p) k))) := by
    funext k
    exact normalizedFacet_adjacentSwap5 D f p k
  rw [hfun]
  exact minority6_adjacent_complement
    (fun k : Fin 6 => normalizedFacet D f k) p

end Hypertournaments
