import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP1ZeroTwoAbstract
import Hypertournaments.CanonicalPacket
import Hypertournaments.GeneralAdjacentFacet

/-!
# Exact coordinates of twice-erased facets in increasing packets

Fix an increasing packet f of n+2 vertices and erase its vertex i.
The remaining increasing tuple has length n+1. Any other original
vertex j is at a unique new coordinate t; it is j before deleting i,
and j-1 after deleting i, precisely the p1ErasePosition arithmetic
appearing in the phase proof.

This module supplies the exact Fin.succAbove geometry and equality of
the *full unordered n-facet sets* after the second deletion. It does
not invoke an AP theorem or assume the source structure is admissible.
-/

namespace Hypertournaments

/-- After removing coordinate i from Fin(n+2), the remaining original
coordinate j has index j when j<i and j-1 when j>i. -/
theorem p1SuccAbove_position
    {n : ℕ} (i j : Fin (n+2)) (hij : i ≠ j) :
    ∃ t : Fin (n+1), i.succAbove t = j ∧
      t.val = p1ErasePosition i j := by
  obtain ⟨t, ht⟩ : ∃ t : Fin (n+1), i.succAbove t = j :=
    Fin.exists_succAbove_eq hij.symm
  refine ⟨t, ht, ?_⟩
  by_cases hji : j < i
  · have hlt : t.castSucc < i := by
      by_contra hh
      have hge : i ≤ t.castSucc := le_of_not_gt hh
      have hpos : i.succAbove t = t.succ :=
        Fin.succAbove_of_le_castSucc i t hge
      have hv := congrArg Fin.val (ht.symm.trans hpos)
      have hli : j.val < i.val := hji
      have hgeval : i.val ≤ t.val := hge
      change j.val = t.val + 1 at hv
      omega
    have hpos : i.succAbove t = t.castSucc :=
      Fin.succAbove_of_castSucc_lt i t hlt
    have hv := congrArg Fin.val (ht.symm.trans hpos)
    have hval : j.val = t.val := hv
    unfold p1ErasePosition
    rw [if_pos hji]
    omega
  · have hijlt : i.val < j.val := by
      have hn : i.val ≠ j.val := by
        intro he
        apply hij
        exact Fin.ext he
      have hnlt : ¬ j.val < i.val := hji
      omega
    have hge : i ≤ t.castSucc := by
      by_contra hh
      have hlt : t.castSucc < i := lt_of_not_ge hh
      have hpos : i.succAbove t = t.castSucc :=
        Fin.succAbove_of_castSucc_lt i t hlt
      have hv := congrArg Fin.val (ht.symm.trans hpos)
      have hval : j.val = t.val := hv
      have hltval : t.val < i.val := hlt
      omega
    have hpos : i.succAbove t = t.succ :=
      Fin.succAbove_of_le_castSucc i t hge
    have hv := congrArg Fin.val (ht.symm.trans hpos)
    have hval : j.val = t.val + 1 := hv
    unfold p1ErasePosition
    rw [if_neg hji]
    omega

/-- True facet geometry for two distinct deletions, with the exact
second deletion index in the first facet's increasing enumeration. -/
theorem p1ActualDoubleFacet_vertices
    {n a : ℕ} (f : Fin (n+2) ↪o Fin a)
    (i j : Fin (n+2)) (hij : i ≠ j) :
    ∃ t : Fin (n+1),
      i.succAbove t = j ∧ t.val = p1ErasePosition i j ∧
        tupleVertices (facet (facet f.toEmbedding i) t) =
          ((tupleVertices f.toEmbedding).erase (f i)).erase (f j) := by
  obtain ⟨t, hcoord, hposition⟩ :=
    p1SuccAbove_position i j hij
  refine ⟨t, hcoord, hposition, ?_⟩
  calc
    tupleVertices (facet (facet f.toEmbedding i) t) =
        (tupleVertices (facet f.toEmbedding i)).erase
          ((facet f.toEmbedding i) t) :=
      tupleVertices_facet_eq_erase (facet f.toEmbedding i) t
    _ = ((tupleVertices f.toEmbedding).erase (f i)).erase (f j) := by
      rw [tupleVertices_facet_eq_erase f.toEmbedding i]
      change ((tupleVertices f.toEmbedding).erase (f i)).erase
        (f (i.succAbove t)) =
        ((tupleVertices f.toEmbedding).erase (f i)).erase (f j)
      rw [hcoord]

end Hypertournaments
