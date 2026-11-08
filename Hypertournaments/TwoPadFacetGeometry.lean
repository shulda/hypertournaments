import Hypertournaments.TwoPadSlice

/-!
# Facet geometry of intrinsic two-pad slices

An old (n+1)-tuple t gives an ambient (n+3)-tuple by prepending two
pads. Deleting any old coordinate i+2 from the ambient tuple is
*exactly* the two-pad tuple obtained by first deleting coordinate i
from t. This is the essential geometric input in the local-index
shift of the general two-coordinate reflection.

No order on either vertex set is assumed and no arity is fixed.
-/

namespace Hypertournaments

/-- Deletion of an old coordinate (index >=2) leaves pad zero
at coordinate zero. -/
theorem twoPad_succAbove_pad_zero {n : ℕ} (i : Fin (n + 1)) :
    (i.succ.succ).succAbove (0 : Fin (n + 2)) = 0 := by
  exact Fin.succ_succAbove_zero i.succ

/-- Deletion of an old coordinate leaves pad one at coordinate one. -/
theorem twoPad_succAbove_pad_one {n : ℕ} (i : Fin (n + 1)) :
    (i.succ.succ).succAbove (1 : Fin (n + 2)) = 1 := by
  change (i.succ.succ).succAbove ((0 : Fin (n + 1)).succ) =
    ((0 : Fin (n + 2)).succ)
  rw [Fin.succ_succAbove_succ]
  rw [Fin.succ_succAbove_zero]

/-- Deletion commutes with prepending the two fixed pad coordinates. -/
theorem twoPad_succAbove_old {n : ℕ}
    (i : Fin (n + 1)) (k : Fin n) :
    (i.succ.succ).succAbove k.succ.succ =
      (i.succAbove k).succ.succ := by
  simp only [Fin.succ_succAbove_succ]

/-- Literal equality of the injective facet tuples. Every facet
of a two-pad packet obtained by deleting an old vertex agrees with
the two-pad tuple of the corresponding old facet. -/
theorem twoPadSliceTuple_facet
    {n : ℕ} {W V : Type*}
    (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (t : Fin (n + 1) ↪ W)
    (i : Fin (n + 1)) :
    twoPadSliceTuple g p q hp hq hpq (facet t i) =
      facet (twoPadSliceTuple g p q hp hq hpq t) i.succ.succ := by
  ext k
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun u => ?_) j) k
  · simp [facet, twoPadSliceTuple, twoPad_succAbove_pad_zero]
  · simp [facet, twoPadSliceTuple, twoPad_succAbove_pad_one]
  · simp [facet, twoPadSliceTuple, twoPad_succAbove_old]

/-- The parity used to normalize a facet is unchanged when its
index is shifted by two. -/
theorem twoPad_facet_parity
    {n : ℕ} (i : Fin (n + 1)) :
    decide ((i.succ.succ).val % 2 = 1) =
      decide (i.val % 2 = 1) := by
  have h : (i.succ.succ).val % 2 = i.val % 2 := by
    simp only [Fin.val_succ]
    omega
  rw [h]

/-- Every old normalized facet of a two-pad slice is literally the
normalized ambient facet at index i+2. This is the key
all-arity bridge between the old and the new packet. -/
theorem normalizedFacet_twoPadSlice_old
    {n : ℕ} {W V : Type*}
    (D : Hyper (n + 2) V) (g : W ↪ V) (p q : V)
    (hp : p ∉ Set.range g) (hq : q ∉ Set.range g)
    (hpq : p ≠ q) (t : Fin (n + 1) ↪ W)
    (i : Fin (n + 1)) :
    normalizedFacet D (twoPadSliceTuple g p q hp hq hpq t)
        i.succ.succ =
      normalizedFacet (D.twoPadSlice g p q hp hq hpq) t i := by
  unfold normalizedFacet
  rw [← twoPadSliceTuple_facet]
  change Bool.xor
      (D.orient (twoPadSliceTuple g p q hp hq hpq (facet t i)))
      (decide ((i.succ.succ).val % 2 = 1)) =
    Bool.xor
      (D.orient (twoPadSliceTuple g p q hp hq hpq (facet t i)))
      (decide (i.val % 2 = 1))
  rw [twoPad_facet_parity]

end Hypertournaments
