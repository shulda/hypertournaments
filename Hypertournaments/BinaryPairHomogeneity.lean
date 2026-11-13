import Hypertournaments.BinaryPair

/-!
# Separately homogeneous binary types force a common order direction

The directed triangle equates the comparison colours of the two edge types.
The induced tournament embedding itself remains unchanged.
-/

universe v w

namespace Hypertournaments.Ramsey

open StructuralRamsey
open StructuralRamsey.Structure

private def cyclePair01 : Embedding (orderedBinaryPair false)
    (toOrderedNative binaryCycle inferInstance) :=
  binaryPairEmbedding binaryCycle inferInstance 0 1 (by decide) false binaryCycle_01

private def cyclePair12 : Embedding (orderedBinaryPair false)
    (toOrderedNative binaryCycle inferInstance) :=
  binaryPairEmbedding binaryCycle inferInstance 1 2 (by decide) false binaryCycle_12

private def cyclePair02 : Embedding (orderedBinaryPair true)
    (toOrderedNative binaryCycle inferInstance) :=
  binaryPairEmbedding binaryCycle inferInstance 0 2 (by decide) true binaryCycle_02

/-- An ordered directed triangle prevents opposite comparison colours for
its two ordered edge types. -/
theorem binary_pair_order_homogeneity
    {U : Type v} {V : Type w} (D : Hyper 2 U) (oldD : LinearOrder U)
    (C : Hyper 2 V) (oldC newC : LinearOrder V)
    (cycle : Embedding (toOrderedNative binaryCycle inferInstance) (toOrderedNative D oldD))
    (f : Embedding (toOrderedNative D oldD) (toOrderedNative C oldC))
    (hhom : ∀ (b : Bool)
      (e₁ e₂ : Embedding (orderedBinaryPair b) (toOrderedNative D oldD)),
      binaryPairColor newC (f.comp e₁) = binaryPairColor newC (f.comp e₂)) :
    (@StrictMono U V oldD.toPreorder newC.toPreorder f) ∨
      (@StrictAnti U V oldD.toPreorder newC.toPreorder f) := by
  let : LinearOrder U := oldD
  let : LinearOrder V := newC
  let e01 := cycle.comp cyclePair01
  let e12 := cycle.comp cyclePair12
  let e02 := cycle.comp cyclePair02
  have hc12 : binaryPairColor newC (f.comp e12) = binaryPairColor newC (f.comp e01) :=
    hhom false e12 e01
  have hsame : binaryPairColor newC (f.comp e02) = binaryPairColor newC (f.comp e01) := by
    cases h01 : binaryPairColor newC (f.comp e01) <;>
      cases h02 : binaryPairColor newC (f.comp e02)
    · rfl
    · have h01' := (binaryPairColor_false newC (f.comp e01)).mp h01
      have h12' := (binaryPairColor_false newC (f.comp e12)).mp (hc12.trans h01)
      have h02' := (binaryPairColor_true newC (f.comp e02)).mp h02
      change ¬ f (cycle 0) < f (cycle 1) at h01'
      change ¬ f (cycle 1) < f (cycle 2) at h12'
      change f (cycle 0) < f (cycle 2) at h02'
      exact False.elim ((not_lt_of_ge (le_trans (le_of_not_gt h12')
        (le_of_not_gt h01'))) h02')
    · have h01' := (binaryPairColor_true newC (f.comp e01)).mp h01
      have h12' := (binaryPairColor_true newC (f.comp e12)).mp (hc12.trans h01)
      have h02' := (binaryPairColor_false newC (f.comp e02)).mp h02
      change f (cycle 0) < f (cycle 1) at h01'
      change f (cycle 1) < f (cycle 2) at h12'
      change ¬ f (cycle 0) < f (cycle 2) at h02'
      exact False.elim (h02' (lt_trans h01' h12'))
    · rfl
  have heq (b : Bool) (e : Embedding (orderedBinaryPair b) (toOrderedNative D oldD)) :
      binaryPairColor newC (f.comp e) = binaryPairColor newC (f.comp e01) := by
    cases b
    · exact hhom false e e01
    · exact (hhom true e e02).trans hsame
  cases hc : binaryPairColor newC (f.comp e01) with
  | false =>
    right
    intro x y hxy
    let b := D.orient (binaryPairTuple oldD x y hxy).toEmbedding
    let e := binaryPairEmbedding D oldD x y hxy b rfl
    have he : binaryPairColor newC (f.comp e) = false := (heq b e).trans hc
    have hnot := (binaryPairColor_false newC (f.comp e)).mp he
    have hnot' : ¬ f x < f y := by
      simpa only [e, Embedding.comp_apply, binaryPairEmbedding_zero, binaryPairEmbedding_one] using hnot
    have hne : f y ≠ f x := by
      intro heq
      exact hxy.ne (f.injective heq).symm
    exact lt_of_le_of_ne (le_of_not_gt hnot') hne
  | true =>
    left
    intro x y hxy
    let b := D.orient (binaryPairTuple oldD x y hxy).toEmbedding
    let e := binaryPairEmbedding D oldD x y hxy b rfl
    have he : binaryPairColor newC (f.comp e) = true := (heq b e).trans hc
    have hlt := (binaryPairColor_true newC (f.comp e)).mp he
    simpa only [e, Embedding.comp_apply, binaryPairEmbedding_zero, binaryPairEmbedding_one] using hlt

end Hypertournaments.Ramsey
