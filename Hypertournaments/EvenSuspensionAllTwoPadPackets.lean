import Hypertournaments.EvenSuspensionPreparedTwoPadShift
import Hypertournaments.EvenPadOrderCount

/-!
# Decomposing all increasing two-pad packets of the even suspension

Every increasing (n+3)-tuple with exactly two padding vertices has
the canonical form consisting of its two increasing pads followed
by the strictly increasing old (n+1)-tuple. We construct the old
tuple using subtraction of the pad offset, with the correct bounds.

This upgrades the previously checked prepared-two-pad local-index
shift to an actual type-shift formula for *all* increasing packets
containing exactly two pads. No all-arity permutation invariance
is assumed here.
-/

namespace Hypertournaments

/-- An arbitrary increasing high tuple with exactly two pads
is uniquely obtained by prepending two increasing pads to an
increasing old tuple. -/
theorem evenPaddedTuple_of_increasing_twoPads
    {n m k : ℕ} (f : Fin (n + 3) ↪o Fin (m + k))
    (htwo :
      (evenPadProjection m k (tupleVertices f.toEmbedding)).card = 2) :
    ∃ (x y : Fin m) (hxy : x < y) (t : Fin (n + 1) ↪o Fin k),
      f.toEmbedding = evenPaddedTuple m k x y hxy t.toEmbedding := by
  have hOld (i : Fin (n + 1)) :
      m ≤ (f i.succ.succ).val := by
    by_contra hnot
    have hlt : (f i.succ.succ).val < m := by omega
    have hp := (evenPadProjection_ordered_prefix f i.succ.succ).2 hlt
    rw [htwo] at hp
    simp only [Fin.val_succ] at hp
    omega
  let tFun : Fin (n + 1) → Fin k := fun i =>
    ⟨(f i.succ.succ).val - m, by
      have hb := (f i.succ.succ).isLt
      have ha := hOld i
      omega⟩
  have htMono : StrictMono tFun := by
    intro i j hij
    have hindex : i.succ.succ < j.succ.succ := by
      change i.val + 2 < j.val + 2
      omega
    have hfij := f.strictMono hindex
    change (f i.succ.succ).val < (f j.succ.succ).val at hfij
    change (f i.succ.succ).val - m <
      (f j.succ.succ).val - m
    have hi := hOld i
    have hj := hOld j
    omega
  let t : Fin (n + 1) ↪o Fin k :=
    OrderEmbedding.ofStrictMono tFun htMono
  have hTail (i : Fin (n + 1)) :
      evenOldShift m k (t i) = f i.succ.succ := by
    apply Fin.ext
    change m + ((f i.succ.succ).val - m) = (f i.succ.succ).val
    have hl := hOld i
    omega
  have hp0 : (f (0 : Fin (n + 3))).val < m := by
    apply (evenPadProjection_ordered_prefix f 0).1
    rw [htwo]
    simp only [Fin.val_zero]
    omega
  have hp1 : (f ((0 : Fin (n + 2)).succ)).val < m := by
    apply (evenPadProjection_ordered_prefix f (0 : Fin (n + 2)).succ).1
    rw [htwo]
    simp only [Fin.val_succ, Fin.val_zero]
    omega
  let x : Fin m := ⟨(f (0 : Fin (n + 3))).val, hp0⟩
  let y : Fin m := ⟨(f ((0 : Fin (n + 2)).succ)).val, hp1⟩
  have hxy : x < y := by
    change (f (0 : Fin (n + 3))).val <
      (f ((0 : Fin (n + 2)).succ)).val
    apply f.strictMono
    change (0 : ℕ) < 1
    omega
  have hx : f (0 : Fin (n + 3)) = evenPadShift m k x := by
    apply Fin.ext
    rfl
  have hy : f ((0 : Fin (n + 2)).succ) = evenPadShift m k y := by
    apply Fin.ext
    rfl
  refine ⟨x, y, hxy, t, ?_⟩
  ext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_
    (fun z => ?_) j) i
  · simpa only [evenPaddedTuple, twoPadSliceTuple, twoPadTuple_zero]
      using congrArg Fin.val hx
  · simpa only [evenPaddedTuple, twoPadSliceTuple, twoPadTuple_one]
      using congrArg Fin.val hy
  · simpa only [evenPaddedTuple, twoPadSliceTuple, twoPadTuple_old]
      using congrArg Fin.val (hTail z).symm

/-- The actual local type of every increasing even-suspension
packet with exactly two pads is the old type plus one. -/
theorem Hyper.evenSuspension_localIndex_increasing_twoPads
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (f : Fin (n + 3) ↪o Fin (m + k))
    (htwo :
      (evenPadProjection m k (tupleVertices f.toEmbedding)).card = 2) :
    ∃ t : Fin (n + 1) ↪o Fin k,
      localIndex (A.evenSuspension m k) f.toEmbedding =
        localIndex A t.toEmbedding + 1 := by
  obtain ⟨x, y, hxy, t, hf⟩ :=
    evenPaddedTuple_of_increasing_twoPads f htwo
  refine ⟨t, ?_⟩
  rw [hf]
  exact A.evenSuspension_localIndex_prepared_twoPads m k x y hxy t

end Hypertournaments
