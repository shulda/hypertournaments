import Hypertournaments.EvenPadOrderCount
import Hypertournaments.EvenSuspensionRecovery

/-!
# Every increasing packet with exactly two pads is a prepared tuple

In the even-suspension convention all pads occupy the initial interval
[0,m). A strictly increasing high tuple with exactly two pads
therefore starts with those two pads, and the rest is an increasing
tuple of old vertices. This is proved by constructing the old tuple
from the high coordinates after subtracting m and checking both
range bounds and strict monotonicity.

The result is a genuine equality of finite embeddings, not merely
a statement about unordered vertex sets or a cardinality count.
-/

namespace Hypertournaments

/-- An increasing high (n+3)-tuple containing exactly two pads
is literally the two-pad lift of an increasing old (n+1)-tuple. -/
theorem evenPaddedTuple_exists_of_increasing_twoPads
    {n m k : ℕ}
    (f : Fin (n + 3) ↪o Fin (m + k))
    (htwo :
      (evenPadProjection m k (tupleVertices f.toEmbedding)).card = 2) :
    ∃ (x y : Fin m) (hxy : x < y) (t : Fin (n + 1) ↪o Fin k),
      evenPaddedTuple m k x y hxy t.toEmbedding = f.toEmbedding := by
  have hpad0 : (f (0 : Fin (n + 3))).val < m := by
    apply (evenPadProjection_ordered_prefix f 0).1
    rw [htwo]
    simp
  have hpad1 : (f ((0 : Fin (n + 2)).succ)).val < m := by
    apply (evenPadProjection_ordered_prefix f (0 : Fin (n + 2)).succ).1
    rw [htwo]
    simp [Fin.val_succ]
  let x : Fin m := ⟨(f (0 : Fin (n + 3))).val, hpad0⟩
  let y : Fin m := ⟨(f ((0 : Fin (n + 2)).succ)).val, hpad1⟩
  have hxy : x < y := by
    have hindex :
        (0 : Fin (n + 3)) < (0 : Fin (n + 2)).succ := by
      change 0 < 1
      omega
    have h := f.strictMono hindex
    exact h
  have htail (i : Fin (n + 1)) :
      m ≤ (f i.succ.succ).val := by
    by_contra hn
    have hlt : (f i.succ.succ).val < m := by omega
    have hsmall :=
      (evenPadProjection_ordered_prefix f i.succ.succ).2 hlt
    rw [htwo] at hsmall
    simp only [Fin.val_succ] at hsmall
    omega
  let old : Fin (n + 1) → Fin k :=
    fun i => ⟨(f i.succ.succ).val - m, by
      have hbound := (f i.succ.succ).isLt
      have hlow := htail i
      omega⟩
  have hstrict : StrictMono old := by
    intro i j hij
    have hidx : i.succ.succ < j.succ.succ := by
      simp only [Fin.lt_def, Fin.val_succ]
      omega
    have hf : (f i.succ.succ).val <
        (f j.succ.succ).val := f.strictMono hidx
    have hi := htail i
    have hj := htail j
    change (f i.succ.succ).val - m < (f j.succ.succ).val - m
    omega
  let t : Fin (n + 1) ↪o Fin k := OrderEmbedding.ofStrictMono old hstrict
  refine ⟨x, y, hxy, t, ?_⟩
  ext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun z => ?_) j) i
  · apply Fin.ext
    simp [evenPaddedTuple, twoPadSliceTuple, x]
  · apply Fin.ext
    simp [evenPaddedTuple, twoPadSliceTuple, y]
  · apply Fin.ext
    change m + ((f z.succ.succ).val - m) = (f z.succ.succ).val
    omega

end Hypertournaments
