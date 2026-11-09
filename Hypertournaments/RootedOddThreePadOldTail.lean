import Hypertournaments.EvenPadOrderCount
import Hypertournaments.CanonicalPacket

/-!
# Every increasing three-pad packet has a canonical increasing old tail

If a finite high (n+3)-tuple is increasing and has exactly three
padding vertices, its final n coordinates are all old vertices.
Subtracting the padding offset m gives an increasing injective
n-tuple t of old vertices. We prove both the literal coordinate
equality and equality of the *entire* old finite-set projection with
the range of t, without making an AP or orientation assumption.

This is the geometric input for the final root-absent h=3 local
type shift in the odd suspension, where the old source (n+1)-tuple
is obtained by prefixing the least distinguished root to t.
-/

namespace Hypertournaments

/-- The last n coordinates of any increasing (n+3)-tuple with
exactly three pads are the unique increasing old tail. -/
theorem evenOldTail_of_increasing_threePads
    {n m a : ℕ}
    (f : Fin (n+3) ↪o Fin (m+a))
    (hthree :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card = 3) :
    ∃ t : Fin n ↪o Fin a,
      (∀ j : Fin n, evenOldShift m a (t j) = f j.succ.succ.succ) ∧
      evenOldProjection m a (tupleVertices f.toEmbedding) =
        tupleVertices t.toEmbedding := by
  have hOld (j : Fin n) : m ≤ (f j.succ.succ.succ).val := by
    by_contra hh
    have hlt : (f j.succ.succ.succ).val < m := by omega
    have hp := (evenPadProjection_ordered_prefix f j.succ.succ.succ).2 hlt
    rw [hthree] at hp
    simp only [Fin.val_succ] at hp
    omega
  let tFun : Fin n → Fin a := fun j =>
    ⟨(f j.succ.succ.succ).val-m, by
      have hb := (f j.succ.succ.succ).isLt
      have ha := hOld j
      omega⟩
  have htMono : StrictMono tFun := by
    intro i j hij
    have hindex : i.succ.succ.succ < j.succ.succ.succ := by
      change i.val + 3 < j.val + 3
      omega
    have hfij := f.strictMono hindex
    change (f i.succ.succ.succ).val <
      (f j.succ.succ.succ).val at hfij
    change (f i.succ.succ.succ).val-m <
      (f j.succ.succ.succ).val-m
    have hi := hOld i
    have hj := hOld j
    omega
  let t : Fin n ↪o Fin a :=
    OrderEmbedding.ofStrictMono tFun htMono
  have hTail (j : Fin n) :
      evenOldShift m a (t j) = f j.succ.succ.succ := by
    apply Fin.ext
    change m + ((f j.succ.succ.succ).val-m) =
      (f j.succ.succ.succ).val
    have hj := hOld j
    omega
  refine ⟨t, hTail, ?_⟩
  ext u
  constructor
  · intro hu
    have hmem :
        evenOldShift m a u ∈ tupleVertices f.toEmbedding := by
      simpa only [evenOldProjection, Finset.mem_filter,
        Finset.mem_univ, true_and] using hu
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    have hge : 3 ≤ i.val := by
      by_contra hh
      have hlt : i.val < 3 := by omega
      have hp : (f i).val < m :=
        (evenPadProjection_ordered_prefix f i).1 (by
          rw [hthree]
          exact hlt)
      have heq := congrArg Fin.val hi
      change (f i).val = m + u.val at heq
      omega
    let j : Fin n := ⟨i.val-3, by
      have hiLt := i.isLt
      omega⟩
    have hij : j.succ.succ.succ = i := by
      apply Fin.ext
      change j.val+3 = i.val
      dsimp [j]
      omega
    have heq : evenOldShift m a (t j) =
        evenOldShift m a u := by
      calc
        evenOldShift m a (t j) = f j.succ.succ.succ := hTail j
        _ = f i := by rw [hij]
        _ = evenOldShift m a u := hi
    have htu : t j = u := (evenOldShift m a).injective heq
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, htu⟩
  · intro hu
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hu
    have hmem :
        evenOldShift m a u ∈ tupleVertices f.toEmbedding := by
      apply Finset.mem_image.mpr
      refine ⟨j.succ.succ.succ, Finset.mem_univ _, ?_⟩
      calc
        f j.succ.succ.succ = evenOldShift m a (t j) := (hTail j).symm
        _ = evenOldShift m a u := congrArg (evenOldShift m a) hj
    simpa only [evenOldProjection, Finset.mem_filter,
      Finset.mem_univ, true_and] using hmem

end Hypertournaments
