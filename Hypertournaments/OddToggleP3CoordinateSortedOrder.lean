import Hypertournaments.OddToggleP3CoordinateTransversals
import Hypertournaments.CanonicalPacket

/-!
# The increasing enumeration of a genuine full p3 transversal

A cyclic coordinate tuple q selects exactly one real old vertex in
each consecutive block i, namely i*t + val(q_i). Since t>0, these
vertices are STRICTLY increasing with the block label i.

Consequently the unique canonical increasing enumeration of the
actual full transversal is LITERALLY this block-coordinate map,
not just equal as an unordered Finset. This is the exact order
bridge needed to identify the first m packet facets with deleted
block coordinates i in the eventual raw alternating packet proof.
-/

namespace Hypertournaments

/-- Chosen real vertices from distinct old blocks are strictly
increasing in their block index, for arbitrary cyclic coordinates. -/
theorem p3BlockCoordinateVertex_strictMono
    (m t : ℕ) (ht : 0 < t) (q : Fin m → ZMod t) :
    StrictMono (fun i : Fin m =>
      p3BlockCoordinateVertex m t ht i (q i)) := by
  letI : NeZero t := ⟨by omega⟩
  intro i j hij
  apply Fin.lt_def.mpr
  have hi : (q i).val < t := ZMod.val_lt (q i)
  have hmul : (i.val+1)*t ≤ j.val*t :=
    Nat.mul_le_mul_right t (by exact Nat.succ_le_of_lt hij)
  change i.val*t + (q i).val < j.val*t + (q j).val
  have hrewrite : (i.val+1)*t = i.val*t+t := by
    simp only [add_mul,one_mul]
  rw [hrewrite] at hmul
  omega

/-- The actual canonical increasing enumeration of each full
old transversal is exactly its block-coordinate map. -/
theorem p3CoordinateTransversal_orderEmbOfFin
    (m t : ℕ) (ht : 0 < t) (q : Fin m → ZMod t)
    (i : Fin m) :
    ((p3CoordinateTransversal m t ht q).orderEmbOfFin
      (p3CoordinateTransversal_card m t ht q)) i =
    p3BlockCoordinateVertex m t ht i (q i) := by
  classical
  let Q : Finset (Fin (m*t)) := p3CoordinateTransversal m t ht q
  let g : Fin m → Fin (m*t) :=
    fun j => p3BlockCoordinateVertex m t ht j (q j)
  have hmono : StrictMono g := p3BlockCoordinateVertex_strictMono m t ht q
  have hmem (j : Fin m) : g j ∈ Q := by
    change g j ∈ (Finset.univ : Finset (Fin m)).image g
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  have hSame : g =
      (Q.orderEmbOfFin (p3CoordinateTransversal_card m t ht q) :
        Fin m → Fin (m*t)) :=
    Finset.orderEmbOfFin_unique
      (p3CoordinateTransversal_card m t ht q) hmem hmono
  exact (congrFun hSame i).symm

end Hypertournaments
