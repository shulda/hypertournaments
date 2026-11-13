import Hypertournaments.OddToggleP3ExplicitPotentials
import Mathlib.Data.ZMod.Basic

/-!
# Real old-base coordinates for the zero-sum p3 transversal code

The existing zero-sum source code was encoded abstractly by tuples
q : Fin m → ZMod t, while the true random side potential is evaluated
on finite subsets of Fin(m*t) partitioned into m consecutive blocks.

We now make the first concrete geometric bridge: a block index i and
cyclic coordinate z determine the ACTUAL old vertex
  i*t + ZMod.val z : Fin(m*t).
Its true old block label is exactly i, and the cyclic coordinate
can be recovered from the old vertex for a fixed block.

Thus any coordinate tuple q determines a finite old vertex set
with m distinct elements, one from each block. The next step
will verify its exact p3IsBlockTransversal predicate and the
punctured-variable source maps on these real vertex sets.
No random probabilities, age membership or AP claims here.
-/

namespace Hypertournaments

/-- The real old-base vertex in block i with cyclic coordinate z. -/
def p3BlockCoordinateVertex
    (m t : ℕ) (ht : 0 < t)
    (i : Fin m) (z : ZMod t) : Fin (m*t) := by
  letI : NeZero t := ⟨by omega⟩
  have hz : z.val < t := ZMod.val_lt z
  have hi : i.val + 1 ≤ m := Nat.succ_le_of_lt i.isLt
  have hmul : (i.val+1)*t ≤ m*t :=
    Nat.mul_le_mul_right t hi
  have hupper : i.val*t+t ≤ m*t := by
    simpa only [add_mul, one_mul] using hmul
  refine ⟨i.val*t+z.val, ?_⟩
  exact (Nat.add_lt_add_left hz (i.val*t)).trans_le hupper

/-- This ACTUAL old vertex lies in precisely the intended block. -/
theorem p3BlockCoordinateVertex_blockNumber
    (m t : ℕ) (ht : 0 < t)
    (i : Fin m) (z : ZMod t) :
    p3BlockNumber t (p3BlockCoordinateVertex m t ht i z) = i.val := by
  letI : NeZero t := ⟨by omega⟩
  have hz : z.val < t := ZMod.val_lt z
  change (i.val*t+z.val)/t = i.val
  calc
    (i.val*t+z.val)/t = (z.val+t*i.val)/t := by
      rw [Nat.mul_comm i.val t, Nat.add_comm]
    _ = z.val /t + i.val := Nat.add_mul_div_left _ _ ht
    _ = i.val := by rw [Nat.div_eq_of_lt hz]; omega

/-- In a fixed old block, the old vertex uniquely determines its
cyclic source coordinate. -/
theorem p3BlockCoordinateVertex_injective_coordinate
    (m t : ℕ) (ht : 0 < t) (i : Fin m) :
    Function.Injective (p3BlockCoordinateVertex m t ht i) := by
  letI : NeZero t := ⟨by omega⟩
  intro u v h
  have hv := congrArg Fin.val h
  change i.val*t+u.val = i.val*t+v.val at hv
  have heq : u.val = v.val := by omega
  exact (ZMod.val_injective t) heq

/-- A concrete old finite set selected by one cyclic coordinate
in every consecutive old block. -/
def p3CoordinateTransversal
    (m t : ℕ) (ht : 0 < t)
    (q : Fin m → ZMod t) : Finset (Fin (m*t)) :=
  Finset.univ.image (fun i : Fin m =>
    p3BlockCoordinateVertex m t ht i (q i))

/-- Distinct block labels yield distinct true old vertices,
independently of their cyclic coordinates. -/
theorem p3CoordinateTransversal_vertex_injective
    (m t : ℕ) (ht : 0 < t)
    (q : Fin m → ZMod t) :
    Function.Injective (fun i : Fin m =>
      p3BlockCoordinateVertex m t ht i (q i)) := by
  intro i j h
  have hb := congrArg (p3BlockNumber t) h
  rw [p3BlockCoordinateVertex_blockNumber,
      p3BlockCoordinateVertex_blockNumber] at hb
  exact Fin.ext hb

/-- Every coordinate tuple selects EXACTLY m actual old vertices,
one per block; no two distinct coordinates collapse across blocks. -/
theorem p3CoordinateTransversal_card
    (m t : ℕ) (ht : 0 < t)
    (q : Fin m → ZMod t) :
    (p3CoordinateTransversal m t ht q).card = m := by
  classical
  change ((Finset.univ : Finset (Fin m)).image
      (fun i : Fin m => p3BlockCoordinateVertex m t ht i (q i))).card = m
  rw [Finset.card_image_of_injective _
    (p3CoordinateTransversal_vertex_injective m t ht q)]
  simp

end Hypertournaments
