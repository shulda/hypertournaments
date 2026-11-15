import Lean.Elab.Tactic.Omega
import Hypertournaments.EvenAlternatingBalance
import Hypertournaments.UniformPacketPermutationCount

/-!
# Generic three-pad prefix lifts minority local index by exactly one

The root-absent case of the odd rooted suspension adds the normalized
facet word (b,!b,b) in place of the first old normalized facet b.
The remaining old facets are unchanged. This elementary fact increases
the positive-count by exactly one, and the length by exactly two, hence
increases the minority local-type index by exactly one.

This module proves that finite Boolean arithmetic for an **arbitrary**
tail, independent of arity, of any geometric presentation, or any AP
assumptions. It is the precise local counting bridge needed for the
root-absent three-pad case.
-/

namespace Hypertournaments

/-- Replacing a single leading bit b by three bits b,!b,b increases
the number of positive entries by exactly one. -/
theorem boolPacketPositiveCount_threePad_prefix
    {m : ℕ} (b : Bool) (tail : Fin m → Bool) :
    boolPacketPositiveCount
      (Fin.cons b (Fin.cons (!b) (Fin.cons b tail))) =
    boolPacketPositiveCount (Fin.cons b tail) + 1 := by
  simp only [boolPacketPositiveCount_cons]
  cases b <;> simp <;> omega

/-- The minority index of the extended word increases by one, with
NO condition on the old signs or their number. -/
theorem boolPacketMinority_threePad_prefix_shift
    {m : ℕ} (b : Bool) (tail : Fin m → Bool) :
    min
      (boolPacketPositiveCount
        (Fin.cons b (Fin.cons (!b) (Fin.cons b tail))))
      ((m + 3) -
        boolPacketPositiveCount
          (Fin.cons b (Fin.cons (!b) (Fin.cons b tail)))) =
    min (boolPacketPositiveCount (Fin.cons b tail))
      ((m + 1) - boolPacketPositiveCount (Fin.cons b tail)) + 1 := by
  let c : ℕ := boolPacketPositiveCount (Fin.cons b tail)
  have hbound : c ≤ m + 1 := boolPacketPositiveCount_le (Fin.cons b tail)
  have hcount :
      boolPacketPositiveCount (Fin.cons b (Fin.cons (!b)
        (Fin.cons b tail))) = c + 1 :=
    boolPacketPositiveCount_threePad_prefix b tail
  change min
      (boolPacketPositiveCount (Fin.cons b (Fin.cons (!b) (Fin.cons b tail))))
      ((m + 3) -
        boolPacketPositiveCount (Fin.cons b (Fin.cons (!b) (Fin.cons b tail)))) =
      min c ((m + 1) - c) + 1
  rw [hcount]
  have hsub : m + 3 - (c + 1) = (m + 1 - c) + 1 := by omega
  rw [hsub]
  by_cases hle : c ≤ m + 1 - c
  · have hs : c + 1 ≤ (m + 1 - c) + 1 := by omega
    rw [Nat.min_eq_left hle, Nat.min_eq_left hs]
  · have hge : m + 1 - c ≤ c := by omega
    have hs : (m + 1 - c) + 1 ≤ c + 1 := by omega
    rw [Nat.min_eq_right hge, Nat.min_eq_right hs]

end Hypertournaments
