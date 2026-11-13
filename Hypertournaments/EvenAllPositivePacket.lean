import Lean.Elab.Tactic.Omega
import Hypertournaments.EvenAlternatingBalance

/-!
# Odd-length alternating normalized facet packets

In an even-arity suspension with n=2k, an (n+3)-vertex packet that
has no two-pad facets has positive raw orientation on every (n+2)-facet.
The alternating normalization of an odd-length packet of 2k+3 facets
then has k+2 positive and k+1 negative signs, so its local type is
central (k+1).

This module proves the parity counting fact uniformly for all k,
independently of the separate geometry establishing the facet
signs in the actual suspension.
-/

namespace Hypertournaments

/-- In an alternating Boolean word of length 2k+3 beginning with
true, there are exactly k+2 positive entries. -/
theorem boolPacketPositiveCount_alternating_odd (k : ℕ) :
    boolPacketPositiveCount
      (fun i : Fin (2 * k + 3) => decide (i.val % 2 = 0)) =
        k + 2 := by
  have hfun :
      (fun i : Fin (2 * k + 3) => decide (i.val % 2 = 0)) =
      Fin.cons true
        (fun i : Fin (2 * k + 2) => decide (i.val % 2 = 1)) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · have hj : (j.succ).val = j.val + 1 := rfl
      change decide ((j.succ).val % 2 = 0) =
        decide (j.val % 2 = 1)
      rw [hj]
      by_cases hodd : j.val % 2 = 1
      · have hnext : (j.val + 1) % 2 = 0 := by omega
        simp [hodd, hnext]
      · have hnext : (j.val + 1) % 2 ≠ 0 := by omega
        simp [hodd, hnext]
  have hev :
      boolPacketPositiveCount
        (fun i : Fin (2 * k + 2) => decide (i.val % 2 = 1)) =
          k + 1 := by
    simpa only [Nat.mul_succ] using
      (boolPacketPositiveCount_alternating_even (k + 1))
  rw [hfun, boolPacketPositiveCount_cons, hev]
  simp <;> omega

/-- The local index of an odd-length alternating normalized packet
with all raw signs positive is the central type k+1. -/
theorem boolPacketMinority_all_positive_odd (k : ℕ) :
    min
      (boolPacketPositiveCount
        (fun i : Fin (2 * k + 3) => decide (i.val % 2 = 0)))
      ((2 * k + 3) -
        boolPacketPositiveCount
          (fun i : Fin (2 * k + 3) => decide (i.val % 2 = 0))) =
          k + 1 := by
  rw [boolPacketPositiveCount_alternating_odd]
  omega

end Hypertournaments
