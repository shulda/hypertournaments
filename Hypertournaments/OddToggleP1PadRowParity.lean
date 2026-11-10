import Hypertournaments.OddToggleP1PadParity
import Hypertournaments.RootedOddFourPadLocalIndex

/-!
# The six canonical pad-to-core link signs have odd row parity

For the explicit p1 one-point span, each pad p_s is linked to
the six core vertices by a six-bit word. It has four constant
positive bits and exactly one positive bit among core a0,a4:
the two latter entries are complementary according to s mod 2.

Hence every right pad row has exactly five positive links, while
the original (precanonicalized) left pad row has one positive link.
Both counts are odd, matching the positive base bit of any pad.
The canonicalized left table uses the right pad row; the parity
remains odd because the complement of six bits preserves parity.

This exact all-arity finite fact is another independent component
of side age membership for the explicit p1 diagram.
-/

namespace Hypertournaments

/-- On any integer the two parity-bit tests are complements. -/
theorem p1PadParity_complement (s : ℕ) :
    decide (s % 2 = 0) = !(decide (s % 2 = 1)) := by
  have hcases : s % 2 = 0 ∨ s % 2 = 1 := by omega
  rcases hcases with hzero | hone
  · have hnot : s % 2 ≠ 1 := by omega
    simp [hzero, hnot]
  · have hnot : s % 2 ≠ 0 := by omega
    simp [hone, hnot]

/-- Every right pad has exactly five positive core links,
uniformly in the number 4k of pads. -/
theorem p1RightPadCore_row_positiveCount
    (k : ℕ) (s : Fin (2*(2*k))) :
    boolPacketPositiveCount
      (fun j : Fin 6 => p1RightPadCoreBit k s j) = 5 := by
  have hcomp := p1PadParity_complement s.val
  have hbits :
      (fun j : Fin 6 => p1RightPadCoreBit k s j) =
        (fun j : Fin 6 =>
          if j = 0 then decide (s.val % 2 = 1)
          else if j = 4 then !(decide (s.val % 2 = 1))
          else true) := by
    funext j
    simp [p1RightPadCoreBit, hcomp]
  rw [hbits]
  cases hpar : decide (s.val % 2 = 1) <;> decide

/-- The pre-canonical left pad word is the Boolean complement;
of six bits, hence it contains exactly one positive link. -/
theorem p1LeftPadCore_row_positiveCount
    (k : ℕ) (s : Fin (2*(2*k))) :
    boolPacketPositiveCount
      (fun j : Fin 6 => p1LeftPadCoreBit k s j) = 1 := by
  change boolPacketPositiveCount
    (fun j : Fin 6 => !(p1RightPadCoreBit k s j)) = 1
  rw [boolPacketPositiveCount_not,
      p1RightPadCore_row_positiveCount k s]

end Hypertournaments
