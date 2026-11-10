import Hypertournaments.OddToggleP1CoreRows
import Hypertournaments.OddToggleP1PadParity

/-!
# Exact right-side homogeneous row templates at core vertices a0 and a4

In the explicit n ≡ 1 (mod 4) bad one-point span, the right-hand
link row at core vertex a0 has raw signs equal to parity of the
facet position after omitting a0. The row at a4 has the Boolean
complement of the same alternating word after omitting a4.

This file checks those *literal* six-core tables and the pad-to-core
links. No age or AP statement is assumed. These are the local
combinatorial facts needed for the two exceptional zero-type
right-hand side packets in the p1 construction.
-/

namespace Hypertournaments

/-- For every other core vertex, the right link from a0 has the
alternating sign determined by its coordinate after erasing a0. -/
theorem p1RightCoreZero_alternating :
    ∀ j : Fin 6, j ≠ 0 →
      p1CoreRightSymBit 0 j =
        decide (((j.val-1)%2)=1) := by
  decide

/-- For every other core vertex, the right link from a4 has
the complementary alternating sign after erasing a4. -/
theorem p1RightCoreFour_complement_alternating :
    ∀ j : Fin 6, j ≠ 4 →
      p1CoreRightSymBit 4 j =
        !(decide (((if j.val < 4 then j.val else j.val-1)%2)=1)) := by
  decide

/-- The right pad-core sign towards a0 reads the parity of the
pad position directly (a0 follows all pads). -/
theorem p1RightPadZero_alternating (k : ℕ)
    (s : Fin (2*(2*k))) :
    p1RightPadCoreBit k s (0 : Fin 6) =
      decide (s.val%2=1) := by
  simp [p1RightPadCoreBit]

/-- The right pad-core sign towards a4 is its Boolean complement. -/
theorem p1RightPadFour_complement_alternating (k : ℕ)
    (s : Fin (2*(2*k))) :
    p1RightPadCoreBit k s (4 : Fin 6) =
      !(decide (s.val%2=1)) := by
  have h := p1PadParity_complement s.val
  simp only [p1RightPadCoreBit, if_neg (by decide : (4 : Fin 6) ≠ 0),
    if_pos (by decide : (4 : Fin 6) = 4)]
  exact h

end Hypertournaments
