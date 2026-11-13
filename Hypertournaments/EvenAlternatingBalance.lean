import Lean.Elab.Tactic.Omega
import Hypertournaments.EvenSuspensionPacket

/-!
# Balanced alternating normalized facets in even arity

For n=2k, a packet of n facets with constant positive raw orientation
has normalized signs true exactly at the odd positions 1,3,...,2k-1.
There are exactly k of these positions.

Together with the separately proved three-pad packet formula, this
is the complete Boolean counting calculation for the three-pad case
of the even suspension. Its geometric facet identity is still a
separate construction-specific obligation.
-/

namespace Hypertournaments

/-- For any even packet length 2k, the indicator of an odd coordinate
has exactly k positive entries. -/
theorem boolPacketPositiveCount_alternating_even (k : ℕ) :
    boolPacketPositiveCount
      (fun i : Fin (2 * k) => decide (i.val % 2 = 1)) = k := by
  induction k with
  | zero =>
      decide
  | succ k ih =>
      let bits : Fin (2 * k) → Bool :=
        fun i => decide (i.val % 2 = 1)
      have htail (i : Fin (2 * k)) :
          decide ((i.succ.succ).val % 2 = 1) = bits i := by
        have hmod : (i.succ.succ).val % 2 = i.val % 2 := by
          simp only [Fin.val_succ]
          omega
        change decide ((i.succ.succ).val % 2 = 1) =
          decide (i.val % 2 = 1)
        rw [hmod]
      have hbits :
          (fun i : Fin (2 * k + 2) => decide (i.val % 2 = 1)) =
            Fin.cons false (Fin.cons true bits) := by
        funext i
        refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun t => ?_) j) i
        · rfl
        · rfl
        · simpa only [Fin.cons_succ] using htail t
      have hstep :
          boolPacketPositiveCount
            (fun i : Fin (2 * k + 2) => decide (i.val % 2 = 1)) =
              k + 1 := by
        rw [hbits, boolPacketPositiveCount_cons, boolPacketPositiveCount_cons]
        simp [bits, ih] <;> omega
      simpa [Nat.mul_succ] using hstep

/-- All three auxiliary pad facets of the even suspension have
normalized signs (b,!b,b), while the 2k remaining constant-sign raw
facets have a balanced alternating normalization. The resulting
local type is central, independently of the arbitrary old sign b. -/
theorem boolPacketMinority_even_suspension_three_pads (k : ℕ) (b : Bool) :
    min
      (boolPacketPositiveCount
        (Fin.cons b (Fin.cons (!b) (Fin.cons b
          (fun i : Fin (2 * k) => decide (i.val % 2 = 1))))))
      ((2 * k + 3) -
        boolPacketPositiveCount
          (Fin.cons b (Fin.cons (!b) (Fin.cons b
            (fun i : Fin (2 * k) => decide (i.val % 2 = 1)))))) =
        k + 1 := by
  exact boolPacketMinority_three_pad_central k b
    (fun i : Fin (2 * k) => decide (i.val % 2 = 1))
    (boolPacketPositiveCount_alternating_even k)

end Hypertournaments
