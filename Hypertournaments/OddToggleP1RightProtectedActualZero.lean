import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP1SideHomogeneousBridge
import Hypertournaments.OddToggleP1RightProtectedPositions
import Hypertournaments.OddToggleP1RowMatchesBase
import Hypertournaments.OddToggleP1ActualRawCount

/-!
# Actual intrinsic homogeneous types of the two protected right p1 packets

For the right one-point extension in arity 4k+5, precisely the
omitted old core vertices a0 and a4 have nonmatching link-row
parity. We show they are genuinely homogeneous local packets:
their normalized facet signs are constant, with respective phases
false and true. This is unconditional, uniformly in k.
-/

namespace Hypertournaments

theorem p1RightCoreZero_packet_localIndex (k : ℕ)
    (hQ : (p1SidePacketOmitOld k (p1CoreAt k (0 : Fin 6))).card = 4*k+6) :
    localIndex (p1SideHyper k false)
      ((p1SidePacketOmitOld k (p1CoreAt k (0 : Fin 6))).orderEmbOfFin hQ).toEmbedding = 0 := by
  apply p1SidePacket_localIndex_zero_of_link k (p1CoreAt k (0 : Fin 6)) false
  · intro w hw
    simpa [p1CoreAt] using (p1RightCoreZero_old_position k w hw)
  · rw [p1BaseVertexBit_core]
    have hp : (4*k+5)%2=1 := by omega
    simp [p1CoreBaseBit, hp]

theorem p1RightCoreFour_packet_localIndex (k : ℕ)
    (hQ : (p1SidePacketOmitOld k (p1CoreAt k (4 : Fin 6))).card = 4*k+6) :
    localIndex (p1SideHyper k false)
      ((p1SidePacketOmitOld k (p1CoreAt k (4 : Fin 6))).orderEmbOfFin hQ).toEmbedding = 0 := by
  apply p1SidePacket_localIndex_zero_of_link k (p1CoreAt k (4 : Fin 6)) true
  · intro w hw
    rw [p1RightCoreFour_old_position k w hw]
    change Bool.not (decide (((if w.val < 4*k+4 then
      w.val else w.val-1)%2)=1)) =
      Bool.xor true (decide (((if w.val < 4*k+4 then
        w.val else w.val-1)%2)=1))
    cases h : decide (((if w.val < 4*k+4 then
      w.val else w.val-1)%2)=1) <;> rfl
  · rw [p1BaseVertexBit_core]
    have hp : (4*k+5)%2=1 := by omega
    simp [p1CoreBaseBit, hp]

end Hypertournaments
