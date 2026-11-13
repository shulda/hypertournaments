import Hypertournaments.RootedOddThreePadAbsentCount
import Hypertournaments.TwoPadPacketCount

/-!
# An intrinsic orientation-level three-pad minority-index shift

A high (n+3)-vertex local packet in an intrinsic (n+2)-hypertournament
has the old n-hypertournament normalized packet after replacing its
first sign b by (b,!b,b) exactly when it has the root-absent three-pad
geometry. This generic theorem turns that equality into the precise
local type shift +1. No sorting, root, or sign table is postulated by
the theorem itself: all geometry is isolated in its explicit packet
equality hypothesis.

This is the direct analogue of the already checked generic two-pad
type shift, but accommodates the three signs forced by an odd rooted
suspension's root-absent packet.
-/

namespace Hypertournaments

/-- If the normalized high packet is the old normalized packet with
its first bit b replaced by (b,!b,b), then the actual intrinsic high
local index equals the old intrinsic local index plus one. -/
theorem localIndex_threePad_prefix_shift_of_packet
    {n : ℕ} {W V : Type*}
    (A : Hyper n W) (D : Hyper (n+2) V)
    (g : Fin (n+1) ↪ W) (f : Fin (n+3) ↪ V)
    (hpacket :
      (fun i : Fin (n+3) => normalizedFacet D f i) =
        Fin.cons (normalizedFacet A g 0)
          (Fin.cons (!(normalizedFacet A g 0))
            (Fin.cons (normalizedFacet A g 0)
              (fun j : Fin n => normalizedFacet A g j.succ)))) :
    localIndex D f = localIndex A g + 1 := by
  have hold :
      (fun i : Fin (n+1) => normalizedFacet A g i) =
      Fin.cons (normalizedFacet A g 0)
        (fun j : Fin n => normalizedFacet A g j.succ) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · rfl
  change
    min
      (boolPacketPositiveCount
        (fun i : Fin (n+3) => normalizedFacet D f i))
      ((n+3) -
        boolPacketPositiveCount
          (fun i : Fin (n+3) => normalizedFacet D f i)) =
      min
        (boolPacketPositiveCount
          (fun i : Fin (n+1) => normalizedFacet A g i))
        ((n+1) -
          boolPacketPositiveCount
            (fun i : Fin (n+1) => normalizedFacet A g i)) + 1
  rw [hpacket, hold]
  exact boolPacketMinority_threePad_prefix_shift
    (normalizedFacet A g 0)
    (fun j : Fin n => normalizedFacet A g j.succ)

end Hypertournaments
