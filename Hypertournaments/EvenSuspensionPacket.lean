import Lean.Elab.Tactic.Omega
import Hypertournaments.TwoPadPacketCount

/-!
# The three-pad packet in an even-arity suspension

The even two-coordinate suspension has one delicate local case:
an (n+3)-set containing exactly three padding vertices, where n=2k.
Deleting the three pads produces the same old n-facet orientation b
in alternating normalized positions (b,!b,b). The remaining 2k
facets have constant positive raw sign; their normalized packet has
exactly k positive signs.

Consequently, regardless of b, the whole new packet of length
2k+3 has minority count k+1, its central type. These lemmas are
uniform in k; they involve actual Boolean facet packets and make
no assumption about a specific finite source witness.

The separate geometric proof that the suspension table has this
packet shape remains to be established.
-/

namespace Hypertournaments

/-- The three new pad facets contribute exactly one positive sign
when their common raw orientation is negative, and two when positive. -/
theorem boolPacketPositiveCount_three_pad
    {m : ℕ} (b : Bool) (bits : Fin m → Bool) :
    boolPacketPositiveCount
        (Fin.cons b (Fin.cons (!b) (Fin.cons b bits))) =
      (if b then 2 else 1) + boolPacketPositiveCount bits := by
  simp only [boolPacketPositiveCount_cons]
  cases b <;> simp <;> omega

/-- If n=2k old facets have a balanced normalized packet (k
positives and k negatives), then three pad facets with raw sign b
produce exactly the central local type k+1 in arity n+2. -/
theorem boolPacketMinority_three_pad_central
    (k : ℕ) (b : Bool) (bits : Fin (2 * k) → Bool)
    (hbalanced : boolPacketPositiveCount bits = k) :
    min
        (boolPacketPositiveCount
          (Fin.cons b (Fin.cons (!b) (Fin.cons b bits))))
        ((2 * k + 3) -
          boolPacketPositiveCount
            (Fin.cons b (Fin.cons (!b) (Fin.cons b bits)))) =
      k + 1 := by
  rw [boolPacketPositiveCount_three_pad, hbalanced]
  cases b <;> simp <;> omega

/-- The exact count, useful when deriving the signs of a concrete
suspension rather than only its minority index. -/
theorem boolPacketPositiveCount_three_pad_of_balanced
    (k : ℕ) (b : Bool) (bits : Fin (2 * k) → Bool)
    (hbalanced : boolPacketPositiveCount bits = k) :
    boolPacketPositiveCount
        (Fin.cons b (Fin.cons (!b) (Fin.cons b bits))) =
      k + (if b then 2 else 1) := by
  rw [boolPacketPositiveCount_three_pad, hbalanced]
  omega

end Hypertournaments
