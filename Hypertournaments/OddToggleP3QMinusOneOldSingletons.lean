import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP3SixRepeatCardinal
import Hypertournaments.OddToggleP3SortedImageCard

/-!
# The q=m-1 old-packet singleton theorem for the p3 side age

Take an actual subset U of the old base with |U|=m+1.
If each old block other than a designated missing block is
occupied, the sorted block-label word has at least m-1=N-2
different values. It is monotone because the blocks are
consecutive. Hence the six-edge repeated-label bound applies
and gives globally singleton block positions of opposite
deletion parities.

This theorem closes the pure old-subset geometry of the
q=m-1 branch for every m≥6. Its transfer to the true one-fresh
packet (whose fresh point is last in canonical coordinates)
and the final side admissibility theorem are separate.
-/

namespace Hypertournaments

/-- Every q=m-1 old packet U (including any extra duplicated
vertices) has opposite-parity globally singleton block labels
in its actual canonical increasing enumeration. -/
theorem p3Sorted_qMinusOne_oppositeParity_singletons
    (m t : ℕ) (hm : 6 ≤ m)
    (U : Finset (Fin (m*t))) (hU : U.card = m+1)
    (missing : Fin m)
    (hOthers : ∀ i : Fin m, i ≠ missing →
      0 < p3BlockOccupancy m t U i) :
    ∃ x y : Fin (m+1),
      x.val%2=0 ∧ y.val%2=1 ∧
      (∀ z : Fin (m+1),
        p3BlockNumber t (U.orderEmbOfFin hU z) =
          p3BlockNumber t (U.orderEmbOfFin hU x) → z=x) ∧
      (∀ z : Fin (m+1),
        p3BlockNumber t (U.orderEmbOfFin hU z) =
          p3BlockNumber t (U.orderEmbOfFin hU y) → z=y) := by
  let B : Fin (m+1) → ℕ :=
    fun z => p3BlockNumber t (U.orderEmbOfFin hU z)
  have hN : 7 ≤ m+1 := by omega
  have hMono : Monotone B :=
    p3SortedOldPacket_block_monotone U hU
  have hImage :
      (m+1)-2 ≤
        ((Finset.univ : Finset (Fin (m+1))).image B).card :=
    p3SortedPacket_qMinusOne_image_large m t U hU missing hOthers
  simpa only [B] using
    (p3SixDistinctLabels_oppositeParity_singletons
      hN B hMono hImage)

end Hypertournaments
