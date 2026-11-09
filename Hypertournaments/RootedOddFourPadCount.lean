import Hypertournaments.EvenAlternatingBalance

/-!
# Four-pad Boolean centrality in rooted odd suspensions

For odd source arity n = 2k+1, the high (n+3)-packet has
2k+4 normalized facet signs. A four-pad packet has the first four
facet signs (b,!b,b,!b), with a balanced alternating tail of 2k
remaining facets. The first four contribute precisely two positive
signs irrespective of b, and the tail contributes k positives,
so the high minority index is exactly its center k+2.

This module proves pure finite Boolean identities and does not
claim the source-specific geometric facet representation.
-/

namespace Hypertournaments

/-- Four successive alternating raw-equal facets contribute exactly
two positive normalized signs, regardless of their common raw sign. -/
theorem boolPacketPositiveCount_four_pad
    {m : ℕ} (b : Bool) (bits : Fin m → Bool) :
    boolPacketPositiveCount
      (Fin.cons b (Fin.cons (!b) (Fin.cons b
        (Fin.cons (!b) bits)))) =
      2 + boolPacketPositiveCount bits := by
  simp only [boolPacketPositiveCount_cons]
  cases b <;> simp <;> omega

/-- A balanced tail gives the exact central minority for a packet
whose initial four normalized facets have the alternating pattern. -/
theorem boolPacketMinority_four_pad_central
    (k : ℕ) (b : Bool) (bits : Fin (2 * k) → Bool)
    (hbalanced : boolPacketPositiveCount bits = k) :
    min
      (boolPacketPositiveCount
        (Fin.cons b (Fin.cons (!b) (Fin.cons b
          (Fin.cons (!b) bits)))))
      ((2 * k + 4) -
        boolPacketPositiveCount
          (Fin.cons b (Fin.cons (!b) (Fin.cons b
            (Fin.cons (!b) bits))))) =
      k + 2 := by
  rw [boolPacketPositiveCount_four_pad, hbalanced]
  omega

/-- The completely explicit Boolean four-pad packet with a positive
raw-sign alternating tail has exact central local type k+2. -/
theorem boolPacketMinority_rooted_odd_four_pads
    (k : ℕ) (b : Bool) :
    min
      (boolPacketPositiveCount
        (Fin.cons b (Fin.cons (!b) (Fin.cons b
          (Fin.cons (!b)
            (fun i : Fin (2 * k) => decide (i.val % 2 = 1)))))))
      ((2 * k + 4) -
        boolPacketPositiveCount
          (Fin.cons b (Fin.cons (!b) (Fin.cons b
            (Fin.cons (!b)
              (fun i : Fin (2 * k) => decide (i.val % 2 = 1))))))) =
      k + 2 := by
  exact boolPacketMinority_four_pad_central k b
    (fun i : Fin (2 * k) => decide (i.val % 2 = 1))
    (boolPacketPositiveCount_alternating_even k)

end Hypertournaments
