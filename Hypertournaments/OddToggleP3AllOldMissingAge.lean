import Hypertournaments.OddToggleP3AllOldMissingBlock
import Hypertournaments.OddToggleP3ProtectedFacets
import Hypertournaments.OddToggleP3SwitchingParity
import Hypertournaments.SwitchingShift

/-!
# A single missing block certifies all-old p3 packet admissibility

For an all-old packet of a genuine one-point p3 side, omission of
any one old block annihilates every raw facet via the actual
full-transversal potential support. Two adjacent raw facets are
therefore both zero, excluding homogeneous type; the all-zero raw
facet packet also has even parity, so it lies in switchingAllowed.
Thus the packet is in the forbidden-homogeneous toggleZero family.

This finishes the missing-block branch of all-old side packets.
The all-blocks-present branch requires actual occupancy geometry.
-/

namespace Hypertournaments

/-- Every genuine all-old packet omitting at least one base block
lies in the exceptional n=4k+3 allowed age, independent of W,L. -/
theorem p3AllOldSidePacket_allowed_of_missing_block
    (k t : ℕ) {V : Type*} [LinearOrder V]
    (old : Fin ((4*k+2)*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin (4*k+2)))
    (W L : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (f : Fin (4*k+4) ↪o V)
    (hfresh : fresh ∉ tupleVertices f.toEmbedding)
    (i : Fin (4*k+2))
    (hmissing : ∀ v : Fin ((4*k+2)*t),
       old v ∈ tupleVertices f.toEmbedding →
         p3BlockNumber t v ≠ i.val) :
    localIndex (p3SideHyper (4*k+2) t old fresh eligible W L)
      f.toEmbedding ∈ toggleZero (switchingAllowed (4*k+3)) := by
  let A := p3SideHyper (4*k+2) t old fresh eligible W L
  have hraw : ∀ q : Fin (4*k+4),
      A.orient (facet f.toEmbedding q) = false := by
    simpa only [show (4*k+2)+2=4*k+4 by omega] using
      (p3AllOldSidePacket_all_raw_facets_zero_of_missing_block
        (4*k+2) t old fresh eligible W L f hfresh i hmissing)
  let q0 : Fin (4*k+4) := ⟨0, by omega⟩
  let q1 : Fin (4*k+4) := ⟨1, by omega⟩
  have hpar : decide (q0.val%2=1) ≠ decide (q1.val%2=1) := by
    simp [q0, q1]
  have hnot : localIndex A f.toEmbedding ≠ 0 :=
    A.localIndex_ne_zero_of_oppositeParity_zeroRaw
      f q0 q1 hpar (hraw q0) (hraw q1)
  have hfilter :
      (Finset.univ.filter
        (fun q : Fin (4*k+4) => A.orient (facet f.toEmbedding q) = true)) =
          ∅ := by
    ext q
    simp [hraw q]
  have hcount :
      boolPacketPositiveCount
        (fun q : Fin (4*k+4) => A.orient (facet f.toEmbedding q)) = 0 := by
    change (Finset.univ.filter
      (fun q : Fin (4*k+4) => A.orient (facet f.toEmbedding q) = true)).card = 0
    rw [hfilter]
    rfl
  have hswitch : localIndex A f.toEmbedding ∈
      switchingAllowed (4*k+3) := by
    apply (A.p3SwitchingAllowed_iff_rawFacetParityEven k f.toEmbedding).mpr
    simp [hcount]
  change (if localIndex A f.toEmbedding = 0
      then localIndex A f.toEmbedding ∉ switchingAllowed (4*k+3)
      else localIndex A f.toEmbedding ∈ switchingAllowed (4*k+3))
  simpa [hnot] using hswitch

end Hypertournaments
