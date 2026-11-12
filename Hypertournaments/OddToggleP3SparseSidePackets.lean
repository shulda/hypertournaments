import Hypertournaments.OddToggleP3TwoMissingBlocks
import Hypertournaments.OddToggleP3ProtectedFacets
import Hypertournaments.OddToggleP3SwitchingParity
import Hypertournaments.SwitchingShift

/-!
# Every raw facet is zero on a p3 side packet missing two old blocks

If a finite one-point side packet misses two distinct old block
indices, its raw facet sign is zero at EVERY deletion position.
This is a consequence of the exact support predicate for the
explicit p3 side potential, not of a random assignment assumption.

In the p3 congruence n=4k+3, the resulting packet is actually in
the forbidden-homogeneous exceptional toggleZero switching age:
the raw facet count is even, and any two adjacent zero facets
have opposite deletion parity, excluding localIndex zero.

This covers the q<=m-2 occupied-block case of the random side
admissibility proof. Remaining higher-occupancy cases are separate.
-/

namespace Hypertournaments

/-- On any genuine side packet lacking two old blocks, every
increasing-facet orientation is false. -/
theorem p3SidePacket_all_raw_facets_zero_of_two_missing_blocks
    (m t : ℕ) {V : Type*} [LinearOrder V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (f : Fin (m+2) ↪o V)
    (i j : Fin m) (hij : i ≠ j)
    (hi : ∀ v : Fin (m*t), old v ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t v ≠ i.val)
    (hj : ∀ v : Fin (m*t), old v ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t v ≠ j.val) :
    ∀ q : Fin (m+2),
      (p3SideHyper m t old fresh eligible W L).orient
        (facet f.toEmbedding q) = false := by
  intro q
  have hsub : tupleVertices (facet f.toEmbedding q) =
      (tupleVertices f.toEmbedding).erase (f q) :=
    tupleVertices_facet_eq_erase f.toEmbedding q
  have hz : coboundary (p3SidePotential m t old fresh eligible W L)
      (tupleVertices (facet f.toEmbedding q)) = 0 := by
    apply p3SidePotential_coboundary_zero_of_two_missing_blocks
      m t old fresh eligible W L
      (tupleVertices (facet f.toEmbedding q)) i j hij
    · intro v hv
      rw [hsub] at hv
      exact hi v (Finset.mem_of_mem_erase hv)
    · intro v hv
      rw [hsub] at hv
      exact hj v (Finset.mem_of_mem_erase hv)
  change (Hyper.fromOrderedSigns
    (fun Q => p3ZMod2ToBool
      (coboundary (p3SidePotential m t old fresh eligible W L) Q))).orient
    (facet f.toEmbedding q) = false
  rw [fromOrderedSigns_facet_increasing
    (fun Q => p3ZMod2ToBool
      (coboundary (p3SidePotential m t old fresh eligible W L) Q)) f q]
  simp [hz, p3ZMod2ToBool]

/-- The low-occupancy branch already lies in the exceptional p3
age, for any arbitrary side potential values W,L. -/
theorem p3SidePacket_allowed_of_two_missing_blocks
    (k t : ℕ) {V : Type*} [LinearOrder V]
    (old : Fin ((4*k+2)*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin (4*k+2)))
    (W L : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (f : Fin (4*k+4) ↪o V)
    (i j : Fin (4*k+2)) (hij : i ≠ j)
    (hi : ∀ v : Fin ((4*k+2)*t), old v ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t v ≠ i.val)
    (hj : ∀ v : Fin ((4*k+2)*t), old v ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t v ≠ j.val) :
    localIndex (p3SideHyper (4*k+2) t old fresh eligible W L)
      f.toEmbedding ∈ toggleZero (switchingAllowed (4*k+3)) := by
  have hraw : ∀ q : Fin (4*k+4),
      (p3SideHyper (4*k+2) t old fresh eligible W L).orient
        (facet f.toEmbedding q) = false := by
    simpa only [show (4*k+2)+2=4*k+4 by omega] using
      (p3SidePacket_all_raw_facets_zero_of_two_missing_blocks
        (4*k+2) t old fresh eligible W L f i j hij hi hj)
  let A := p3SideHyper (4*k+2) t old fresh eligible W L
  let q0 : Fin (4*k+4) := ⟨0, by omega⟩
  let q1 : Fin (4*k+4) := ⟨1, by omega⟩
  have hpar : decide (q0.val%2=1) ≠ decide (q1.val%2=1) := by
    simp [q0, q1]
  have hnot : localIndex A f.toEmbedding ≠ 0 :=
    A.localIndex_ne_zero_of_oppositeParity_zeroRaw
      f q0 q1 hpar (hraw q0) (hraw q1)
  have hrawA : ∀ q : Fin (4*k+4),
      A.orient (facet f.toEmbedding q) = false := hraw
  have hfilter :
      (Finset.univ.filter
        (fun q : Fin (4*k+4) => A.orient (facet f.toEmbedding q) = true)) =
          ∅ := by
    ext q
    simp [hrawA q]
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
