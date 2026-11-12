import Hypertournaments.OddToggleP3TwoMissingBlocks
import Hypertournaments.OddToggleP3ActualProtectedSidePackets

/-!
# Actual p3 side packets missing one block: singleton zero facets

When a side packet X is missing one old block b, deleting a
singleton vertex from any *other* old block c makes the resulting
facet miss BOTH b and c. Thus its genuine intrinsic side orientation
is false, regardless of the random W/L values, even if c is not
in the protected half. Two such singleton vertices at opposite
positions force the packet into the homogeneous-free switching age.

This is the exact intrinsic-Hyper zero-facet bridge needed for the
q=m-1 occupied-block branch. The separate finite occupancy argument
must still prove the existence of the required opposite-parity
singletons in every concrete q=m-1 packet.
-/

namespace Hypertournaments

/-- A packet missing block b acquires a second missing block c
upon deleting the unique old vertex of c, so the side coboundary
vanishes on the resulting true facet. -/
theorem p3SidePotential_coboundary_zero_of_missing_singleton
    (m t : ℕ) {V : Type*} [DecidableEq V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (X : Finset V)
    (v : Fin (m*t))
    (missing single : Fin m) (hDistinct : missing ≠ single)
    (hMissing : ∀ w : Fin (m*t), old w ∈ X →
      p3BlockNumber t w ≠ missing.val)
    (hUnique : ∀ w : Fin (m*t), old w ∈ X →
      p3BlockNumber t w = single.val → w = v) :
    coboundary (p3SidePotential m t old fresh eligible W L)
      (X.erase (old v)) = 0 := by
  apply p3SidePotential_coboundary_zero_of_two_missing_blocks
    m t old fresh eligible W L (X.erase (old v))
    missing single hDistinct
  · intro w hw
    exact hMissing w (Finset.mem_of_mem_erase hw)
  · intro w hw hBlock
    have hEq : w = v :=
      hUnique w (Finset.mem_of_mem_erase hw) hBlock
    have hNe : old w ≠ old v := (Finset.mem_erase.mp hw).1
    exact hNe (congrArg (fun z => old z) hEq)

/-- The local zero-coboundary statement is a zero orientation on
the actual facet of the concrete intrinsic one-point side. -/
theorem p3SidePacket_raw_zero_at_singleton_of_missing_block
    (m t : ℕ) {V : Type*} [LinearOrder V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible : Finset (Fin m))
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (f : Fin (m+2) ↪o V) (x : Fin (m+2))
    (v : Fin (m*t)) (hv : old v = f x)
    (missing single : Fin m) (hDistinct : missing ≠ single)
    (hMissing : ∀ w : Fin (m*t),
      old w ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t w ≠ missing.val)
    (hUnique : ∀ w : Fin (m*t),
      old w ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t w = single.val → w = v) :
    (p3SideHyper m t old fresh eligible W L).orient
      (facet f.toEmbedding x) = false := by
  have hFacet :
      tupleVertices (facet f.toEmbedding x) =
        (tupleVertices f.toEmbedding).erase (old v) := by
    have hh := tupleVertices_facet_eq_erase f.toEmbedding x
    change tupleVertices (facet f.toEmbedding x) =
      (tupleVertices f.toEmbedding).erase (f x) at hh
    rw [← hv] at hh
    exact hh
  have hz : coboundary (p3SidePotential m t old fresh eligible W L)
      (tupleVertices (facet f.toEmbedding x)) = 0 := by
    rw [hFacet]
    exact p3SidePotential_coboundary_zero_of_missing_singleton
      m t old fresh eligible W L (tupleVertices f.toEmbedding)
      v missing single hDistinct hMissing hUnique
  change (Hyper.fromOrderedSigns
      (fun Q => p3ZMod2ToBool
        (coboundary (p3SidePotential m t old fresh eligible W L) Q))).orient
      (facet f.toEmbedding x) = false
  rw [fromOrderedSigns_facet_increasing
    (fun Q => p3ZMod2ToBool
      (coboundary (p3SidePotential m t old fresh eligible W L) Q)) f x]
  simp [p3ZMod2ToBool, hz]

/-- If a genuine one-point side packet is missing one old block
and has singleton vertices of opposite deletion parity in other
blocks, it is automatically allowed, for arbitrary W and L.
No protected-half condition is required on these two vertices. -/
theorem p3SidePacket_allowed_of_missing_and_two_singletons
    (k t a : ℕ)
    (old : Fin ((4*k+2)*t) ↪ Fin a) (fresh : Fin a)
    (eligible : Finset (Fin (4*k+2)))
    (W L : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (f : Fin (4*k+4) ↪o Fin a)
    (missing : Fin (4*k+2))
    (hMissing : ∀ w : Fin ((4*k+2)*t),
      old w ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t w ≠ missing.val)
    (x y : Fin (4*k+4))
    (hParity : decide (x.val%2=1) ≠ decide (y.val%2=1))
    (i j : Fin (4*k+2))
    (hMissingI : missing ≠ i) (hMissingJ : missing ≠ j)
    (v w : Fin ((4*k+2)*t))
    (hv : old v = f x) (hw : old w = f y)
    (hUniqueV : ∀ u : Fin ((4*k+2)*t),
      old u ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t u = i.val → u = v)
    (hUniqueW : ∀ u : Fin ((4*k+2)*t),
      old u ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t u = j.val → u = w) :
    localIndex (p3SideHyper (4*k+2) t old fresh eligible W L)
      f.toEmbedding ∈
        toggleZero (switchingAllowed (4*k+3)) := by
  let A := p3SideHyper (4*k+2) t old fresh eligible W L
  have hzX : A.orient (facet f.toEmbedding x) = false := by
    change (p3SideHyper (4*k+2) t old fresh eligible W L).orient
      (facet f.toEmbedding x) = false
    exact p3SidePacket_raw_zero_at_singleton_of_missing_block
      (4*k+2) t old fresh eligible W L f x v hv
      missing i hMissingI hMissing hUniqueV
  have hzY : A.orient (facet f.toEmbedding y) = false := by
    change (p3SideHyper (4*k+2) t old fresh eligible W L).orient
      (facet f.toEmbedding y) = false
    exact p3SidePacket_raw_zero_at_singleton_of_missing_block
      (4*k+2) t old fresh eligible W L f y w hw
      missing j hMissingJ hMissing hUniqueW
  have hNotZero : localIndex A f.toEmbedding ≠ 0 :=
    A.localIndex_ne_zero_of_oppositeParity_zeroRaw
      f x y hParity hzX hzY
  have hSwitch : localIndex A f.toEmbedding ∈
      switchingAllowed (4*k+3) := by
    change localIndex
      (p3HyperFromPotential (4*k+3) a
        (p3SidePotential (4*k+2) t old fresh eligible W L))
      f.toEmbedding ∈ switchingAllowed (4*k+3)
    exact p3HyperFromPotential_switchingAllowed k a
      (p3SidePotential (4*k+2) t old fresh eligible W L) f
  change (if localIndex A f.toEmbedding = 0
    then localIndex A f.toEmbedding ∉ switchingAllowed (4*k+3)
    else localIndex A f.toEmbedding ∈ switchingAllowed (4*k+3))
  simpa [hNotZero] using hSwitch

end Hypertournaments
