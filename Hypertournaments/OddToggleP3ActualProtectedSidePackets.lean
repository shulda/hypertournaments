import Hypertournaments.OddToggleP3ExplicitSideSupport
import Hypertournaments.OddToggleP3PotentialSwitching
import Hypertournaments.OddToggleP3ProtectedFacets

/-!
# Genuine protected singleton zero facets on p3 one-point sides

An explicit p3 side potential has nonzero entries only on sets
meeting every protected block. If a protected block has a unique
old vertex v in a packet X, deleting v removes the entire block.
Hence its actual intrinsic side hypertournament raw facet
orientation is FALSE, regardless of W and L.

For finite side vertex set Fin a, two such protected singleton
old vertices at opposite canonical deletion parities force the
genuine packet into the exceptional homogeneous-free p3 age:
zero raw facets exclude type zero, and potential-induced
switching parity holds automatically by δ²=0.

This is a pointwise ACTUAL-Hyper criterion. It does not assert
that every packet in the concrete random sides has the required
protected singleton pair; all-old and low-occupancy packets use
other already certified zero-facet mechanisms.
-/

namespace Hypertournaments

/-- The facet deleting a unique vertex of a protected block
has actual intrinsic orientation false in the p3 one-point side. -/
theorem p3SidePacket_raw_zero_at_protected_singleton
    (m t : ℕ) {V : Type*} [LinearOrder V]
    (old : Fin (m*t) ↪ V) (fresh : V)
    (eligible protectedBlocks : Finset (Fin m))
    (hdisjoint : Disjoint eligible protectedBlocks)
    (W L : Finset (Fin (m*t)) → ZMod 2)
    (f : Fin (m+2) ↪o V) (q : Fin (m+2))
    (i : Fin m) (hi : i ∈ protectedBlocks)
    (v : Fin (m*t)) (hvertex : old v = f q)
    (hlabel : p3BlockNumber t v = i.val)
    (hunique : ∀ w : Fin (m*t),
      old w ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t w = i.val → w = v) :
    (p3SideHyper m t old fresh eligible W L).orient
      (facet f.toEmbedding q) = false := by
  have hdel :
      tupleVertices (facet f.toEmbedding q) =
        (tupleVertices f.toEmbedding).erase (old v) := by
    rw [tupleVertices_facet_eq_erase f.toEmbedding q]
    rw [← hvertex]
  have hzero :=
    p3SidePotential_coboundary_zero_of_unique_protected
      m t old fresh eligible protectedBlocks hdisjoint
      W L (tupleVertices f.toEmbedding) v i hi hlabel hunique
  have hz : coboundary
      (p3SidePotential m t old fresh eligible W L)
      (tupleVertices (facet f.toEmbedding q)) = 0 := by
    rw [hdel]
    exact hzero
  change (Hyper.fromOrderedSigns
    (fun Q => p3ZMod2ToBool
      (coboundary (p3SidePotential m t old fresh eligible W L) Q))).orient
      (facet f.toEmbedding q) = false
  rw [fromOrderedSigns_facet_increasing
    (fun Q => p3ZMod2ToBool
      (coboundary (p3SidePotential m t old fresh eligible W L) Q)) f q]
  simp [p3ZMod2ToBool, hz]

/-- Two actual protected singleton old vertices with opposite
facet-position parity suffice to certify a genuine p3 side
packet as belonging to the exceptional allowed age. -/
theorem p3SidePacket_allowed_of_two_protected_singletons
    (k t a : ℕ)
    (old : Fin ((4*k+2)*t) ↪ Fin a) (fresh : Fin a)
    (eligible protectedBlocks : Finset (Fin (4*k+2)))
    (hdisjoint : Disjoint eligible protectedBlocks)
    (W L : Finset (Fin ((4*k+2)*t)) → ZMod 2)
    (f : Fin (4*k+4) ↪o Fin a)
    (x y : Fin (4*k+4))
    (hpar : decide (x.val%2=1) ≠ decide (y.val%2=1))
    (i j : Fin (4*k+2)) (hi : i ∈ protectedBlocks)
    (hj : j ∈ protectedBlocks)
    (v w : Fin ((4*k+2)*t))
    (hv : old v = f x) (hw : old w = f y)
    (hvi : p3BlockNumber t v = i.val)
    (hwj : p3BlockNumber t w = j.val)
    (huniquev : ∀ u : Fin ((4*k+2)*t),
      old u ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t u = i.val → u = v)
    (huniquew : ∀ u : Fin ((4*k+2)*t),
      old u ∈ tupleVertices f.toEmbedding →
      p3BlockNumber t u = j.val → u = w) :
    localIndex (p3SideHyper (4*k+2) t old fresh eligible W L)
      f.toEmbedding ∈
        toggleZero (switchingAllowed (4*k+3)) := by
  let A := p3SideHyper (4*k+2) t old fresh eligible W L
  have hrawx : A.orient (facet f.toEmbedding x) = false := by
    change (p3SideHyper ((4*k+2)) t old fresh eligible W L).orient
      (facet f.toEmbedding x) = false
    exact p3SidePacket_raw_zero_at_protected_singleton
      (4*k+2) t old fresh eligible protectedBlocks hdisjoint
      W L f x i hi v hv hvi huniquev
  have hrawy : A.orient (facet f.toEmbedding y) = false := by
    change (p3SideHyper ((4*k+2)) t old fresh eligible W L).orient
      (facet f.toEmbedding y) = false
    exact p3SidePacket_raw_zero_at_protected_singleton
      (4*k+2) t old fresh eligible protectedBlocks hdisjoint
      W L f y j hj w hw hwj huniquew
  have hnot : localIndex A f.toEmbedding ≠ 0 :=
    A.localIndex_ne_zero_of_oppositeParity_zeroRaw
      f x y hpar hrawx hrawy
  have hswitch : localIndex A f.toEmbedding ∈
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
  simpa [hnot] using hswitch

end Hypertournaments
