import Hypertournaments.OddToggleP1JointEndpointSigns
import Hypertournaments.OddToggleP1MixedPacketOrder
import Hypertournaments.OddToggleP1LinkDisagreementSupport
import Hypertournaments.CanonicalIncreasingFacetSign

/-!
# Actual homogeneous mixed p1 packets can only use eligible core edges

In the canonical two-point joint for the exceptional class n=4k+5,
every mixed (n+1)-packet omits two old vertices. Its final two
increasing facet deletions are the two newly added endpoints.
If the actual intrinsic local index is homogeneous (zero), those
facet signs must disagree, while preserving either source side
identifies them with the canonical right/left link-table bits.
Thus their disagreement is forced, and the omitted old pair must
lie in the exact seven-edge eligible core graph.

No abstract graph or synthetic Boolean coloring is assumed.
-/

namespace Hypertournaments

/-- In any genuine joint of the two explicit one-point sides,
a homogeneous mixed packet missing distinct old v,w forces the
canonical left and right link bits at v,w to disagree. -/
theorem p1Joint_homogeneous_mixed_link_disagreement
    (k : ℕ) (v w : Fin (4*k+6)) (hvne : v ≠ w)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hEL : Preserves (p1SideHyper k true) E
      (leftJointInclusion (4*k+6)))
    (hER : Preserves (p1SideHyper k false) E
      (rightJointInclusion (4*k+6)))
    (hQ : (p1JointMixedPacket k v w).card = 4*k+6)
    (hzero : localIndex E
      ((p1JointMixedPacket k v w).orderEmbOfFin hQ).toEmbedding = 0) :
    p1CanonicalLink k true v w ≠
      p1CanonicalLink k false v w := by
  let Q : Finset (Fin (4*k+6+2)) := p1JointMixedPacket k v w
  let g : Fin (4*k+6) ↪o Fin (4*k+6+2) := Q.orderEmbOfFin hQ
  let i0 : Fin (4*k+6) := ⟨4*k+4, by omega⟩
  let i1 : Fin (4*k+6) := ⟨4*k+5, by omega⟩
  have hsorted := p1JointMixedPacket_sorted_endpoints k v w hvne hQ
  have hleft : g i0 = p1JointLeftNew k := hsorted.1
  have hright : g i1 = p1JointRightNew k := hsorted.2
  have hverts : tupleVertices g.toEmbedding = Q := by
    simpa [tupleVertices, g] using
      (Finset.image_orderEmbOfFin_univ Q hQ)
  have hrawLeft :
      E.orient (facet g.toEmbedding i0) =
        p1CanonicalLink k false v w := by
    calc
      E.orient (facet g.toEmbedding i0) =
          E.canonicalSignTable
            ((tupleVertices g.toEmbedding).erase (g i0)) :=
        E.orient_facet_eq_canonical_erase g i0
      _ = E.canonicalSignTable
          ((p1JointMixedPacket k v w).erase (p1JointLeftNew k)) := by
        rw [hverts, hleft]
      _ = p1CanonicalLink k false v w :=
        p1JointMixed_right_canonicalSign k v w hvne E hER
  have hrawRight :
      E.orient (facet g.toEmbedding i1) =
        p1CanonicalLink k true v w := by
    calc
      E.orient (facet g.toEmbedding i1) =
          E.canonicalSignTable
            ((tupleVertices g.toEmbedding).erase (g i1)) :=
        E.orient_facet_eq_canonical_erase g i1
      _ = E.canonicalSignTable
          ((p1JointMixedPacket k v w).erase (p1JointRightNew k)) := by
        rw [hverts, hright]
      _ = p1CanonicalLink k true v w :=
        p1JointMixed_left_canonicalSign k v w hvne E hEL
  have hne :
      E.orient (facet g.toEmbedding i0) ≠
        E.orient (facet g.toEmbedding i1) :=
    E.p1Homogeneous_lastTwo_raw_ne k g.toEmbedding hzero
  intro heq
  exact hne (hrawLeft.trans (heq.symm.trans hrawRight.symm))

/-- Actual homogeneous mixed packets are supported on the
specified seven eligible edges of the six-vertex core. -/
theorem p1Joint_homogeneous_mixed_core_support
    (k : ℕ) (v w : Fin (4*k+6)) (hvne : v ≠ w)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hEL : Preserves (p1SideHyper k true) E
      (leftJointInclusion (4*k+6)))
    (hER : Preserves (p1SideHyper k false) E
      (rightJointInclusion (4*k+6)))
    (hQ : (p1JointMixedPacket k v w).card = 4*k+6)
    (hzero : localIndex E
      ((p1JointMixedPacket k v w).orderEmbOfFin hQ).toEmbedding = 0) :
    ∃ i j : Fin 6, v = p1CoreAt k i ∧
      w = p1CoreAt k j ∧ p1CoreEligible i j := by
  exact p1CanonicalLink_disagreement_support k v w
    (p1Joint_homogeneous_mixed_link_disagreement
      k v w hvne E hEL hER hQ hzero)

end Hypertournaments
