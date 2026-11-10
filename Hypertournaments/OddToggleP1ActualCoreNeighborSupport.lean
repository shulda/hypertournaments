import Hypertournaments.OddToggleP1NeighborCanonicalPair
import Hypertournaments.OddToggleP1JointForcedNeighbors
import Hypertournaments.OddToggleP1ActualMixedSupport
import Hypertournaments.OddToggleP1CanonicalLinks

/-!
# Actual seven-edge core support for the homogeneous-neighbor graph

Every neighbor pair of distinct old vertices in a canonical p1 joint
corresponds to the genuine mixed (n+1)-packet omitting precisely
those two old vertices. By the already certified source-to-joint
link-sign bridge, homogeneity forces this old pair to lie on an
eligible six-core edge.

The only potential old neighbors of a4 and a2 are therefore a2
and respectively a4,a5. This reduces the final degree-two forcing
to three explicit exclusions of nonmixed new-vertex neighbors
and one fixed edge from the right protected homogeneous packet.
-/

namespace Hypertournaments

theorem p1JointVertex_old_or_new (k : ℕ)
    (y : Fin (4*k+6+2)) :
    (∃ w : Fin (4*k+6), y = p1JointOld k w) ∨
    y = p1JointLeftNew k ∨ y = p1JointRightNew k := by
  by_cases hOld : y.val < 4*k+6
  · left
    refine ⟨⟨y.val, hOld⟩, ?_⟩
    apply Fin.ext
    rfl
  · right
    by_cases hLeft : y.val = 4*k+6
    · left
      apply Fin.ext
      exact hLeft
    · right
      apply Fin.ext
      change y.val = 4*k+6+1
      have hy := y.isLt
      omega

/-- A homogeneous old-old neighbor pair has two eligible core
coordinates, not merely an abstract graph edge. -/
theorem p1JointOldNeighbor_core_support (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hEL : Preserves (p1SideHyper k true) E
      (leftJointInclusion (4*k+6)))
    (hER : Preserves (p1SideHyper k false) E
      (rightJointInclusion (4*k+6)))
    (v w : Fin (4*k+6)) (hvw : v ≠ w)
    (hNeighbor : p1JointOld k w ∈
      p1JointHomogeneousNeighbors k E (p1JointOld k v)) :
    ∃ i j : Fin 6,
      v = p1CoreAt k i ∧ w = p1CoreAt k j ∧ p1CoreEligible i j := by
  have hxy : p1JointOld k v ≠ p1JointOld k w := by
    intro heq
    apply hvw
    apply Fin.ext
    have hv := congrArg Fin.val heq
    change v.val = w.val at hv
    exact hv
  have hz := (p1JointNeighbor_mem_iff_canonical_zero k E
    (p1JointOld k v) (p1JointOld k w) hxy).mp hNeighbor
  have hQ : (p1JointMixedPacket k v w).card = 4*k+6 :=
    p1JointMixedPacket_card k v w hvw
  have hzero :
      localIndex E
        ((p1JointMixedPacket k v w).orderEmbOfFin hQ).toEmbedding = 0 := by
    simpa only [p1JointDoubleDeletion, p1JointMixedPacket] using hz
  exact p1Joint_homogeneous_mixed_core_support
    k v w hvw E hEL hER hQ hzero

theorem p1JointCoreFour_old_neighbor_only_two (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hEL : Preserves (p1SideHyper k true) E
      (leftJointInclusion (4*k+6)))
    (hER : Preserves (p1SideHyper k false) E
      (rightJointInclusion (4*k+6)))
    (w : Fin (4*k+6))
    (h : p1JointOld k w ∈ p1JointHomogeneousNeighbors k E
      (p1JointOld k (p1CoreAt k (4 : Fin 6)))) :
    w = p1CoreAt k (2 : Fin 6) := by
  have hvw : p1CoreAt k (4 : Fin 6) ≠ w := by
    intro he
    have hh := p1JointHomogeneousNeighbors_ne_self k E
      (p1JointOld k (p1CoreAt k (4 : Fin 6)))
      (p1JointOld k w) h
    exact hh (congrArg (p1JointOld k) he.symm)
  obtain ⟨i,j,hi,hj,hel⟩ :=
    p1JointOldNeighbor_core_support k E hEL hER
      (p1CoreAt k (4 : Fin 6)) w hvw h
  have hi4 : i = 4 := ((p1CoreAt_injective k) hi).symm
  rw [hi4] at hel
  have hj2 : j = 2 := (p1Core_only_neighbor_four j).mp hel
  simpa only [hj2] using hj

theorem p1JointCoreTwo_old_neighbor_only_four_five (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hEL : Preserves (p1SideHyper k true) E
      (leftJointInclusion (4*k+6)))
    (hER : Preserves (p1SideHyper k false) E
      (rightJointInclusion (4*k+6)))
    (w : Fin (4*k+6))
    (h : p1JointOld k w ∈ p1JointHomogeneousNeighbors k E
      (p1JointOld k (p1CoreAt k (2 : Fin 6)))) :
    w = p1CoreAt k (4 : Fin 6) ∨ w = p1CoreAt k (5 : Fin 6) := by
  have hvw : p1CoreAt k (2 : Fin 6) ≠ w := by
    intro he
    have hh := p1JointHomogeneousNeighbors_ne_self k E
      (p1JointOld k (p1CoreAt k (2 : Fin 6)))
      (p1JointOld k w) h
    exact hh (congrArg (p1JointOld k) he.symm)
  obtain ⟨i,j,hi,hj,hel⟩ :=
    p1JointOldNeighbor_core_support k E hEL hER
      (p1CoreAt k (2 : Fin 6)) w hvw h
  have hi2 : i = 2 := ((p1CoreAt_injective k) hi).symm
  rw [hi2] at hel
  rcases (p1Core_only_neighbors_two j).mp hel with h4 | h5
  · left
    simpa only [h4] using hj
  · right
    simpa only [h5] using hj

/-- All old-vertex support restrictions follow from the verified
mixed packet eligibility theorem. Assuming only the three
new-vertex exclusions and the protected a4 fixed edge, the
actual zero-or-two degree law forces the two key old edges. -/
theorem p1JointCore_forced_of_nonmixed_exclusions (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hE : Admissible (toggleZero (switchingAllowed (4*k+5))) E)
    (hEL : Preserves (p1SideHyper k true) E
      (leftJointInclusion (4*k+6)))
    (hER : Preserves (p1SideHyper k false) E
      (rightJointInclusion (4*k+6)))
    (hfixed4 :
      p1JointLeftNew k ∈ p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (4 : Fin 6))))
    (hNoRight4 :
      p1JointRightNew k ∉ p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (4 : Fin 6))))
    (hNoLeft2 :
      p1JointLeftNew k ∉ p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (2 : Fin 6))))
    (hNoRight2 :
      p1JointRightNew k ∉ p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (2 : Fin 6)))) :
    p1JointOld k (p1CoreAt k (2 : Fin 6)) ∈
      p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (4 : Fin 6))) ∧
    p1JointOld k (p1CoreAt k (5 : Fin 6)) ∈
      p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (2 : Fin 6))) := by
  have hsupport4 (y : Fin (4*k+6+2))
      (hy : y ∈ p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (4 : Fin 6)))) :
      y = p1JointLeftNew k ∨
      y = p1JointOld k (p1CoreAt k (2 : Fin 6)) := by
    rcases p1JointVertex_old_or_new k y with ⟨w,hw⟩ | hleft | hright
    · right
      rw [hw] at hy
      have hh := p1JointCoreFour_old_neighbor_only_two k E
        hEL hER w hy
      rw [hw, hh]
    · exact Or.inl hleft
    · rw [hright] at hy
      exact (hNoRight4 hy).elim
  have hsupport2 (y : Fin (4*k+6+2))
      (hy : y ∈ p1JointHomogeneousNeighbors k E
        (p1JointOld k (p1CoreAt k (2 : Fin 6)))) :
      y = p1JointOld k (p1CoreAt k (4 : Fin 6)) ∨
      y = p1JointOld k (p1CoreAt k (5 : Fin 6)) := by
    rcases p1JointVertex_old_or_new k y with ⟨w,hw⟩ | hleft | hright
    · rw [hw] at hy
      rcases p1JointCoreTwo_old_neighbor_only_four_five k E
        hEL hER w hy with h4 | h5
      · left
        rw [hw,h4]
      · right
        rw [hw,h5]
    · rw [hleft] at hy
      exact (hNoLeft2 hy).elim
    · rw [hright] at hy
      exact (hNoRight2 hy).elim
  exact p1JointCore_forced_neighbors_of_support k E hE
    hfixed4 hsupport4 hsupport2

end Hypertournaments
