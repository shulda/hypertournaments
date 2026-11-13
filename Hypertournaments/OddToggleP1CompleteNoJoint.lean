import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP1ActualNonmixedJointEdges
import Hypertournaments.OddToggleP1ActualCoreNeighborSupport
import Hypertournaments.OddToggleP1ActualForcedFacetContradiction
import Hypertournaments.OddToggleP1NoJointInterface

/-!
# Complete ordinary non-amalgamation obstruction for n ≡ 1 (mod 4)

The actual explicit p1 common base and both one-point sides are
already certified admissible. Assume a canonical two-distinct-new-
vertex joint preserves both sides. The right protected a4 packet
gives one fixed homogeneous neighbor; the left side and the
unprotected right a2 packet exclude the other three new edges.
The seven-core eligible support and intrinsic zero-or-two degree
law force the old edges a4--a2 and a2--a5. Their actual mixed
packets would both be homogeneous, contradicting the explicitly
certified common n-facet orientation.

The existing no-joint-to-ordinary-AP lemma handles the possibility
of identifying the two newly added points. No strong AP assumption,
synthetic Boolean graph, or external solver is used.
-/

namespace Hypertournaments

theorem p1NoCanonicalJoint (k : ℕ) : P1NoCanonicalJoint k := by
  intro E hE hEL hER
  obtain ⟨hfixed4, hNoRight4, hNoLeft2, hNoRight2⟩ :=
    p1JointCore_fixed_and_excluded_new_edges k E hEL hER
  obtain ⟨h42,h25⟩ :=
    p1JointCore_forced_of_nonmixed_exclusions
      k E hE hEL hER hfixed4 hNoRight4 hNoLeft2 hNoRight2
  have hne24 :
      p1CoreAt k (2 : Fin 6) ≠ p1CoreAt k (4 : Fin 6) := by
    intro he
    have hh := (p1CoreAt_injective k) he
    exact (by decide : (2 : Fin 6) ≠ 4) hh
  have hne25 :
      p1CoreAt k (2 : Fin 6) ≠ p1CoreAt k (5 : Fin 6) := by
    intro he
    have hh := (p1CoreAt_injective k) he
    exact (by decide : (2 : Fin 6) ≠ 5) hh
  have hlt24 :
      p1JointOld k (p1CoreAt k (2 : Fin 6)) <
        p1JointOld k (p1CoreAt k (4 : Fin 6)) := by
    change 4*k+2 < 4*k+4
    omega
  have hlt25 :
      p1JointOld k (p1CoreAt k (2 : Fin 6)) <
        p1JointOld k (p1CoreAt k (5 : Fin 6)) := by
    change 4*k+2 < 4*k+5
    omega
  have h24 :
      p1JointOld k (p1CoreAt k (4 : Fin 6)) ∈
        p1JointHomogeneousNeighbors k E
          (p1JointOld k (p1CoreAt k (2 : Fin 6))) :=
    p1JointHomogeneousNeighbors_symmetric k E
      (p1JointOld k (p1CoreAt k (4 : Fin 6)))
      (p1JointOld k (p1CoreAt k (2 : Fin 6))) h42
  have hz24 :
      localIndex E
        ((p1JointMixedPacket k
          (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (4 : Fin 6))).orderEmbOfFin
          (p1JointMixedPacket_card k _ _ hne24)).toEmbedding = 0 := by
    have he := (p1JointNeighbor_mem_iff_canonical_zero k E
      (p1JointOld k (p1CoreAt k (2 : Fin 6)))
      (p1JointOld k (p1CoreAt k (4 : Fin 6)))
      (ne_of_lt hlt24)).mp h24
    simpa only [p1JointDoubleDeletion, p1JointMixedPacket] using he
  have hz25 :
      localIndex E
        ((p1JointMixedPacket k
          (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (5 : Fin 6))).orderEmbOfFin
          (p1JointMixedPacket_card k _ _ hne25)).toEmbedding = 0 := by
    have he := (p1JointNeighbor_mem_iff_canonical_zero k E
      (p1JointOld k (p1CoreAt k (2 : Fin 6)))
      (p1JointOld k (p1CoreAt k (5 : Fin 6)))
      (ne_of_lt hlt25)).mp h25
    simpa only [p1JointDoubleDeletion, p1JointMixedPacket] using he
  exact p1Joint_forced24_25_homogeneous_contradiction k E hER
    hz24 hz25

/-- Unconditional bad ordinary one-point witness for the entire
n ≡ 1 mod 4 exceptional toggle-zero parity class, including n=5. -/
theorem p1BadOnePoint_all (k : ℕ) :
    HasBadOnePoint (4*k+5)
      (toggleZero (switchingAllowed (4*k+5))) :=
  p1HasBadOnePoint_of_no_canonical_joint k (p1NoCanonicalJoint k)

/-- In every arity n=4k+5 the exceptional toggle-zero switching
class fails ordinary amalgamation, not just strong amalgamation. -/
theorem p1NotHasAP_all (k : ℕ) :
    ¬ HasAP (4*k+5)
      (toggleZero (switchingAllowed (4*k+5))) :=
  p1NotHasAP_of_no_canonical_joint k (p1NoCanonicalJoint k)

end Hypertournaments
