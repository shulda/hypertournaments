import Hypertournaments.OddToggleP1ForcedFacetPositions
import Hypertournaments.OddToggleP1JointEndpointSigns
import Hypertournaments.OddToggleP1RawAlternating

/-!
# Exact actual forced-facet contradiction for the two p1 mixed core packets

In a hypothetical canonical joint preserving the explicit right
one-point side, the two mixed packets missing old core pairs
(a2,a4) and (a2,a5) cannot BOTH be homogeneous.

Their right-hand (left-new-deleted) n-facets have actual prescribed
opposite canonical link signs, fixing opposite homogeneous phases.
Their final old deletions have exactly the same increasing facet
index and leave exactly the same n-subset of the joint. That one
intrinsic canonical sign is therefore forced to be both true and
false. No abstract Boolean edge predicate or age assumption is
used in this conditional contradiction.
-/

namespace Hypertournaments

/-- The exact intrinsic core contradiction once the two actual
mixed packets have homogeneous local type zero. -/
theorem p1Joint_forced24_25_homogeneous_contradiction (k : ℕ)
    (E : Hyper (4*k+5) (Fin (4*k+6+2)))
    (hER : Preserves (p1SideHyper k false) E
      (rightJointInclusion (4*k+6)))
    (hzero24 : localIndex E
      ((p1JointMixedPacket k
         (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (4 : Fin 6))).orderEmbOfFin
        (p1JointMixedPacket_card k _ _
          (by
            intro hh
            have hv := congrArg Fin.val hh
            change 4*k+2 = 4*k+4 at hv
            omega))).toEmbedding = 0)
    (hzero25 : localIndex E
      ((p1JointMixedPacket k
         (p1CoreAt k (2 : Fin 6)) (p1CoreAt k (5 : Fin 6))).orderEmbOfFin
        (p1JointMixedPacket_card k _ _
          (by
            intro hh
            have hv := congrArg Fin.val hh
            change 4*k+2 = 4*k+5 at hv
            omega))).toEmbedding = 0) :
    False := by
  let v : Fin (4*k+6) := p1CoreAt k (2 : Fin 6)
  let w4 : Fin (4*k+6) := p1CoreAt k (4 : Fin 6)
  let w5 : Fin (4*k+6) := p1CoreAt k (5 : Fin 6)
  have hne24 : v ≠ w4 := by
    intro hh
    have hv := congrArg Fin.val hh
    change 4*k+2 = 4*k+4 at hv
    omega
  have hne25 : v ≠ w5 := by
    intro hh
    have hv := congrArg Fin.val hh
    change 4*k+2 = 4*k+5 at hv
    omega
  let Q24 : Finset (Fin (4*k+6+2)) := p1JointMixedPacket k v w4
  let Q25 : Finset (Fin (4*k+6+2)) := p1JointMixedPacket k v w5
  have hQ24 : Q24.card = 4*k+6 := p1JointMixedPacket_card k v w4 hne24
  have hQ25 : Q25.card = 4*k+6 := p1JointMixedPacket_card k v w5 hne25
  let g24 : Fin (4*k+6) ↪o Fin (4*k+6+2) := Q24.orderEmbOfFin hQ24
  let g25 : Fin (4*k+6) ↪o Fin (4*k+6+2) := Q25.orderEmbOfFin hQ25
  have hz24 : localIndex E g24.toEmbedding = 0 := by
    simpa [g24, Q24, v, w4] using hzero24
  have hz25 : localIndex E g25.toEmbedding = 0 := by
    simpa [g25, Q25, v, w5] using hzero25
  let j0 : Fin (4*k+6) := ⟨4*k+4, by omega⟩
  let j : Fin (4*k+6) := ⟨4*k+3, by omega⟩
  have hverts24 : tupleVertices g24.toEmbedding = Q24 := by
    simpa [g24, tupleVertices] using
      (Finset.image_orderEmbOfFin_univ Q24 hQ24)
  have hverts25 : tupleVertices g25.toEmbedding = Q25 := by
    simpa [g25, tupleVertices] using
      (Finset.image_orderEmbOfFin_univ Q25 hQ25)
  have hlast24 :
      g24 j0 = p1JointLeftNew k :=
    (p1JointMixedPacket_sorted_endpoints k v w4 hne24 hQ24).1
  have hlast25 :
      g25 j0 = p1JointLeftNew k :=
    (p1JointMixedPacket_sorted_endpoints k v w5 hne25 hQ25).1
  have hset24 :
      tupleVertices (facet g24.toEmbedding j0) =
        Q24.erase (p1JointLeftNew k) := by
    rw [tupleVertices_facet_eq_erase, hverts24]
    change Q24.erase (g24 j0) = Q24.erase (p1JointLeftNew k)
    rw [hlast24]
  have hset25 :
      tupleVertices (facet g25.toEmbedding j0) =
        Q25.erase (p1JointLeftNew k) := by
    rw [tupleVertices_facet_eq_erase, hverts25]
    change Q25.erase (g25 j0) = Q25.erase (p1JointLeftNew k)
    rw [hlast25]
  have hbit24 : p1CanonicalLink k false v w4 = true := by
    rw [p1CanonicalLink_core_right]
    decide
  have hbit25 : p1CanonicalLink k false v w5 = false := by
    rw [p1CanonicalLink_core_right]
    decide
  have hraw24 :
      E.canonicalSignTable (tupleVertices (facet g24.toEmbedding j0)) =
        true := by
    rw [hset24]
    exact (p1JointMixed_right_canonicalSign k v w4 hne24 E hER).trans hbit24
  have hraw25 :
      E.canonicalSignTable (tupleVertices (facet g25.toEmbedding j0)) =
        false := by
    rw [hset25]
    exact (p1JointMixed_right_canonicalSign k v w5 hne25 E hER).trans hbit25
  obtain ⟨b24, hb24⟩ :=
    E.localIndex_zero_canonical_sign_alternating g24 hz24
  obtain ⟨b25, hb25⟩ :=
    E.localIndex_zero_canonical_sign_alternating g25 hz25
  have hj0 : ¬(j0.val % 2 = 1) := by
    dsimp [j0]
    omega
  have hj : j.val % 2 = 1 := by
    dsimp [j]
    omega
  have hphase24 : b24 = true := by
    have he := hb24 j0
    have hbit : decide (j0.val % 2 = 1) = false := by simp [hj0]
    rw [hbit] at he
    simpa only [Bool.xor_false] using (he.symm.trans hraw24)
  have hphase25 : b25 = false := by
    have he := hb25 j0
    have hbit : decide (j0.val % 2 = 1) = false := by simp [hj0]
    rw [hbit] at he
    simpa only [Bool.xor_false] using (he.symm.trans hraw25)
  have hlastOld24 :
      g24 j = p1JointOld k w5 :=
    p1JointMixed24_thirdLast_a5 k hQ24
  have hlastOld25 :
      g25 j = p1JointOld k w4 :=
    p1JointMixed25_thirdLast_a4 k hQ25
  have hshared :
      tupleVertices (facet g24.toEmbedding j) =
        tupleVertices (facet g25.toEmbedding j) := by
    rw [tupleVertices_facet_eq_erase, tupleVertices_facet_eq_erase,
      hverts24, hverts25]
    change Q24.erase (g24 j) = Q25.erase (g25 j)
    rw [hlastOld24, hlastOld25]
    ext t
    simp only [Q24, Q25, p1JointMixedPacket, Finset.mem_erase,
      Finset.mem_univ, true_and]
    tauto
  have hsign24 :
      E.canonicalSignTable (tupleVertices (facet g24.toEmbedding j)) =
        false := by
    have hh := hb24 j
    have hbit : decide (j.val % 2 = 1) = true := by simp [hj]
    rw [hbit, hphase24] at hh
    simpa using hh
  have hsign25 :
      E.canonicalSignTable (tupleVertices (facet g25.toEmbedding j)) =
        true := by
    have hh := hb25 j
    have hbit : decide (j.val % 2 = 1) = true := by simp [hj]
    rw [hbit, hphase25] at hh
    simpa only [Bool.false_xor] using hh
  have hcontr : (false : Bool) = true := by
    calc
      false = E.canonicalSignTable
          (tupleVertices (facet g24.toEmbedding j)) := hsign24.symm
      _ = E.canonicalSignTable
          (tupleVertices (facet g25.toEmbedding j)) :=
        congrArg E.canonicalSignTable hshared
      _ = true := hsign25
  cases hcontr

end Hypertournaments
