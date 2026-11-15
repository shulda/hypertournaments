import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Convert
import Hypertournaments.RootedOddSuspensionSigns
import Hypertournaments.EvenSuspensionFacetCases
import Hypertournaments.CanonicalPacket
import Hypertournaments.EvenAlternatingBalance
import Hypertournaments.UniformPacketPermutationCount

/-!
# Central local types far from the two/three/four-pad cases

For an odd source arity n=2k+1, its rooted two-pad suspension has
high arity n+2=2k+3. Every (n+3)-packet with at most one pad or at
least five pads has **all positive raw facet orientations**, and
thus its normalized packet of even length 2k+4 is balanced.
The local type is the central index k+2.

All results use the *actual* finite-set sign table and intrinsic
hypertournament orientations. No conditional admissibility
assumption is introduced.
-/

namespace Hypertournaments

/-- With at most one or at least five pads, erasing a vertex cannot
leave exactly two or three pads in the corresponding facet. -/
theorem rootedOdd_far_erase_ne_two_three (m a : ℕ)
    (Q : Finset (Fin (m+a)))
    (hfar : (evenPadProjection m a Q).card ≤ 1 ∨
      5 ≤ (evenPadProjection m a Q).card)
    (v : Fin (m+a)) :
    (evenPadProjection m a (Q.erase v)).card ≠ 2 ∧
    (evenPadProjection m a (Q.erase v)).card ≠ 3 := by
  have hh := evenPadProjection_erase_card m a Q v
  rcases hfar with hlo | hhi
  · rcases hh with h | h <;> omega
  · rcases hh with h | h <;> omega

/-- All raw facet signs are positive for the far pad-count cases
of the actual rooted odd suspension finite-set sign table. -/
theorem rootedOddSuspensionSignTable_facet_far
    {n : ℕ} (m a : ℕ) (A : Hyper n (Fin a))
    (root : Fin a)
    (Q : Finset (Fin (m+a)))
    (hfar : (evenPadProjection m a Q).card ≤ 1 ∨
      5 ≤ (evenPadProjection m a Q).card)
    (v : Fin (m+a)) :
    rootedOddSuspensionSignTable m a A root (Q.erase v) = true := by
  obtain ⟨h2, h3⟩ :=
    rootedOdd_far_erase_ne_two_three m a Q hfar v
  simp [rootedOddSuspensionSignTable, h2, h3]

/-- The actual orientation of each facet of an increasing packet
with 0,1 or >=5 pads is positive, in every source arity. -/
theorem Hyper.rootedOddSuspension_orient_increasingFacet_far
    {n m a : ℕ} (A : Hyper n (Fin a))
    (root : Fin a) (f : Fin (n+3) ↪o Fin (m+a))
    (hfar :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card ≤ 1 ∨
      5 ≤ (evenPadProjection m a (tupleVertices f.toEmbedding)).card)
    (i : Fin (n+3)) :
    (A.rootedOddSuspension m a root).orient (facet f.toEmbedding i) =
      true := by
  calc
    (A.rootedOddSuspension m a root).orient (facet f.toEmbedding i) =
      rootedOddSuspensionSignTable m a A root
        (tupleVertices (facet f.toEmbedding i)) :=
      fromOrderedSigns_facet_increasing
        (rootedOddSuspensionSignTable m a A root) f i
    _ = rootedOddSuspensionSignTable m a A root
        ((tupleVertices f.toEmbedding).erase (f i)) := by
      simpa using congrArg (rootedOddSuspensionSignTable m a A root)
        (tupleVertices_facet_eq_erase f.toEmbedding i)
    _ = true :=
      rootedOddSuspensionSignTable_facet_far m a A root
        (tupleVertices f.toEmbedding) hfar (f i)

/-- An all-positive raw packet of even length 2k+4 has exactly
k+2 positive normalized facets. -/
theorem boolPacketPositiveCount_all_positive_even_odd_source
    (k : ℕ) :
    boolPacketPositiveCount
      (fun i : Fin (2*k+4) => !(decide (i.val%2=1))) = k+2 := by
  have hcount :
      boolPacketPositiveCount
        (fun i : Fin (2*k+4) => decide (i.val%2=1)) = k+2 := by
    convert boolPacketPositiveCount_alternating_even (k+2) using 1 <;> omega
  rw [boolPacketPositiveCount_not, hcount]
  omega

/-- True intrinsic centrality for every increasing rooted
odd-suspension packet with 0,1 or at least five pads. -/
theorem Hyper.rootedOddSuspension_localIndex_increasing_far
    (k m a : ℕ) (A : Hyper (2*k+1) (Fin a))
    (root : Fin a)
    (f : Fin (2*k+4) ↪o Fin (m+a))
    (hfar :
      (evenPadProjection m a (tupleVertices f.toEmbedding)).card ≤ 1 ∨
      5 ≤ (evenPadProjection m a (tupleVertices f.toEmbedding)).card) :
    localIndex (A.rootedOddSuspension m a root) f.toEmbedding = k+2 := by
  let D : Hyper (2*k+3) (Fin (m+a)) :=
    A.rootedOddSuspension m a root
  have hpacket :
      (fun i : Fin (2*k+4) => normalizedFacet D f.toEmbedding i) =
        (fun i : Fin (2*k+4) => !(decide (i.val%2=1))) := by
    funext i
    have hraw :
        D.orient (facet f.toEmbedding i) = true :=
      A.rootedOddSuspension_orient_increasingFacet_far root f hfar i
    unfold normalizedFacet
    rw [hraw]
    cases hbit : decide (i.val%2=1) <;> decide
  have hcount :
      positiveFacetCount D f.toEmbedding = k+2 := by
    change boolPacketPositiveCount
      (fun i : Fin (2*k+4) => normalizedFacet D f.toEmbedding i) = k+2
    rw [hpacket]
    exact boolPacketPositiveCount_all_positive_even_odd_source k
  change min (positiveFacetCount D f.toEmbedding)
      ((2*k+3+1)-positiveFacetCount D f.toEmbedding) = k+2
  rw [hcount]
  omega

end Hypertournaments
