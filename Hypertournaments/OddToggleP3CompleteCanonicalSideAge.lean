import Hypertournaments.OddToggleP3QAllActualAge
import Hypertournaments.OddToggleP3OccupancyTrichotomy
import Hypertournaments.OddToggleP3FreshOccupancyBridge
import Hypertournaments.OddToggleP3OrderedFreshAgeReduction
import Hypertournaments.OddToggleP3Halves
import Hypertournaments.OddToggleP3SparseSidePackets

/-!
# Complete canonical p3 one-point side age for both complementary halves

Fix m=4k+2 (k≥1) and positive block size t. Let a one-point side
have arbitrary W potential on full old transversals and arbitrary
L link potential supported on transversals missing an eligible block.

If the complement of eligible contains three consecutive protectedBlocks
blocks, EVERY actual fresh-containing increasing (m+2)-packet is
admissible, independently of W and L:
* q≤m−2 occupied old blocks: two missing blocks kill all raw facets;
* q=m−1: the certified true missing-singleton packet age theorem;
* q=m: two protectedBlocks singleton facets of opposite parity.

The true old base is already admissible for arbitrary W and the
local index is intrinsic under arbitrary packet permutations, so
this certifies the FULL un-ordered side age.

The final corollaries instantiate eligible to the lower/upper halves,
establishing both sides of the explicit random p3 one-point span.
No ordinary AP obstruction is asserted.
-/

namespace Hypertournaments

theorem p3CanonicalSide_admissible_of_protectedTriple
    (k t : ℕ) (hk : 1 ≤ k) (ht : 0 < t)
    (eligible protectedBlocks : Finset (Fin (4*k+2)))
    (hdisjoint : Disjoint eligible protectedBlocks)
    (start : ℕ) (hstart : start+2 < 4*k+2)
    (hprotected : ∀ b : Fin (4*k+2),
      start ≤ b.val → b.val ≤ start+2 → b ∈ protectedBlocks)
    (W L : Finset (Fin ((4*k+2)*t)) → ZMod 2) :
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3CanonicalSide (4*k+2) t eligible W L) := by
  apply p3CanonicalSide_admissible_of_ordered_fresh_packets
    k t hk ht eligible W L
  intro f hfresh
  obtain ⟨U,hU,_hEnum,hMem⟩ :=
    p3CanonicalFresh_old_enumeration_membership
      ((4*k+2)*t) ((4*k+2)+1) f hfresh
  have hPos (i : Fin (4*k+2))
      (hi : 0 < p3BlockOccupancy (4*k+2) t U i) :
      ∃ v : Fin ((4*k+2)*t),
        v.castSucc ∈ tupleVertices f.toEmbedding ∧
        p3BlockNumber t v = i.val :=
    p3CanonicalFresh_positive_occupancy_witness
      (4*k+2) t U f hMem i hi
  have hMiss (i : Fin (4*k+2))
      (hi : p3BlockOccupancy (4*k+2) t U i = 0) :
      ∀ v : Fin ((4*k+2)*t),
        v.castSucc ∈ tupleVertices f.toEmbedding →
        p3BlockNumber t v ≠ i.val :=
    p3CanonicalFresh_zero_occupancy_is_missing
      (4*k+2) t U f hMem i hi
  rcases p3ActualPacket_block_occupancy_trichotomy
      (4*k+2) t U with
    hall | ⟨missing,hzero,hrest⟩ | ⟨i,j,hij,hi,hj⟩
  · exact p3CanonicalSide_allowed_qAll_fresh_packet
      k (4*k+2) t hk rfl ht
      eligible protectedBlocks hdisjoint start hstart hprotected
      W L f hfresh
      (fun i => hPos i (hall i))
  · exact p3CanonicalSide_allowed_qMinusOne_fresh_packet
      k (4*k+2) t hk rfl ht
      eligible W L f hfresh missing
      (hMiss missing hzero)
      (fun i hine => hPos i (hrest i hine))
  · change localIndex
      (p3SideHyper (4*k+2) t
        (Fin.castSuccOrderEmb :
          Fin ((4*k+2)*t) ↪o Fin ((4*k+2)*t+1)).toEmbedding
        (Fin.last ((4*k+2)*t))
        eligible W L) f.toEmbedding ∈
        toggleZero (switchingAllowed (4*k+3))
    exact p3SidePacket_allowed_of_two_missing_blocks
      k t
      (Fin.castSuccOrderEmb :
        Fin ((4*k+2)*t) ↪o Fin ((4*k+2)*t+1)).toEmbedding
      (Fin.last ((4*k+2)*t))
      eligible W L f i j hij (hMiss i hi) (hMiss j hj)

/-- Side supported on lower-half missing blocks is admitted for
all potential coefficients, since the upper half is protectedBlocks. -/
theorem p3CanonicalSide_lowerHalf_admissible
    (k t : ℕ) (hk : 1 ≤ k) (ht : 0 < t)
    (W L : Finset (Fin ((4*k+2)*t)) → ZMod 2) :
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3CanonicalSide (4*k+2) t
        (p3EligibleLowerHalf (4*k+2)) W L) := by
  obtain ⟨hstart,hprotected⟩ := p3UpperProtectedTriple k hk
  exact p3CanonicalSide_admissible_of_protectedTriple
    k t hk ht
    (p3EligibleLowerHalf (4*k+2))
    (p3EligibleUpperHalf (4*k+2))
    (p3EligibleHalves_disjoint (4*k+2))
    ((4*k+2)/2) hstart hprotected W L

/-- Side supported on upper-half missing blocks is admitted for
all potential coefficients, since the lower half is protectedBlocks. -/
theorem p3CanonicalSide_upperHalf_admissible
    (k t : ℕ) (hk : 1 ≤ k) (ht : 0 < t)
    (W R : Finset (Fin ((4*k+2)*t)) → ZMod 2) :
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3CanonicalSide (4*k+2) t
        (p3EligibleUpperHalf (4*k+2)) W R) := by
  obtain ⟨hstart,hprotected⟩ := p3LowerProtectedTriple k hk
  exact p3CanonicalSide_admissible_of_protectedTriple
    k t hk ht
    (p3EligibleUpperHalf (4*k+2))
    (p3EligibleLowerHalf (4*k+2))
    (p3EligibleHalves_disjoint (4*k+2)).symm
    0 hstart hprotected W R

/-- Both actual one-point sides with complementary eligible
halves and common old W potential are simultaneously members
of the exceptional homogeneous-free p3 age. -/
theorem p3CanonicalComplementarySpan_admissible
    (k t : ℕ) (hk : 1 ≤ k) (ht : 0 < t)
    (W L R : Finset (Fin ((4*k+2)*t)) → ZMod 2) :
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3CanonicalSide (4*k+2) t
        (p3EligibleLowerHalf (4*k+2)) W L) ∧
    Admissible (toggleZero (switchingAllowed (4*k+3)))
      (p3CanonicalSide (4*k+2) t
        (p3EligibleUpperHalf (4*k+2)) W R) :=
  ⟨p3CanonicalSide_lowerHalf_admissible k t hk ht W L,
   p3CanonicalSide_upperHalf_admissible k t hk ht W R⟩

end Hypertournaments
