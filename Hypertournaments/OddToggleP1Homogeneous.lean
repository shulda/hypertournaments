import Hypertournaments.TwoPadPacketCount
import Hypertournaments.LocalTypes

/-!
# Exact homogeneous local type as a constant normalized facet packet

A local-index-zero (n+1)-packet has either no positive normalized
facets or all positive normalized facets. Thus the normalized
facet signs are constant (false or true), equivalently the raw
signs alternate with the deletion index parity.

This module uses the actual intrinsic `localIndex` and
`normalizedFacet`, not an arbitrary auxiliary Boolean predicate.
It is a prerequisite for transporting the abstract phase
obstruction to actual homogeneous local packets.
-/

namespace Hypertournaments

/-- The minority count of a nonempty Boolean packet is zero exactly
when all of its bits are equal. -/
theorem p1BoolMinority_zero_iff_constant
    {m : ℕ} (bits : Fin (m+1) → Bool) :
    min (boolPacketPositiveCount bits)
      ((m+1)-boolPacketPositiveCount bits) = 0 ↔
    ∃ b : Bool, ∀ i : Fin (m+1), bits i = b := by
  classical
  have hcard : boolPacketPositiveCount bits ≤ m+1 :=
    boolPacketPositiveCount_le bits
  constructor
  · intro hz
    have hcases : boolPacketPositiveCount bits = 0 ∨
        boolPacketPositiveCount bits = m+1 := by omega
    rcases hcases with hzero | hfull
    · have hempty :
          (Finset.univ.filter (fun i : Fin (m+1) => bits i = true)) =
            ∅ := Finset.card_eq_zero.mp hzero
      refine ⟨false, ?_⟩
      intro i
      have hnot : bits i ≠ true := by
        intro ht
        have hmem : i ∈
            (Finset.univ.filter (fun j : Fin (m+1) => bits j = true)) := by
          simp [ht]
        rw [hempty] at hmem
        simpa using hmem
      cases hb : bits i <;> simp_all
    · have hset :
          (Finset.univ.filter (fun i : Fin (m+1) => bits i = true)) =
            Finset.univ := by
        apply Finset.eq_of_subset_of_card_le
          (Finset.filter_subset _ _)
        simpa [boolPacketPositiveCount, hfull]
      refine ⟨true, ?_⟩
      intro i
      have hmem : i ∈
          (Finset.univ.filter (fun j : Fin (m+1) => bits j = true)) := by
        rw [hset]
        exact Finset.mem_univ _
      simpa using hmem
  · rintro ⟨b, hb⟩
    cases b
    · have hempty :
          (Finset.univ.filter (fun i : Fin (m+1) => bits i = true)) =
            ∅ := by
        ext i
        simp [hb i]
      have hzero : boolPacketPositiveCount bits = 0 := by
        unfold boolPacketPositiveCount
        rw [hempty]
        simp
      simp [hzero]
    · have hfull :
          (Finset.univ.filter (fun i : Fin (m+1) => bits i = true)) =
            Finset.univ := by
        ext i
        simp [hb i]
      have hc : boolPacketPositiveCount bits = m+1 := by
        unfold boolPacketPositiveCount
        rw [hfull]
        simp
      simp [hc]

/-- Zero local index for an actual intrinsic hypertournament packet
is equivalent to the existence of one fixed normalized facet sign. -/
theorem localIndex_zero_iff_normalized_constant
    {n : ℕ} {V : Type*} (A : Hyper n V)
    (f : Fin (n+1) ↪ V) :
    localIndex A f = 0 ↔
      ∃ b : Bool, ∀ i : Fin (n+1), normalizedFacet A f i = b := by
  change min (boolPacketPositiveCount
      (fun i : Fin (n+1) => normalizedFacet A f i))
      ((n+1)-boolPacketPositiveCount
        (fun i : Fin (n+1) => normalizedFacet A f i)) = 0 ↔
    ∃ b : Bool, ∀ i : Fin (n+1), normalizedFacet A f i = b
  exact p1BoolMinority_zero_iff_constant
    (fun i : Fin (n+1) => normalizedFacet A f i)

end Hypertournaments
