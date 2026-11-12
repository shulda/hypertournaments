import Hypertournaments.OddToggleP1BooleanParity
import Hypertournaments.EvenAlternatingBalance
import Hypertournaments.SwitchingShift

/-!
# Exact p3 type of a packet with all raw orientation bits zero

For n=4k+3, an (n+1)-packet with every raw facet sign false
has normalized facet word exactly the alternating parity word.
Its positive count is 2k+2, exactly half the packet length, so its
intrinsic local index is the central type 2k+2 (nonzero, even).

Thus every all-zero raw packet AUTOMATICALLY belongs to the
exceptional homogeneous-free toggleZero switching family. This
strengthens the previously certified low-occupancy parity argument
and gives a reusable one-line age certificate after a support-zero
proof, without separately finding protected facets.
-/

namespace Hypertournaments

/-- A true intrinsic p3 packet with all raw facets zero has exactly
the central local type, in every arity n=4k+3. -/
theorem Hyper.p3LocalIndex_central_of_all_raw_zero
    (k : ℕ) {V : Type*} (A : Hyper (4*k+3) V)
    (f : Fin (4*k+4) ↪ V)
    (hraw : ∀ i : Fin (4*k+4),
      A.orient (facet f i) = false) :
    localIndex A f = 2*k+2 := by
  have hnormalized :
      (fun i : Fin (4*k+4) => normalizedFacet A f i) =
      (fun i : Fin (4*k+4) => decide (i.val%2=1)) := by
    funext i
    simp [normalizedFacet, hraw i]
  have hpositive : positiveFacetCount A f = 2*k+2 := by
    change boolPacketPositiveCount
      (fun i : Fin (4*k+4) => normalizedFacet A f i) = 2*k+2
    rw [hnormalized]
    have hlen : 4*k+4 = 2*(2*k+2) := by omega
    rw [hlen]
    exact boolPacketPositiveCount_alternating_even (2*k+2)
  unfold localIndex
  rw [hpositive]
  have hhalf : 4*k+3+1 - (2*k+2) = 2*k+2 := by omega
  rw [hhalf]
  exact min_self _

/-- All-zero actual raw p3 packets are admitted by the exceptional
switching family with homogeneous index zero deleted. -/
theorem Hyper.p3ToggleAllowed_of_all_raw_zero
    (k : ℕ) {V : Type*} (A : Hyper (4*k+3) V)
    (f : Fin (4*k+4) ↪ V)
    (hraw : ∀ i : Fin (4*k+4),
      A.orient (facet f i) = false) :
    localIndex A f ∈ toggleZero (switchingAllowed (4*k+3)) := by
  have htype := A.p3LocalIndex_central_of_all_raw_zero k f hraw
  have hne : localIndex A f ≠ 0 := by rw [htype]; omega
  change (if localIndex A f = 0
    then localIndex A f ∉ switchingAllowed (4*k+3)
    else localIndex A f ∈ switchingAllowed (4*k+3))
  rw [if_neg hne, htype]
  have hcentral : centralIndex (4*k+3) = 2*k+2 := by
    unfold centralIndex
    omega
  rw [← hcentral]
  exact central_mem_switchingAllowed (4*k+3)

end Hypertournaments
