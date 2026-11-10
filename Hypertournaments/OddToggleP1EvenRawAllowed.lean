import Hypertournaments.OddToggleP1RawCountParity
import Hypertournaments.OddToggleP1IndexParity

/-!
# Even raw facet parity is sufficient for p1 local admissibility

The exceptional arity 4k+5 allowed type family contains the
homogeneous type zero and all positive odd minority indices.
The normalized alternating parity word has odd positive count
(2k+3) on its 4k+6 facets.

Consequently any actual packet with an even *raw* positive-facet
count has odd normalized minority index, so it belongs to the
switching family and hence to toggleZero(switchingAllowed).

This direction has no admissibility premise; it is the basic local
certificate for the base and for most side packets in the explicit
one-point nonamalgamation diagram.
-/

namespace Hypertournaments

/-- On an even packet of length 4k+6, if r+2k+3 is even,
then the minority of r and 4k+6-r is necessarily odd. -/
theorem p1OddMinority_of_evenShiftedCount
    (k r : ℕ) (hr : r ≤ 4*k+6)
    (hpar : (r+2*k+3)%2=0) :
    (min r (4*k+6-r))%2=1 := by
  by_cases hle : r ≤ 4*k+6-r
  · rw [Nat.min_eq_left hle]
    omega
  · rw [Nat.min_eq_right (le_of_lt (lt_of_not_ge hle))]
    omega

/-- Any genuine packet in arity 4k+5 whose unnormalized facet
word has even positive count belongs to the p1 allowed type family,
without assuming any other packets are admissible. -/
theorem Hyper.p1Toggle_allowed_of_even_rawFacetCount
    (k : ℕ) {V : Type*} (A : Hyper (4*k+5) V)
    (f : Fin (4*k+6) ↪ V)
    (heven :
      (boolPacketPositiveCount
        (fun i : Fin (4*k+6) => A.orient (facet f i)) % 2) = 0) :
    localIndex A f ∈
      toggleZero (switchingAllowed (4*k+5)) := by
  let rc : ℕ :=
    boolPacketPositiveCount
      (fun i : Fin (4*k+6) => A.orient (facet f i))
  have hrawzero : ((rc : ℕ) : ZMod 2) = 0 := by
    rw [p1NatCast_eq_oddBit]
    have hrc : rc % 2 = 0 := heven
    simp [hrc, p1BitToZMod]
  have hnormzero :
      (((positiveFacetCount A f + (2*k+3) : ℕ) : ZMod 2)) = 0 := by
    rw [← A.p1RawFacetCount_toZMod k f]
    exact hrawzero
  have hnormeven :
      (positiveFacetCount A f + (2*k+3)) % 2 = 0 := by
    by_contra hn
    have ho : (positiveFacetCount A f + (2*k+3))%2 = 1 := by omega
    have hone :
        (((positiveFacetCount A f + (2*k+3) : ℕ) : ZMod 2)) = 1 := by
      rw [p1NatCast_eq_oddBit]
      simp [ho, p1BitToZMod]
    exact (by decide : (1 : ZMod 2) ≠ 0) (hone.symm.trans hnormzero)
  have hcount : positiveFacetCount A f ≤ 4*k+6 :=
    positiveFacetCount_le A f
  have hindexodd :
      (localIndex A f) % 2 = 1 := by
    change (min (positiveFacetCount A f)
      (4*k+5+1-positiveFacetCount A f))%2 = 1
    have hnat : 4*k+5+1=4*k+6 := by omega
    rw [hnat]
    exact p1OddMinority_of_evenShiftedCount
      k (positiveFacetCount A f) hcount hnormeven
  have hnonzero : localIndex A f ≠ 0 := by
    intro hz
    omega
  change (if localIndex A f = 0
    then localIndex A f ∉ switchingAllowed (4*k+5)
    else localIndex A f ∈ switchingAllowed (4*k+5))
  rw [if_neg hnonzero]
  change (localIndex A f ≤ centralIndex (4*k+5)) ∧
    ((localIndex A f)%2 = (centralIndex (4*k+5))%2)
  constructor
  · exact localIndex_le_central A f
  · unfold centralIndex
    omega

end Hypertournaments
