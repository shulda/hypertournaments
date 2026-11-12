import Hypertournaments.OddToggleP1ActualCoboundary
import Hypertournaments.OddToggleP1RawCountParity
import Hypertournaments.EvenAlternatingBalance

/-!
# Actual odd p3 switching parity equals zero raw coboundary

In arity n=4k+3 the normalized packet has length 4k+4 and
contains 2k+2 alternating parity positions, an EVEN number. Hence
normalizing does not change raw orientation parity. The local
minority index has the same parity as the positive normalized
count, since the packet length is even.

As centralIndex n=2k+2 is also even, an actual packet lies in
switchingAllowed n if and only if its raw facet sum is zero in
ZMod 2. For an intrinsic hypertournament on Fin a and an
increasing packet, this is precisely the vanishing of the
unsigned coboundary of its genuine canonical sign table.

This provides the actual-geometry cochain bridge needed for
the n congruent to 3 mod 4 exceptional non-AP construction.
It does not yet assert existence of the probabilistic witness.
-/

namespace Hypertournaments

/-- In characteristic two, a natural number vanishes exactly when
it is even. -/
theorem p3NatCast_zero_iff_even (r : ℕ) :
    ((r : ℕ) : ZMod 2) = 0 ↔ r % 2 = 0 := by
  rw [p1NatCast_mod_two]
  have hc : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hc with h | h
  · simp [h]
  · simp [h]

/-- The raw and normalized counts have the same F₂ parity
in every actual arity 4k+3 hypertournament packet. -/
theorem Hyper.p3RawFacetCount_toZMod
    (k : ℕ) {V : Type*} (A : Hyper (4*k+3) V)
    (f : Fin (4*k+4) ↪ V) :
    ((boolPacketPositiveCount
      (fun i : Fin (4*k+4) => A.orient (facet f i)) : ℕ) : ZMod 2) =
    ((positiveFacetCount A f : ℕ) : ZMod 2) := by
  let raw : Fin (4*k+4) → Bool := fun i => A.orient (facet f i)
  let alt : Fin (4*k+4) → Bool := fun i => decide (i.val % 2 = 1)
  have hlen : 4*k+4 = 2*(2*k+2) := by omega
  have hcount : boolPacketPositiveCount alt = 2*k+2 := by
    dsimp [alt]
    rw [hlen]
    exact boolPacketPositiveCount_alternating_even (2*k+2)
  have hbits :
      (fun i : Fin (4*k+4) => raw i ^^ alt i) =
      (fun i : Fin (4*k+4) => normalizedFacet A f i) := rfl
  have hhalf : (((2*k+2 : ℕ) : ZMod 2)) = 0 := by
    have htwo : (2 : ZMod 2) = 0 := by decide
    calc
      (((2*k+2 : ℕ) : ZMod 2)) =
          (2 : ZMod 2) * (k : ZMod 2) + 2 := by push_cast; ring
      _ = 0 := by rw [htwo]; simp
  have hxor := p1BoolPacketXor_toZMod raw alt
  rw [hbits, hcount, hhalf] at hxor
  change ((boolPacketPositiveCount raw : ℕ) : ZMod 2) =
    ((positiveFacetCount A f : ℕ) : ZMod 2)
  simpa only [add_zero, boolPacketPositiveCount, positiveFacetCount] using hxor.symm

/-- Since an arity 4k+3 packet has even length, its minority
type index has the same parity as its normalized positive count. -/
theorem Hyper.p3LocalIndex_mod_two
    (k : ℕ) {V : Type*} (A : Hyper (4*k+3) V)
    (f : Fin (4*k+4) ↪ V) :
    localIndex A f % 2 = positiveFacetCount A f % 2 := by
  have hcount := positiveFacetCount_le A f
  change (min (positiveFacetCount A f)
      (4*k+3+1-positiveFacetCount A f)) % 2 =
    positiveFacetCount A f % 2
  have hlen : 4*k+3+1 = 4*k+4 := by omega
  rw [hlen]
  by_cases hle : positiveFacetCount A f ≤
      4*k+4-positiveFacetCount A f
  · rw [Nat.min_eq_left hle]
  · rw [Nat.min_eq_right (le_of_lt (lt_of_not_ge hle))]
    omega

/-- Genuine local switching membership in arities 3 mod 4 is
exactly even raw facet parity, without an admissibility assumption. -/
theorem Hyper.p3SwitchingAllowed_iff_rawFacetParityEven
    (k : ℕ) {V : Type*} (A : Hyper (4*k+3) V)
    (f : Fin (4*k+4) ↪ V) :
    localIndex A f ∈ switchingAllowed (4*k+3) ↔
      ((boolPacketPositiveCount
        (fun i : Fin (4*k+4) => A.orient (facet f i)) : ℕ) :
          ZMod 2) = 0 := by
  have hcentral : centralIndex (4*k+3) = 2*k+2 := by
    unfold centralIndex
    omega
  have hindex := A.p3LocalIndex_mod_two k f
  have hraw := A.p3RawFacetCount_toZMod k f
  constructor
  · intro hallowed
    change localIndex A f ≤ centralIndex (4*k+3) ∧
      localIndex A f % 2 = centralIndex (4*k+3) % 2 at hallowed
    have hnorm : positiveFacetCount A f % 2 = 0 := by
      rw [hcentral] at hallowed
      omega
    have hz : ((positiveFacetCount A f : ℕ) : ZMod 2) = 0 :=
      (p3NatCast_zero_iff_even _).mpr hnorm
    exact hraw.trans hz
  · intro hz
    have hnorm : positiveFacetCount A f % 2 = 0 :=
      (p3NatCast_zero_iff_even _).mp (hraw.symm.trans hz)
    change localIndex A f ≤ centralIndex (4*k+3) ∧
      localIndex A f % 2 = centralIndex (4*k+3) % 2
    constructor
    · exact localIndex_le_central A f
    · rw [hcentral]
      omega

/-- The true intrinsic switching test on a canonical increasing
packet is the vanishing of the unsigned coboundary of the source
hypertournament's canonical unordered orientation table. -/
theorem Hyper.p3SwitchingAllowed_iff_coboundary_zero
    (k a : ℕ) (A : Hyper (4*k+3) (Fin a))
    (f : Fin (4*k+4) ↪o Fin a) :
    localIndex A f.toEmbedding ∈ switchingAllowed (4*k+3) ↔
      coboundary
        (fun Q => p1BitToZMod (A.canonicalSignTable Q))
        (tupleVertices f.toEmbedding) = 0 := by
  simpa only [← A.p1CanonicalRawFacetSum f] using
    (A.p3SwitchingAllowed_iff_rawFacetParityEven k f.toEmbedding)

end Hypertournaments
