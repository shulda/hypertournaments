import Hypertournaments.OddToggleP1IndexParity
import Hypertournaments.OddToggleP1BooleanParity
import Hypertournaments.EvenAlternatingBalance

/-!
# The actual raw facet parity detects the zero local type

For source arity n=4k+5, the normalized packet has 4k+6 facets,
and its parity differs from the parity of the raw facet word by
2k+3, which is odd. In the exceptional toggle-zero switching family,
only type zero and odd minority types are permitted.

Consequently type zero is equivalent to *odd* raw facet parity in
ZMod 2, on every actual intrinsic hypertournament packet.

This proves the Boolean and finite-field arithmetic bridge. The
next geometric step transports raw counts on an increasing
(n+1)-tuple to coboundary of the canonical unordered sign table.
-/

namespace Hypertournaments

/-- Reduction of a natural-number cast into ZMod 2 to its remainder. -/
theorem p1NatCast_mod_two (r : ℕ) :
    (r : ZMod 2) = ((r % 2 : ℕ) : ZMod 2) := by
  have hrepr : r = r % 2 + 2 * (r / 2) := by omega
  calc
    (r : ZMod 2) = ((r % 2 + 2 * (r / 2) : ℕ) : ZMod 2) :=
      congrArg (fun x : ℕ => (x : ZMod 2)) hrepr
    _ = ((r % 2 : ℕ) : ZMod 2) := by
      have hz : (2 : ZMod 2) = 0 := by decide
      push_cast
      simp [hz]

/-- A Boolean test of oddness equals its F₂ integer cast. -/
theorem p1NatCast_eq_oddBit (r : ℕ) :
    (r : ZMod 2) = p1BitToZMod (decide (r % 2 = 1)) := by
  rw [p1NatCast_mod_two]
  have hcases : r % 2 = 0 ∨ r % 2 = 1 := by omega
  rcases hcases with hz | ho
  · simp [hz, p1BitToZMod]
  · simp [ho, p1BitToZMod]

/-- On every genuine n=4k+5 packet the total raw positive-facet
count has the same F₂ parity as normalized positive count plus
the odd alternating half-length 2k+3. -/
theorem Hyper.p1RawFacetCount_toZMod
    (k : ℕ) {V : Type*} (A : Hyper (4*k+5) V)
    (f : Fin (4*k+6) ↪ V) :
    ((boolPacketPositiveCount
      (fun i : Fin (4*k+6) => A.orient (facet f i)) : ℕ) : ZMod 2) =
    ((positiveFacetCount A f + (2*k+3) : ℕ) : ZMod 2) := by
  let raw : Fin (4*k+6) → Bool := fun i => A.orient (facet f i)
  let alt : Fin (4*k+6) → Bool := fun i => decide (i.val%2=1)
  have hlen : 4*k+6 = 2*(2*k+3) := by omega
  have hcount : boolPacketPositiveCount alt = 2*k+3 := by
    dsimp [alt]
    rw [hlen]
    exact boolPacketPositiveCount_alternating_even (2*k+3)
  have hbits :
      (fun i : Fin (4*k+6) => raw i ^^ alt i) =
        (fun i : Fin (4*k+6) => normalizedFacet A f i) := rfl
  have hxor := p1BoolPacketXor_toZMod raw alt
  rw [hbits, hcount] at hxor
  have hnorm :
      ((positiveFacetCount A f : ℕ) : ZMod 2) =
        ((boolPacketPositiveCount raw : ℕ) : ZMod 2) +
        ((2*k+3 : ℕ) : ZMod 2) := hxor
  have hdouble :
      ((2*k+3 : ℕ) : ZMod 2) +
        ((2*k+3 : ℕ) : ZMod 2) = 0 := by
    have hz : (2 : ZMod 2) = 0 := by decide
    calc
      _ = (2 : ZMod 2) * ((2*k+3 : ℕ) : ZMod 2) := by ring
      _ = 0 := by rw [hz]; simp
  change ((boolPacketPositiveCount raw : ℕ) : ZMod 2) =
    ((positiveFacetCount A f + (2*k+3) : ℕ) : ZMod 2)
  calc
    ((boolPacketPositiveCount raw : ℕ) : ZMod 2) =
        ((boolPacketPositiveCount raw : ℕ) : ZMod 2) + 0 := by simp
    _ = ((boolPacketPositiveCount raw : ℕ) : ZMod 2) +
          (((2*k+3 : ℕ) : ZMod 2) +
            ((2*k+3 : ℕ) : ZMod 2)) := by rw [hdouble]
    _ = (((boolPacketPositiveCount raw : ℕ) : ZMod 2) +
          ((2*k+3 : ℕ) : ZMod 2)) +
          ((2*k+3 : ℕ) : ZMod 2) := by ring
    _ = ((positiveFacetCount A f : ℕ) : ZMod 2) +
          ((2*k+3 : ℕ) : ZMod 2) := by rw [← hnorm]
    _ = ((positiveFacetCount A f + (2*k+3) : ℕ) : ZMod 2) := by
      push_cast
      ring

/-- Every allowed local packet in a toggle-zero odd-arity class is
homogeneous iff its actual raw facet word has odd F₂ parity. -/
theorem Hyper.p1Toggle_typeZero_iff_rawFacetParityOne
    (k : ℕ) {V : Type*} (A : Hyper (4*k+5) V)
    (f : Fin (4*k+6) ↪ V)
    (hallowed :
      localIndex A f ∈ toggleZero (switchingAllowed (4*k+5))) :
    p1BitToZMod (decide (localIndex A f = 0)) =
      ((boolPacketPositiveCount
        (fun i : Fin (4*k+6) => A.orient (facet f i)) : ℕ) : ZMod 2) := by
  have hpar :=
    A.p1Toggle_normalizedCount_parity_iff_localIndex_zero
      k f hallowed
  calc
    p1BitToZMod (decide (localIndex A f = 0)) =
        p1BitToZMod
          (decide ((positiveFacetCount A f + (2*k+3)) % 2 = 1)) := by
      rw [hpar]
    _ = ((positiveFacetCount A f + (2*k+3) : ℕ) : ZMod 2) :=
      (p1NatCast_eq_oddBit _).symm
    _ = ((boolPacketPositiveCount
          (fun i : Fin (4*k+6) => A.orient (facet f i)) : ℕ) :
            ZMod 2) :=
      (A.p1RawFacetCount_toZMod k f).symm

end Hypertournaments
