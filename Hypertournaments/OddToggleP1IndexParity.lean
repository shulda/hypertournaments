import Hypertournaments.NegativeModuloOddToggle
import Hypertournaments.OddToggleP1BooleanParity

/-!
# Parity of normalized local types in the odd n ≡ 1 (mod 4) exception

For n=4k+5, the normalized local packet has 4k+6 facets, an even
number with odd half-length 2k+3. The toggle-zero switching family
allows type zero together with odd positive minority indices.

The first lemma shows that those type indices are either zero or odd.
The second numerical lemma says exactly that, for a packet whose
minority type is zero or odd, the positive normalized count plus the
half-length is odd iff its minority type is zero.

Thus the parity of the raw facet word (after XOR with an alternating
normalization) recognizes the forbidden homogeneous type. This file
proves the underlying exact arithmetic and an intrinsic localIndex
specialization. No cochain or AP witness is assumed.
-/

namespace Hypertournaments

/-- The exceptional allowed family in arity 4k+5 consists of type
zero and the odd switching types. -/
theorem p1ToggleTypes_zero_or_odd
    (k d : ℕ)
    (hd : d ∈ toggleZero (switchingAllowed (4*k+5))) :
    d = 0 ∨ d % 2 = 1 := by
  by_cases hd0 : d = 0
  · exact Or.inl hd0
  · right
    change (if d = 0 then d ∉ switchingAllowed (4*k+5)
      else d ∈ switchingAllowed (4*k+5)) at hd
    simp only [if_neg hd0] at hd
    exact (by
      have hp : d % 2 = centralIndex (4*k+5) % 2 := hd.2
      unfold centralIndex at hp
      omega)

/-- Numerical core of the homogeneous-indicator parity calculation:
when only zero or odd minority types are permitted, positive
normalized count plus odd half-length is odd precisely at type zero. -/
theorem p1OddHalfParity_iff_minority_zero
    (k r : ℕ)
    (hr : r ≤ 4*k+6)
    (hallowed :
      min r (4*k+6-r) = 0 ∨
      (min r (4*k+6-r)) % 2 = 1) :
    ((r+2*k+3) % 2 = 1 ↔
      min r (4*k+6-r) = 0) := by
  by_cases hle : r ≤ 4*k+6-r
  · have hm : min r (4*k+6-r) = r :=
      Nat.min_eq_left hle
    rw [hm] at hallowed ⊢
    omega
  · have hm : min r (4*k+6-r) = 4*k+6-r :=
      Nat.min_eq_right (le_of_lt (lt_of_not_ge hle))
    rw [hm] at hallowed ⊢
    omega

/-- Actual local packet specialization of the numerical parity
criterion, for any intrinsic hypertournament of arity 4k+5.
The left side still uses the *normalized* count; comparison with
the raw cochain is a separate Boolean-XOR lemma. -/
theorem Hyper.p1Toggle_normalizedCount_parity_iff_localIndex_zero
    (k : ℕ) {V : Type*} (A : Hyper (4*k+5) V)
    (f : Fin (4*k+6) ↪ V)
    (hallowed :
      localIndex A f ∈ toggleZero (switchingAllowed (4*k+5))) :
    ((positiveFacetCount A f + (2*k+3)) % 2 = 1 ↔
      localIndex A f = 0) := by
  have hbound : positiveFacetCount A f ≤ 4*k+6 :=
    positiveFacetCount_le A f
  have htypes := p1ToggleTypes_zero_or_odd
    k (localIndex A f) hallowed
  change
    min (positiveFacetCount A f)
      (4*k+6-positiveFacetCount A f) = 0 ∨
    (min (positiveFacetCount A f)
      (4*k+6-positiveFacetCount A f)) % 2 = 1 at htypes
  exact p1OddHalfParity_iff_minority_zero
    k (positiveFacetCount A f) hbound htypes

end Hypertournaments
