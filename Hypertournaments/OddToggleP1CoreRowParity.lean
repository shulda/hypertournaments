import Hypertournaments.OddToggleP1RowCountSplit
import Hypertournaments.OddToggleP1CoreRows
import Hypertournaments.OddToggleP1PadParity

/-!
# Exact parity of canonical p1 link rows at each six-core vertex

For an old core vertex a_j, the canonical link row has two parts:
4k pad columns and six core columns. The pad part has even parity
for both sides and every j, as certified by the pad-column parity
lemma. The core contribution is exactly the certified finite
six-core link table. Consequently the complete link-row parity
equals the base sign on the left and differs from it on the right
precisely at j=0 and j=4.

This is a concrete uniform arithmetic fact about the actual
one-point side sign tables. It is not an admissibility or
amalgamation theorem.
-/

namespace Hypertournaments

/-- Every canonical link from a core vertex to a pad is
given by the right pad-core sign bit on both one-point sides. -/
theorem p1CanonicalLink_core_pad
    (k : ℕ) (left : Bool)
    (j : Fin 6) (s : Fin (2*(2*k))) :
    p1CanonicalLink k left (p1CoreAt k j) (p1PadAt k s) =
      p1RightPadCoreBit k s j := by
  have hcore : ¬(p1CoreAt k j).val < 4*k := by
    have := p1CoreAt_ge k j
    omega
  have hpad : (p1PadAt k s).val < 4*k :=
    p1PadAt_lt k s
  simp [p1CanonicalLink, hcore, hpad, p1CoreAt, p1PadAt]

/-- On a core row, the pad-column contribution is always even. -/
theorem p1CanonicalCore_padContribution_even
    (k : ℕ) (left : Bool) (j : Fin 6) :
    ((Finset.univ.filter (fun s : Fin (2*(2*k)) =>
      p1CanonicalLink k left (p1CoreAt k j) (p1PadAt k s) = true)).card)%2 =
      0 := by
  have hbits :
      (fun s : Fin (2*(2*k)) =>
        p1CanonicalLink k left (p1CoreAt k j) (p1PadAt k s)) =
        (fun s => p1RightPadCoreBit k s j) := by
    funext s
    exact p1CanonicalLink_core_pad k left j s
  change boolPacketPositiveCount
    (fun s : Fin (2*(2*k)) =>
      p1CanonicalLink k left (p1CoreAt k j) (p1PadAt k s)) % 2 = 0
  rw [hbits]
  exact p1RightPadCore_column_even k j

/-- On a core row, the core-column contribution has exactly the
finite six-core link row parity certified separately. -/
theorem p1CanonicalCore_coreContribution_parity
    (k : ℕ) (left : Bool) (j : Fin 6) :
    ((Finset.univ.filter (fun t : Fin 6 =>
      p1CanonicalLink k left (p1CoreAt k j) (p1CoreAt k t) = true)).card)%2 =
      if left then
        (if p1CoreBaseBit j then 1 else 0)
      else
        ((if p1CoreBaseBit j then 1 else 0) +
          (if j=0 ∨ j=4 then 1 else 0))%2 := by
  cases left
  · simpa [p1CoreLinkRowParity, p1CanonicalLink_core_right] using
      (p1Core_right_row_parity j)
  · simpa [p1CoreLinkRowParity, p1CanonicalLink_core_left] using
      (p1Core_left_row_parity j)

/-- Complete canonical link-row parity at any old core vertex. -/
theorem p1CanonicalCore_rowParity
    (k : ℕ) (left : Bool) (j : Fin 6) :
    p1CanonicalRowPositiveCount k left (p1CoreAt k j)%2 =
      if left then
        (if p1CoreBaseBit j then 1 else 0)
      else
        ((if p1CoreBaseBit j then 1 else 0) +
          (if j=0 ∨ j=4 then 1 else 0))%2 := by
  rw [p1CanonicalRowPositiveCount_split]
  have hp := p1CanonicalCore_padContribution_even k left j
  have hc := p1CanonicalCore_coreContribution_parity k left j
  cases left <;> omega

end Hypertournaments
