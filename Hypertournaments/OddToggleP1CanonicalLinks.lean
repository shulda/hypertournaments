import Hypertournaments.OddToggleP1PadParity
import Hypertournaments.OddToggleP1CoreRows

/-!
# Canonical links for the uniform odd p1 obstruction

The manuscript orders its one-point left vertex between the pads
P and six core vertices U, but right vertex r after U. The Lean
canonical joint must use one common base embedding, conveniently
with both new vertices after U.

Moving the left endpoint after U flips its raw (n-ary) link sign
whenever the number of retained core vertices is odd. For omitted
base pairs of different kinds:
* two pads: retained core count 6, even, and both bits zero;
* one pad and one core: retained core count 5, odd, and the
  manuscript's left pad-core sign is the complement of the right;
* two core vertices: retained core count 4, even, and the original
  left/right six-core link matrices are unchanged.

Consequently the *canonical* left and right link tables agree
whenever a missing pair contains at least one pad, and can disagree
only on a core-core pair, precisely the seven eligible pairs.

This module encodes the canonical link table explicitly, without yet
constructing side hypertournaments or asserting AP failure.
-/

namespace Hypertournaments

/-- Embed a six-core vertex after the 4k pad vertices. -/
def p1CoreAt (k : ℕ) (j : Fin 6) : Fin (4*k+6) :=
  ⟨4*k+j.val, by have := j.isLt; omega⟩

/-- The canonical unordered-link bit for each one-point side,
on a base pair. Boolean side flag true = left, false = right. -/
def p1CanonicalLink (k : ℕ) (left : Bool)
    (v w : Fin (4*k+6)) : Bool :=
  if hv : v.val < 4*k then
    if hw : w.val < 4*k then
      false
    else
      p1RightPadCoreBit k
        ⟨v.val, by omega⟩
        ⟨w.val - 4*k, by have := w.isLt; omega⟩
  else if hw : w.val < 4*k then
    p1RightPadCoreBit k
      ⟨w.val, by omega⟩
      ⟨v.val - 4*k, by have := v.isLt; omega⟩
  else
    if left then
      p1CoreLeftSymBit
        ⟨v.val-4*k, by have := v.isLt; omega⟩
        ⟨w.val-4*k, by have := w.isLt; omega⟩
    else
      p1CoreRightSymBit
        ⟨v.val-4*k, by have := v.isLt; omega⟩
        ⟨w.val-4*k, by have := w.isLt; omega⟩

/-- Canonical left and right links never disagree when at least
one of the missing base vertices is an auxiliary pad. -/
theorem p1CanonicalLink_pad_agree
    (k : ℕ) (v w : Fin (4*k+6))
    (hpad : v.val < 4*k ∨ w.val < 4*k) :
    p1CanonicalLink k true v w =
      p1CanonicalLink k false v w := by
  rcases hpad with hv | hw
  · simp [p1CanonicalLink, hv]
  · by_cases hv : v.val < 4*k
    · simp [p1CanonicalLink, hv]
    · simp [p1CanonicalLink, hv, hw]

/-- On core-core pairs, the canonical left link reduces exactly
to the certified finite six-core matrix. -/
theorem p1CanonicalLink_core_left (k : ℕ) (i j : Fin 6) :
    p1CanonicalLink k true (p1CoreAt k i) (p1CoreAt k j) =
      p1CoreLeftSymBit i j := by
  have hi : ¬(p1CoreAt k i).val < 4*k := by
    change ¬(4*k+i.val < 4*k)
    omega
  have hj : ¬(p1CoreAt k j).val < 4*k := by
    change ¬(4*k+j.val < 4*k)
    omega
  simp [p1CanonicalLink, hi, hj, p1CoreAt]

/-- On core-core pairs, the canonical right link reduces exactly
to the certified finite six-core matrix. -/
theorem p1CanonicalLink_core_right (k : ℕ) (i j : Fin 6) :
    p1CanonicalLink k false (p1CoreAt k i) (p1CoreAt k j) =
      p1CoreRightSymBit i j := by
  have hi : ¬(p1CoreAt k i).val < 4*k := by
    change ¬(4*k+i.val < 4*k)
    omega
  have hj : ¬(p1CoreAt k j).val < 4*k := by
    change ¬(4*k+j.val < 4*k)
    omega
  simp [p1CanonicalLink, hi, hj, p1CoreAt]

end Hypertournaments
