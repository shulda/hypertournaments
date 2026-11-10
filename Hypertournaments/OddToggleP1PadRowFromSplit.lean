import Hypertournaments.OddToggleP1RowCountSplit
import Hypertournaments.OddToggleP1PadRowParity

/-!
# Exact canonical link-row count at every auxiliary pad vertex

The canonical p1 side link table vanishes on pad/pad pairs. On
pad/core pairs it is the right pad-to-core table, independent of
the left/right choice; each row has exactly five positive entries.
Thus every auxiliary pad vertex has an odd canonical link row on
both sides, agreeing with its positive base sign.

This is the pad-vertex half of the uniform side age argument.
-/

namespace Hypertournaments

theorem p1CanonicalLink_pad_pad_false (k : ℕ) (left : Bool)
    (s t : Fin (2*(2*k))) :
    p1CanonicalLink k left (p1PadAt k s) (p1PadAt k t) = false := by
  have hs := p1PadAt_lt k s
  have ht := p1PadAt_lt k t
  simp [p1CanonicalLink, hs, ht]

theorem p1CanonicalLink_pad_core (k : ℕ) (left : Bool)
    (s : Fin (2*(2*k))) (j : Fin 6) :
    p1CanonicalLink k left (p1PadAt k s) (p1CoreAt k j) =
      p1RightPadCoreBit k s j := by
  have hs := p1PadAt_lt k s
  have hj : ¬(p1CoreAt k j).val < 4*k := by
    have h := p1CoreAt_ge k j
    omega
  simp only [p1CanonicalLink, dif_pos hs, dif_neg hj]
  congr 1
  · apply Fin.ext
    rfl
  · apply Fin.ext
    dsimp [p1CoreAt]
    omega

theorem p1CanonicalPad_row_positiveCount (k : ℕ) (left : Bool)
    (s : Fin (2*(2*k))) :
    p1CanonicalRowPositiveCount k left (p1PadAt k s) = 5 := by
  rw [p1CanonicalRowPositiveCount_split]
  have hpad :
      (Finset.univ.filter (fun t : Fin (2*(2*k)) =>
        p1CanonicalLink k left (p1PadAt k s) (p1PadAt k t)=true)).card =
          0 := by
    have hset :
        (Finset.univ.filter (fun t : Fin (2*(2*k)) =>
          p1CanonicalLink k left (p1PadAt k s) (p1PadAt k t)=true)) =
            ∅ := by
      ext t
      simp [p1CanonicalLink_pad_pad_false]
    rw [hset]
    rfl
  have hcore :
      (Finset.univ.filter (fun j : Fin 6 =>
        p1CanonicalLink k left (p1PadAt k s) (p1CoreAt k j)=true)).card =
          5 := by
    change boolPacketPositiveCount
      (fun j : Fin 6 =>
        p1CanonicalLink k left (p1PadAt k s) (p1CoreAt k j)) = 5
    have hbits :
        (fun j : Fin 6 =>
          p1CanonicalLink k left (p1PadAt k s) (p1CoreAt k j)) =
          (fun j => p1RightPadCoreBit k s j) := by
      funext j
      exact p1CanonicalLink_pad_core k left s j
    rw [hbits]
    exact p1RightPadCore_row_positiveCount k s
  rw [hpad, hcore]

theorem p1CanonicalPad_rowParity (k : ℕ) (left : Bool)
    (s : Fin (2*(2*k))) :
    p1CanonicalRowPositiveCount k left (p1PadAt k s) % 2 = 1 := by
  rw [p1CanonicalPad_row_positiveCount]

end Hypertournaments
