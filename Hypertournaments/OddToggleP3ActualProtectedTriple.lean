import Lean.Elab.Tactic.Omega
import Hypertournaments.OddToggleP3OneFreshActualExcess
import Hypertournaments.OddToggleP3OneFreshGap
import Hypertournaments.OddToggleP3ProtectedTriple

/-!
# Actual protected triple arithmetic for one-fresh full-block packets

An actual old subset U of m+1 vertices, meeting all m consecutive
old blocks, has exactly one excess vertex beyond the baseline one
per block. Hence any THREE different occupied block labels have
total occupancy at most four. For consecutive protected labels
this is precisely the numerical premise of the certified protected
triple opposite-parity selector, including the middle-double case
(1,2,1), where the two singletons are three positions apart.

This proves actual finite-set occupancy/arithmetic, not yet the
ordered-position transfer into a genuine Hyper packet.
-/

namespace Hypertournaments

/-- Any three distinct block labels of the actual one-fresh
full-occupancy old set contain altogether at most four vertices. -/
theorem p3ActualOneFresh_three_blocks_le_four
    (m t : ℕ) (ht : 0 < t)
    (U : Finset (Fin (m*t))) (hsize : U.card = m+1)
    (hall : ∀ i : Fin m, 0 < p3BlockOccupancy m t U i)
    (i j l : Fin m)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l) :
    p3BlockOccupancy m t U i +
      p3BlockOccupancy m t U j +
      p3BlockOccupancy m t U l ≤ 4 := by
  let occ : Fin m → ℕ := p3BlockOccupancy m t U
  have hi : 0 < occ i := hall i
  have hj : 0 < occ j := hall j
  have hl : 0 < occ l := hall l
  have hi2 : occ i ≤ 2 :=
    p3ActualOneFresh_occ_le_two m t ht U hsize hall i
  have hj2 : occ j ≤ 2 :=
    p3ActualOneFresh_occ_le_two m t ht U hsize hall j
  have hl2 : occ l ≤ 2 :=
    p3ActualOneFresh_occ_le_two m t ht U hsize hall l
  have hIJ : ¬ (1 < occ i ∧ 1 < occ j) := by
    rintro ⟨ha,hb⟩
    exact p3ActualOneFresh_no_two_double_blocks
      m t ht U hsize hall i j hij ha hb
  have hIL : ¬ (1 < occ i ∧ 1 < occ l) := by
    rintro ⟨ha,hb⟩
    exact p3ActualOneFresh_no_two_double_blocks
      m t ht U hsize hall i l hil ha hb
  have hJL : ¬ (1 < occ j ∧ 1 < occ l) := by
    rintro ⟨ha,hb⟩
    exact p3ActualOneFresh_no_two_double_blocks
      m t ht U hsize hall j l hjl ha hb
  change occ i + occ j + occ l ≤ 4
  by_cases hBigI : 1 < occ i
  · have hSmallJ : occ j ≤ 1 := by
      by_contra hnot
      have hBigJ : 1 < occ j := by omega
      exact hIJ ⟨hBigI, hBigJ⟩
    have hSmallL : occ l ≤ 1 := by
      by_contra hnot
      have hBigL : 1 < occ l := by omega
      exact hIL ⟨hBigI, hBigL⟩
    omega
  · by_cases hBigJ : 1 < occ j
    · have hSmallL : occ l ≤ 1 := by
        by_contra hnot
        have hBigL : 1 < occ l := by omega
        exact hJL ⟨hBigJ, hBigL⟩
      omega
    · omega

/-- Actual protected labels have the exact arithmetic
singleton/phase alternatives used in the one-fresh side proof,
for any starting position of their consecutive sorted fiber
segment. The subsequent work must identify that start. -/
theorem p3ActualOneFresh_protectedTriple_numeric_parity
    (m t : ℕ) (ht : 0 < t)
    (U : Finset (Fin (m*t))) (hsize : U.card = m+1)
    (hall : ∀ i : Fin m, 0 < p3BlockOccupancy m t U i)
    (i j l : Fin m)
    (hij : i ≠ j) (hil : i ≠ l) (hjl : j ≠ l)
    (start : ℕ) :
    let a := p3BlockOccupancy m t U i
    let b := p3BlockOccupancy m t U j
    let c := p3BlockOccupancy m t U l
    (a=1 ∧ b=1 ∧ start%2 ≠ (start+a)%2) ∨
    (b=1 ∧ c=1 ∧ (start+a)%2 ≠ (start+a+b)%2) ∨
    (a=1 ∧ b=2 ∧ c=1 ∧
      start%2 ≠ (start+a+b)%2) := by
  dsimp
  exact p3ProtectedTriple_singletons_oppositeParity
    start
    (p3BlockOccupancy m t U i)
    (p3BlockOccupancy m t U j)
    (p3BlockOccupancy m t U l)
    (hall i) (hall j) (hall l)
    (p3ActualOneFresh_three_blocks_le_four
      m t ht U hsize hall i j l hij hil hjl)

end Hypertournaments
