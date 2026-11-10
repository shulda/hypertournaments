import Hypertournaments.OddToggleP1CoreRowParity
import Hypertournaments.OddToggleP1RightProtectedRows
import Hypertournaments.OddToggleP1PadCorePartition

/-!
# Right protected p1 rows after deleting one old base vertex

The right core vertices a0 and a4 have exceptional odd raw sign
parity. Their link rows are not arbitrary: after omitting the
corresponding old vertex, the signs alternate exactly with the
position in the increasing packet. This lemma combines the existing
certified six-core and auxiliary pad tables without assuming
admissibility or an amalgamation.
-/

namespace Hypertournaments

/-- On the right of a0, the link at any other old vertex reads the
parity of its increasing position after deleting a0. -/
theorem p1RightCoreZero_old_position (k : ℕ)
    (w : Fin (4*k+6))
    (hw : w ≠ p1CoreAt k (0 : Fin 6)) :
    p1CanonicalLink k false (p1CoreAt k (0 : Fin 6)) w =
      decide (((if w.val < 4*k then w.val else w.val-1)%2)=1) := by
  rcases p1OldVertex_pad_or_core k w with ⟨s, rfl⟩ | ⟨j, rfl⟩
  · rw [p1CanonicalLink_core_pad, p1RightPadZero_alternating]
    have hs := p1PadAt_lt k s
    have hlt : s.val < 4*k := by
      have hbound := s.isLt
      omega
    change decide (s.val%2=1) =
      decide (((if s.val < 4*k then s.val else s.val-1)%2)=1)
    simp [hlt]
  · have hjne : j ≠ 0 := by
      intro he
      subst j
      exact hw rfl
    rw [p1CanonicalLink_core_right,
      p1RightCoreZero_alternating j hjne]
    have hnot : ¬ (p1CoreAt k j).val < 4*k := by
      have hge := p1CoreAt_ge k j
      omega
    have hpos : 0 < j.val := by
      by_contra hn
      have hz : j = 0 := Fin.ext (by omega)
      exact hjne hz
    have hpar : ((p1CoreAt k j).val - 1)%2 = (j.val-1)%2 := by
      change (4*k+j.val-1)%2 = (j.val-1)%2
      omega
    simp only [if_neg hnot, hpar]

/-- On the right of a4, the link at any other old vertex is the
Boolean complement of the parity of its increasing position after
deleting a4. -/
theorem p1RightCoreFour_old_position (k : ℕ)
    (w : Fin (4*k+6))
    (hw : w ≠ p1CoreAt k (4 : Fin 6)) :
    p1CanonicalLink k false (p1CoreAt k (4 : Fin 6)) w =
      !(decide (((if w.val < 4*k+4 then w.val else w.val-1)%2)=1)) := by
  rcases p1OldVertex_pad_or_core k w with ⟨s, rfl⟩ | ⟨j, rfl⟩
  · rw [p1CanonicalLink_core_pad, p1RightPadFour_complement_alternating]
    have hs : (p1PadAt k s).val < 4*k+4 := by
      have h := p1PadAt_lt k s
      omega
    have hlt : s.val < 4*k+4 := by
      have hbound := s.isLt
      omega
    change (!(decide (s.val%2=1))) =
      !(decide (((if s.val < 4*k+4 then s.val else s.val-1)%2)=1))
    simp [hlt]
  · have hjne : j ≠ 4 := by
      intro he
      subst j
      exact hw rfl
    rw [p1CanonicalLink_core_right,
      p1RightCoreFour_complement_alternating j hjne]
    by_cases hj : j.val < 4
    · have hlt : (p1CoreAt k j).val < 4*k+4 := by
        dsimp [p1CoreAt]
        omega
      have hpar : ((p1CoreAt k j).val)%2 = j.val%2 := by
        change (4*k+j.val)%2 = j.val%2
        omega
      simp only [if_pos hj, if_pos hlt, hpar]
    · have hnot : ¬ (p1CoreAt k j).val < 4*k+4 := by
        dsimp [p1CoreAt]
        omega
      have hpar : ((p1CoreAt k j).val-1)%2 = (j.val-1)%2 := by
        change (4*k+j.val-1)%2 = (j.val-1)%2
        omega
      simp only [if_neg hj, if_neg hnot, hpar]

end Hypertournaments
