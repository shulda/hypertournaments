import Hypertournaments.NegativeReduction

/-!
# The parity family under a two-arity type-index shift

This module isolates a purely arithmetic fact used in the exceptional
odd-arity cases: if all positive allowed indices of the higher arity
are exactly the shifted switching indices, the only freedom left is
whether the homogeneous index zero is allowed.
-/

namespace Hypertournaments

/-- Shifting the positive indices of the higher switching family
recovers exactly the lower switching family. -/
theorem shiftedAllowed_switching (n : ℕ) :
    shiftedAllowed (switchingAllowed (n + 2)) =
      switchingAllowed n := by
  ext d
  change (d + 1 ≤ centralIndex (n + 2) ∧
          (d + 1) % 2 = centralIndex (n + 2) % 2) ↔
         (d ≤ centralIndex n ∧ d % 2 = centralIndex n % 2)
  rw [centralIndex_add_two]
  omega

/-- If the shifted family agrees with switching, then it agrees
with the upper switching family at every positive index. -/
theorem shiftedAllowed_switching_positive
    (n : ℕ) (S : Set ℕ)
    (hshift : shiftedAllowed S = switchingAllowed n)
    (d : ℕ) (hd : 0 < d) :
    d ∈ S ↔ d ∈ switchingAllowed (n + 2) := by
  have h : (d - 1) ∈ shiftedAllowed S ↔
      (d - 1) ∈ switchingAllowed n := by
    rw [hshift]
  change (d - 1 + 1 ∈ S) ↔
    ((d - 1 ≤ centralIndex n) ∧
      (d - 1) % 2 = centralIndex n % 2) at h
  have hpred : d - 1 + 1 = d := by omega
  rw [hpred] at h
  change d ∈ S ↔ (d ≤ centralIndex (n + 2) ∧
    d % 2 = centralIndex (n + 2) % 2)
  rw [centralIndex_add_two]
  omega

/-- Agreement at zero is the last requirement for agreement
with the entire higher switching family. -/
theorem shiftedAllowed_switching_eq_of_zero
    (n : ℕ) (S : Set ℕ)
    (hshift : shiftedAllowed S = switchingAllowed n)
    (hzero : (0 ∈ S) ↔ (0 ∈ switchingAllowed (n + 2))) :
    S = switchingAllowed (n + 2) := by
  ext d
  by_cases hd : d = 0
  · subst d
    exact hzero
  · exact shiftedAllowed_switching_positive n S hshift d (Nat.pos_of_ne_zero hd)

/-- Toggle the membership of the homogeneous local type, keeping
every positive-index type unchanged. -/
def toggleZero (S : Set ℕ) : Set ℕ :=
  {d | if d = 0 then d ∉ S else d ∈ S}

/-- A matching shifted switching family is either the switching
family itself or the one obtained by toggling the homogeneous type. -/
theorem shiftedAllowed_switching_two_choices
    (n : ℕ) (S : Set ℕ)
    (hshift : shiftedAllowed S = switchingAllowed n) :
    S = switchingAllowed (n + 2) ∨
      S = toggleZero (switchingAllowed (n + 2)) := by
  by_cases hzero : (0 ∈ S) ↔ (0 ∈ switchingAllowed (n + 2))
  · exact Or.inl (shiftedAllowed_switching_eq_of_zero n S hshift hzero)
  · right
    ext d
    by_cases hd : d = 0
    · subst d
      change (0 ∈ S) ↔ (0 ∉ switchingAllowed (n + 2))
      by_cases hs : 0 ∈ S <;> by_cases he : 0 ∈ switchingAllowed (n + 2) <;>
        simp_all
    · change d ∈ S ↔ (if d = 0 then d ∉ switchingAllowed (n + 2)
                       else d ∈ switchingAllowed (n + 2))
      simp [hd, shiftedAllowed_switching_positive n S hshift d (Nat.pos_of_ne_zero hd)]

end Hypertournaments
