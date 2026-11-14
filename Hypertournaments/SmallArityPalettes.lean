import Hypertournaments.LocalTypes
import Mathlib.Tactic.Ext
import Lean.Elab.Tactic.Omega

/-!
# The two binary and four ternary unbounded palettes

Source: article pin `919349e7eceed3c7fa0ed126a337c6fae6624704`,
`thm:constrained-classification`. These are equalities of valid palettes;
impossible indices can subsequently be removed by `admissible_validize`.
-/

namespace Hypertournaments

/-- A valid binary palette containing the central type is one of two sets. -/
theorem binary_central_palette_cases (S : Set ℕ) (hvalid : ValidTypes 2 S)
    (hcentral : centralIndex 2 ∈ S) :
    S = {1} ∨ S = {0, 1} := by
  classical
  have hc : 1 ∈ S := hcentral
  have hb (d : ℕ) (hd : d ∈ S) : d = 0 ∨ d = 1 := by
    have h := hvalid d hd
    change d ≤ 1 at h
    omega
  by_cases hz : 0 ∈ S
  · right
    ext d
    constructor
    · intro hd
      rcases hb d hd with rfl | rfl <;> simp
    · intro hd
      rcases hd with hd | hd
      · simpa [hd] using hz
      · simp only [Set.mem_singleton_iff] at hd
        simpa [hd] using hc
  · left
    ext d
    constructor
    · intro hd
      rcases hb d hd with hd0 | hd1
      · exact (hz (by simpa [hd0] using hd)).elim
      · exact hd1
    · intro hd
      simp only [Set.mem_singleton_iff] at hd
      simpa [hd] using hc

/-- A valid ternary palette containing the central type is one of four sets. -/
theorem ternary_central_palette_cases (S : Set ℕ) (hvalid : ValidTypes 3 S)
    (hcentral : centralIndex 3 ∈ S) :
    S = {2} ∨ S = {0, 2} ∨ S = {1, 2} ∨ S = {0, 1, 2} := by
  classical
  have hc : 2 ∈ S := hcentral
  have hb (d : ℕ) (hd : d ∈ S) : d = 0 ∨ d = 1 ∨ d = 2 := by
    have h := hvalid d hd
    change d ≤ 2 at h
    omega
  by_cases hz : 0 ∈ S
  · by_cases ho : 1 ∈ S
    · right; right; right
      ext d
      constructor
      · intro hd
        rcases hb d hd with rfl | rfl | rfl <;> simp
      · intro hd
        rcases hd with hd | hd
        · simpa [hd] using hz
        · rcases hd with hd | hd
          · simpa [hd] using ho
          · simp only [Set.mem_singleton_iff] at hd
            simpa [hd] using hc
    · right; left
      ext d
      constructor
      · intro hd
        rcases hb d hd with hd0 | hd1 | hd2
        · simp [hd0]
        · exact (ho (by simpa [hd1] using hd)).elim
        · simp [hd2]
      · intro hd
        rcases hd with hd | hd
        · simpa [hd] using hz
        · simp only [Set.mem_singleton_iff] at hd
          simpa [hd] using hc
  · by_cases ho : 1 ∈ S
    · right; right; left
      ext d
      constructor
      · intro hd
        rcases hb d hd with hd0 | hd1 | hd2
        · exact (hz (by simpa [hd0] using hd)).elim
        · simp [hd1]
        · simp [hd2]
      · intro hd
        rcases hd with hd | hd
        · simpa [hd] using ho
        · simp only [Set.mem_singleton_iff] at hd
          simpa [hd] using hc
    · left
      ext d
      constructor
      · intro hd
        rcases hb d hd with hd0 | hd1 | hd2
        · exact (hz (by simpa [hd0] using hd)).elim
        · exact (ho (by simpa [hd1] using hd)).elim
        · exact hd2
      · intro hd
        simp only [Set.mem_singleton_iff] at hd
        simpa [hd] using hc

end Hypertournaments
