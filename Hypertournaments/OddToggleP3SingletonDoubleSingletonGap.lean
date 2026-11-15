import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.OddToggleP3SortedBlockFibers

/-!
# The difficult singleton-double-singleton protected triple gap

Consider a monotone finite word of block labels. Suppose label u
occurs exactly once at position x, label u+2 exactly once at y,
and the intermediate label u+1 occurs exactly twice. The two
intermediate occurrences must lie strictly between x and y.
Conversely every position strictly between x and y has label
u+1, because the endpoint labels are singleton. Thus the
positions differ by exactly three, and have opposite parity.

This handles the only protected triple pattern not addressed by
the existing consecutive-singleton-fiber theorem. It is pure
finite order combinatorics; no random coefficients or age claim.
-/

namespace Hypertournaments

/-- If singleton blocks u and u+2 enclose precisely two elements
of block u+1 in a monotone block word, their positions differ by
exactly three and therefore have opposite parity. -/
theorem p3Monotone_singletonDoubleSingleton_oppositeParity
    {N : ℕ} (block : Fin N → ℕ) (hmono : Monotone block)
    (x y : Fin N) (hstep : block y = block x + 2)
    (hxUnique : ∀ z : Fin N, block z = block x → z = x)
    (hyUnique : ∀ z : Fin N, block z = block y → z = y)
    (hmiddle : (Finset.univ.filter
      (fun z : Fin N => block z = block x + 1)).card = 2) :
    y.val = x.val + 3 ∧ x.val % 2 ≠ y.val % 2 := by
  classical
  let middle : Finset (Fin N) :=
    Finset.univ.filter (fun z : Fin N => block z = block x + 1)
  have hxy : x < y := by
    by_contra h
    have hyx := hmono (le_of_not_gt h)
    omega
  have hBetween (z : Fin N) (hz : z ∈ middle) :
      x.val < z.val ∧ z.val < y.val := by
    have hzValue : block z = block x + 1 :=
      (Finset.mem_filter.mp hz).2
    have hxz : x < z := by
      by_contra h
      have hzle := hmono (le_of_not_gt h)
      omega
    have hzy : z < y := by
      by_contra h
      have hyle := hmono (le_of_not_gt h)
      omega
    exact ⟨hxz,hzy⟩
  have hInside (z : Fin N) (hxz : x < z) (hzy : z < y) :
      z ∈ middle := by
    have hlo := hmono (le_of_lt hxz)
    have hhi := hmono (le_of_lt hzy)
    have hnX : z ≠ x := ne_of_gt hxz
    have hnY : z ≠ y := ne_of_lt hzy
    have hneqX : block z ≠ block x := by
      intro heq
      exact hnX (hxUnique z heq)
    have hneqY : block z ≠ block y := by
      intro heq
      exact hnY (hyUnique z heq)
    have hv : block z = block x + 1 := by omega
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hv⟩
  have hLower : x.val + 3 ≤ y.val := by
    by_contra hh
    have hgap : y.val ≤ x.val + 2 := by omega
    let z : Fin N := ⟨x.val+1, by have hy := y.isLt; omega⟩
    have hsub : middle ⊆ {z} := by
      intro w hw
      have hb := hBetween w hw
      have hwz : w = z := by
        apply Fin.ext
        change w.val = x.val+1
        omega
      simp [hwz]
    have hcard := Finset.card_le_card hsub
    have hsingleton : ({z} : Finset (Fin N)).card = 1 := by simp
    rw [hsingleton, hmiddle] at hcard
    omega
  have hUpper : y.val ≤ x.val + 3 := by
    by_contra hh
    have hgap : x.val + 4 ≤ y.val := by omega
    let z1 : Fin N := ⟨x.val+1, by have hy := y.isLt; omega⟩
    let z2 : Fin N := ⟨x.val+2, by have hy := y.isLt; omega⟩
    let z3 : Fin N := ⟨x.val+3, by have hy := y.isLt; omega⟩
    have hz1 : z1 ∈ middle := by
      apply hInside
      · change x.val < x.val+1; omega
      · change x.val+1 < y.val; omega
    have hz2 : z2 ∈ middle := by
      apply hInside
      · change x.val < x.val+2; omega
      · change x.val+2 < y.val; omega
    have hz3 : z3 ∈ middle := by
      apply hInside
      · change x.val < x.val+3; omega
      · change x.val+3 < y.val; omega
    have h12 : z1 ≠ z2 := by
      intro heq
      have hv := congrArg Fin.val heq
      change x.val+1 = x.val+2 at hv
      omega
    have h13 : z1 ≠ z3 := by
      intro heq
      have hv := congrArg Fin.val heq
      change x.val+1 = x.val+3 at hv
      omega
    have h23 : z2 ≠ z3 := by
      intro heq
      have hv := congrArg Fin.val heq
      change x.val+2 = x.val+3 at hv
      omega
    have hsub : ({z1,z2,z3} : Finset (Fin N)) ⊆ middle := by
      intro z hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl | rfl
      · exact hz1
      · exact hz2
      · exact hz3
    have hcard := Finset.card_le_card hsub
    have hthree : ({z1,z2,z3} : Finset (Fin N)).card = 3 := by
      simp [h12,h13,h23, Ne.symm h12, Ne.symm h13, Ne.symm h23]
    rw [hthree, hmiddle] at hcard
    omega
  have hgap : y.val = x.val + 3 := by omega
  refine ⟨hgap, ?_⟩
  omega

end Hypertournaments
