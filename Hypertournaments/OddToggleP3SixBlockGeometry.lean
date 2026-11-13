import Mathlib.Data.Fintype.Pi
import Lean.Elab.Tactic.Omega
import Hypertournaments.Basic

/-!
# Finite six-block geometry for protected zero facets

Every base-only p3 packet meeting all m blocks has at most two
nonsingleton blocks: the packet uses m+2 vertices. Among the first
six consecutive blocks, some pair of consecutive blocks must therefore
both be singleton. This note formalizes the FINITE six-block selection
step under its exact at-most-two-bad-block hypothesis.

The second general lemma proves that in any increasing monotone block
word, singleton occurrences of consecutive block labels occur at
consecutive vertex positions, so those facets have opposite parity.

The counting step from a concrete (m+2)-vertex transversal to the
at-most-two-bad-block hypothesis remains a separate obligation.
-/

namespace Hypertournaments

/-- If at most two of six consecutive block indices are bad,
one of the three disjoint consecutive pairs (0,1), (2,3), (4,5)
contains two good blocks. This is an exact six-bit finite certificate. -/
theorem p3SixBlocks_good_consecutive_pair
    (bad : Fin 6 → Bool)
    (hbad :
      (Finset.univ.filter (fun i : Fin 6 => bad i = true)).card ≤ 2) :
    (bad 0 = false ∧ bad 1 = false) ∨
    (bad 2 = false ∧ bad 3 = false) ∨
    (bad 4 = false ∧ bad 5 = false) := by
  have hfinite :
      ∀ b : Fin 6 → Bool,
        (Finset.univ.filter (fun i : Fin 6 => b i = true)).card ≤ 2 →
        (b 0 = false ∧ b 1 = false) ∨
        (b 2 = false ∧ b 3 = false) ∨
        (b 4 = false ∧ b 5 = false) := by decide
  exact hfinite bad hbad

/-- If a monotone sequence of block indices contains two consecutive
block labels, each at a unique position, those positions are
themselves consecutive. No surjectivity assumption is needed. -/
theorem p3Consecutive_singleton_blocks_adjacent_positions
    (N : ℕ) (block : Fin N → ℕ) (hmono : Monotone block)
    (i j : Fin N)
    (hstep : block j = block i + 1)
    (huniquei : ∀ q : Fin N, block q = block i → q = i)
    (huniquej : ∀ q : Fin N, block q = block j → q = j) :
    j.val = i.val + 1 := by
  have hij : i < j := by
    by_contra hh
    have hji : j ≤ i := le_of_not_gt hh
    have hrev := hmono hji
    omega
  have hbound : j.val ≤ i.val + 1 := by
    by_contra hh
    have hgap : i.val + 1 < j.val := by omega
    let q : Fin N := ⟨i.val+1, by
      have hlt := j.isLt
      omega⟩
    have hiq : i ≤ q := by
      change i.val ≤ i.val + 1
      omega
    have hqj : q ≤ j := by
      change i.val + 1 ≤ j.val
      omega
    have hlo := hmono hiq
    have hhi := hmono hqj
    have hval : block q = block i ∨ block q = block j := by
      omega
    rcases hval with hval | hval
    · have hqi := huniquei q hval
      have heq := congrArg Fin.val hqi
      dsimp [q] at heq
      omega
    · have hqj' := huniquej q hval
      have heq := congrArg Fin.val hqj'
      dsimp [q] at heq
      omega
  have hlt := hij
  change i.val < j.val at hlt
  omega

end Hypertournaments
