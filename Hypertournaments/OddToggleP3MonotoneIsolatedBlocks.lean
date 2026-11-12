import Hypertournaments.Basic

/-!
# Local strict transitions certify globally singleton block positions

An increasing packet's numeric block-label word is monotone.
For such a word, a position i is the unique occurrence of its
label whenever the immediately previous and next transitions,
when they exist, are strictly increasing.

A strict transition after the first position and before the last
is therefore enough to isolate that block globally. This is the
precise monotone geometry used to turn the finite six-edge p3
selector into genuine singleton-block vertices with opposite
deletion parity.

The lemma does not assume any random coefficients or AP property.
-/

namespace Hypertournaments

/-- In a monotone block-label word, strict immediate left/right
transitions (whenever those neighbors exist) make the label at
position i unique in the ENTIRE word, not only a seven-position
prefix. -/
theorem p3Monotone_isolated_of_strict_neighbors
    {N : ℕ} (block : Fin N → ℕ) (hmono : Monotone block)
    (i : Fin N)
    (hleft : ∀ j : Fin N, j.val+1=i.val → block j < block i)
    (hright : ∀ j : Fin N, i.val+1=j.val → block i < block j) :
    ∀ j : Fin N, block j = block i → j = i := by
  intro j heq
  by_cases hji : j = i
  · exact hji
  · rcases lt_or_gt_of_ne hji with hij | hji'
    · let pred : Fin N := ⟨i.val-1, by have hi := i.isLt; omega⟩
      have hpred : pred.val+1=i.val := by
        dsimp [pred]
        have hh : j.val < i.val := hij
        omega
      have hstrict := hleft pred hpred
      have hjpred : j ≤ pred := by
        change j.val ≤ i.val-1
        have hh : j.val < i.val := hij
        omega
      have hmon := hmono hjpred
      omega
    · let succ : Fin N := ⟨i.val+1, by
        have hj := j.isLt
        have hh : i.val < j.val := hji'
        omega⟩
      have hnext : i.val+1=succ.val := rfl
      have hstrict := hright succ hnext
      have hsuccj : succ ≤ j := by
        change i.val+1 ≤ j.val
        have hh : i.val < j.val := hji'
        omega
      have hmon := hmono hsuccj
      omega

end Hypertournaments
