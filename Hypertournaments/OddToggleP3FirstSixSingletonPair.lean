import Hypertournaments.OddToggleP3ActualOccupancies
import Hypertournaments.OddToggleP3SixBlockGeometry

/-!
# The first six blocks contain a consecutive singleton pair

Combining the precise two-point excess inequality with the exact
six-block finite Boolean certificate yields two consecutive
singleton block labels among the first six.

This is stated first for an abstract positive occupancy profile
of total m+2. The numerical result requires no new hypotheses
beyond those used in the actual p3 block transversal construction.
-/

namespace Hypertournaments

/-- Order-preserving inclusion of the first six labels in Fin m. -/
def p3FirstSixEmbedding (m : ℕ) (hm : 6 ≤ m) : Fin 6 ↪ Fin m where
  toFun i := ⟨i.val, by omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact congrArg (fun x : Fin m => x.val) h

/-- A positive occupancy with two excess vertices has two
consecutive singleton labels within the first six blocks. -/
theorem p3FirstSixSingletonPair_of_twoExcess
    (m : ℕ) (hm : 6 ≤ m)
    (occ : Fin m → ℕ)
    (hall : ∀ i : Fin m, 0 < occ i)
    (hsum : (∑ i : Fin m, occ i) = m+2) :
    ∃ q : Fin 3,
      occ (p3FirstSixEmbedding m hm
        (⟨2*q.val, by omega⟩ : Fin 6)) = 1 ∧
      occ (p3FirstSixEmbedding m hm
        (⟨2*q.val+1, by omega⟩ : Fin 6)) = 1 := by
  classical
  let e := p3FirstSixEmbedding m hm
  let badM : Finset (Fin m) :=
    Finset.univ.filter (fun i => 1 < occ i)
  let bad6 : Finset (Fin 6) :=
    Finset.univ.filter (fun i => 1 < occ (e i))
  have hsubset : bad6.image e ⊆ badM := by
    intro j hj
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
  have hbad6 : bad6.card ≤ 2 := by
    calc
      bad6.card = (bad6.image e).card :=
        (Finset.card_image_of_injective bad6 e.injective).symm
      _ ≤ badM.card := Finset.card_le_card hsubset
      _ ≤ 2 := p3AtMostTwoNonSingletonOfTwoExcess m occ hall hsum
  let bad : Fin 6 → Bool := fun i => decide (1 < occ (e i))
  have hdecide :
      (Finset.univ.filter (fun i : Fin 6 => bad i = true)) = bad6 := by
    ext i
    simp [bad, bad6]
  have hbool : (Finset.univ.filter
      (fun i : Fin 6 => bad i = true)).card ≤ 2 := by
    rw [hdecide]
    exact hbad6
  have hsingle (i : Fin 6) (hi : bad i = false) : occ (e i) = 1 := by
    have hn : ¬ 1 < occ (e i) := by
      intro hh
      have hb : bad i = true := by simp [bad, hh]
      rw [hi] at hb
      cases hb
    have hp := hall (e i)
    omega
  rcases p3SixBlocks_good_consecutive_pair bad hbool with h01 | h23 | h45
  · refine ⟨⟨0, by decide⟩, ?_, ?_⟩
    · exact hsingle 0 h01.1
    · exact hsingle 1 h01.2
  · refine ⟨⟨1, by decide⟩, ?_, ?_⟩
    · exact hsingle 2 h23.1
    · exact hsingle 3 h23.2
  · refine ⟨⟨2, by decide⟩, ?_, ?_⟩
    · exact hsingle 4 h45.1
    · exact hsingle 5 h45.2

end Hypertournaments
