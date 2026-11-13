import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ext
import Hypertournaments.EvenSuspensionFacetCases

/-!
# Exact two- and three-pad facet geometry in even suspension

This module fills in the remaining projection geometry for packets
containing two or three padding vertices. In a three-pad packet,
deleting any pad gives the same old canonical sign, whereas deleting
a nonpad gives the constant positive sign. In a two-pad packet,
deleting a pad gives the constant positive sign, whereas deleting an
old vertex gives the canonical sign of the old set with that vertex
removed.

These are statements about the *actual* sign table on finite subsets,
not merely abstract Boolean packet patterns. Their conversion into
intrinsic local-type/admissibility statements is a separate step.
-/

namespace Hypertournaments

/-- Removing a padding vertex cannot change the old projection. -/
theorem evenOldProjection_erase_pad (m k : ℕ)
    (Q : Finset (Fin (m + k))) (p : Fin m) :
    evenOldProjection m k (Q.erase (evenPadShift m k p)) =
      evenOldProjection m k Q := by
  ext u
  have hneq : evenOldShift m k u ≠ evenPadShift m k p :=
    (evenPadShift_ne_oldShift m k p u).symm
  simp [evenOldProjection, hneq]

/-- Removing an old vertex erases precisely its index from the old
projection, regardless of whether that vertex was present in Q. -/
theorem evenOldProjection_erase_old (m k : ℕ)
    (Q : Finset (Fin (m + k))) (u : Fin k) :
    evenOldProjection m k (Q.erase (evenOldShift m k u)) =
      (evenOldProjection m k Q).erase u := by
  ext v
  simp only [evenOldProjection, Finset.mem_filter, Finset.mem_univ,
    true_and, Finset.mem_erase]
  constructor
  · rintro ⟨hneq, hmem⟩
    refine ⟨?_, hmem⟩
    intro huv
    exact hneq (congrArg (evenOldShift m k) huv)
  · rintro ⟨hneq, hmem⟩
    refine ⟨?_, hmem⟩
    intro huv
    exact hneq ((evenOldShift m k).injective huv)

/-- Old vertices are disjoint from the range of the padding map. -/
theorem evenOldShift_not_mem_pad (m k : ℕ) (u : Fin k) :
    evenOldShift m k u ∉ Set.range (evenPadShift m k) := by
  rintro ⟨p, hp⟩
  exact evenPadShift_ne_oldShift m k p u hp

/-- With exactly three pads in Q, deleting one present pad leaves two
pads and retains the entire old vertex set, hence reads the old sign. -/
theorem evenSuspensionSignTable_erase_pad_three
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (Q : Finset (Fin (m + k)))
    (hthree : (evenPadProjection m k Q).card = 3)
    (p : Fin m) (hp : p ∈ evenPadProjection m k Q) :
    evenSuspensionSignTable m k A (Q.erase (evenPadShift m k p)) =
      A.canonicalSignTable (evenOldProjection m k Q) := by
  have htwo :
      (evenPadProjection m k (Q.erase (evenPadShift m k p))).card = 2 := by
    rw [evenPadProjection_erase_pad]
    have h := Finset.card_erase_add_one hp
    omega
  simp [evenSuspensionSignTable, htwo, evenOldProjection_erase_pad]

/-- With exactly three pads, deleting any nonpad still leaves three
pads and therefore gives the constant positive raw sign. -/
theorem evenSuspensionSignTable_erase_nonpad_three
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (Q : Finset (Fin (m + k)))
    (hthree : (evenPadProjection m k Q).card = 3)
    (v : Fin (m + k)) (hv : v ∉ Set.range (evenPadShift m k)) :
    evenSuspensionSignTable m k A (Q.erase v) = true := by
  have hne :
      (evenPadProjection m k (Q.erase v)).card ≠ 2 := by
    rw [evenPadProjection_erase_nonpad m k Q v hv, hthree]
    omega
  simp [evenSuspensionSignTable, hne]

/-- With exactly two pads, deleting either present pad leaves one and
therefore gives the constant positive raw sign. -/
theorem evenSuspensionSignTable_erase_pad_two
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (Q : Finset (Fin (m + k)))
    (htwo : (evenPadProjection m k Q).card = 2)
    (p : Fin m) (hp : p ∈ evenPadProjection m k Q) :
    evenSuspensionSignTable m k A (Q.erase (evenPadShift m k p)) =
      true := by
  have hone :
      (evenPadProjection m k (Q.erase (evenPadShift m k p))).card = 1 := by
    rw [evenPadProjection_erase_pad]
    have h := Finset.card_erase_add_one hp
    omega
  have hne :
      (evenPadProjection m k (Q.erase (evenPadShift m k p))).card ≠ 2 := by
    omega
  simp [evenSuspensionSignTable, hne]

/-- With exactly two pads, deleting an old vertex preserves the pad
pair and removes exactly that old vertex in the source sign table. -/
theorem evenSuspensionSignTable_erase_old_two
    {n : ℕ} (m k : ℕ) (A : Hyper n (Fin k))
    (Q : Finset (Fin (m + k)))
    (htwo : (evenPadProjection m k Q).card = 2)
    (u : Fin k) :
    evenSuspensionSignTable m k A (Q.erase (evenOldShift m k u)) =
      A.canonicalSignTable ((evenOldProjection m k Q).erase u) := by
  have hcard :
      (evenPadProjection m k (Q.erase (evenOldShift m k u))).card = 2 := by
    rw [evenPadProjection_erase_nonpad m k Q
      (evenOldShift m k u) (evenOldShift_not_mem_pad m k u)]
    exact htwo
  simp [evenSuspensionSignTable, hcard, evenOldProjection_erase_old]

end Hypertournaments
