import Hypertournaments.OddToggleP3ActualOccupancies

/-!
# Erasing the unique old vertex of a singleton p3 block

The actual p3 block occupancy statistic is the cardinality of a
finite fiber. If the occupancy is exactly one, its sole old vertex
is unique. Deleting this vertex from a packet eliminates that
entire block, with an explicit finite-set membership statement.

Together with already certified missing-block coboundary support,
this is the exact transfer from singleton block selection to an
actual zero raw facet of a potential-induced side hypertournament.
-/

namespace Hypertournaments

/-- A positive old vertex in a block of occupancy one is its
only vertex among the selected old finite set. -/
theorem p3SingletonBlock_vertex_unique
    (m t : ℕ) (U : Finset (Fin (m*t)))
    (i : Fin m) (hocc : p3BlockOccupancy m t U i = 1)
    (v : Fin (m*t)) (hv : v ∈ U)
    (hblock : p3BlockNumber t v = i.val) :
    ∀ w : Fin (m*t), w ∈ U →
      p3BlockNumber t w = i.val → w = v := by
  classical
  let S : Finset (Fin (m*t)) :=
    U.filter (fun x => p3BlockNumber t x = i.val)
  have hcard : S.card = 1 := hocc
  obtain ⟨a, hS⟩ := Finset.card_eq_one.mp hcard
  have hvmem : v ∈ S :=
    Finset.mem_filter.mpr ⟨hv, hblock⟩
  have hva : v = a := by
    rw [hS] at hvmem
    simpa using hvmem
  intro w hw hwblock
  have hwmem : w ∈ S :=
    Finset.mem_filter.mpr ⟨hw, hwblock⟩
  have hwa : w = a := by
    rw [hS] at hwmem
    simpa using hwmem
  exact hwa.trans hva.symm

/-- Removing the only occupied old vertex of a singleton block
makes the entire block absent from the remaining finite set. -/
theorem p3SingletonBlock_erase_missing
    (m t : ℕ) (U : Finset (Fin (m*t)))
    (i : Fin m) (hocc : p3BlockOccupancy m t U i = 1)
    (v : Fin (m*t)) (hv : v ∈ U)
    (hblock : p3BlockNumber t v = i.val) :
    ∀ w : Fin (m*t), w ∈ U.erase v →
      p3BlockNumber t w ≠ i.val := by
  intro w hw hbw
  have hwU : w ∈ U := Finset.mem_of_mem_erase hw
  have heq : w = v :=
    p3SingletonBlock_vertex_unique m t U i hocc v hv hblock w hwU hbw
  exact (Finset.mem_erase.mp hw).1 heq

end Hypertournaments
